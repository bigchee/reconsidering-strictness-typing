import Strictness.Inference.Construction.Infrastructure

/-!
Completeness constructions for constants, variables, abstraction, projection
and subsumption. Each construction returns the common `Buildable` witness.
-/

namespace Strictness.RawInference.CoreBoundary

open Raw

/-- Completeness construction for constants. -/
theorem buildable_const
    {Γ : Strictness.Env} {n : Int} {u : Usage}
    (hLazy : Strictness.Env.IsLazy Γ) :
    Buildable (Strictness.Env.scale u Γ) (.int n) (.int u) := by
  intro start initial
  let G := allocatedEnv start Γ
  let p : Raw.Expr := .var (start + envAnnotationCount Γ)
  let B : RTy := .int p
  let E := Raw.Env.scale p G
  let ν := writeBoundary Γ (.int u) initial start
  let limit := start + envAnnotationCount Γ + 1

  obtain ⟨hGEval, hBEval⟩ :=
    allocatedBoundary_eval Γ (.int u) initial start
  have hpEval : p.eval ν = u := by
    change Strictness.Ty.int (p.eval ν) = .int u at hBEval
    exact Strictness.Ty.int.inj hBEval

  have hGBound : EnvBelow limit G := by
    apply envBelow_mono (allocatedEnv_below Γ start)
    dsimp [limit]
    omega
  have hpBound : ExprBelow limit p := by
    change start + envAnnotationCount Γ <
      start + envAnnotationCount Γ + 1
    omega
  have hEBound := envBelow_scale hpBound hGBound
  have hBVariables : VariableTy B := by trivial
  have hBBound : TyBelow limit B := hpBound

  have hLocalSat : G.lazyConstraints.Satisfies ν := by
    apply (Raw.Env.eval_lazyConstraints ν G).mpr
    rw [hGEval]
    exact hLazy
  have hEEval :
      Raw.Env.eval ν E = Strictness.Env.scale u Γ := by
    dsimp [E]
    rw [Raw.Env.eval_scale, hGEval, hpEval]

  have hEnv :
      Strictness.Env.Subtype
        (Strictness.Env.scale u Γ) (Raw.Env.eval ν E) := by
    rw [hEEval]
    exact envSubtype_refl _
  have hTy :
      Strictness.Ty.Subtype (B.eval ν) (.int u) := by
    change Strictness.Ty.Subtype (.int (p.eval ν)) (.int u)
    rw [hpEval]
    exact subtype_refl _

  exact completeNode
    (Γ := Strictness.Env.scale u Γ) (τ := .int u)
    (start := start) (initial := initial) (limit := limit) (ν := ν)
    (Rule.const (Γ := G) (u := p) (n := n)
      (allocatedEnv_variables Γ start)
      (by trivial))
    (by intro P hMem; simp at hMem)
    (Raw.UseConstraints.satisfies_nil ν)
    hLocalSat hEBound hBBound hBVariables
    (constraintsBelow_nil limit)
    (lazyEnv_below hGBound)
    hEnv hTy
    (by dsimp [limit]; omega)
    (writeBoundary_agreeBelow Γ (.int u) initial (Nat.le_refl start))

/-- Completeness construction for the head variable. -/
theorem buildable_var
    {Γ : Strictness.Env} {τ : Strictness.Ty}
    (hLazy : Strictness.Env.IsLazy Γ) :
    Buildable (τ :: Strictness.Env.scale τ.outer Γ) (.var 0) τ := by
  intro start initial
  let G := allocatedEnv start Γ
  let A := allocatedTy (start + envAnnotationCount Γ) τ
  let E := A :: Raw.Env.scale A.outer G
  let ν := writeBoundary Γ τ initial start
  let limit := start + envAnnotationCount Γ + annotationCount τ

  obtain ⟨hGEval, hAEval⟩ :=
    allocatedBoundary_eval Γ τ initial start
  have hABound : TyBelow limit A :=
    allocatedTy_below τ (start + envAnnotationCount Γ)
  have hGBound : EnvBelow limit G := by
    apply envBelow_mono (allocatedEnv_below Γ start)
    dsimp [limit]
    omega
  have hScaledBound :=
    envBelow_scale (tyBelow_outer hABound) hGBound
  have hEBound : EnvBelow limit E := by
    intro B hMem
    change B ∈ A :: Raw.Env.scale A.outer G at hMem
    rcases List.mem_cons.mp hMem with hHead | hTail
    · subst B
      exact hABound
    · exact hScaledBound B hTail

  have hLocalSat : G.lazyConstraints.Satisfies ν := by
    apply (Raw.Env.eval_lazyConstraints ν G).mpr
    rw [hGEval]
    exact hLazy
  have hEEval :
      Raw.Env.eval ν E =
        τ :: Strictness.Env.scale τ.outer Γ := by
    dsimp [E]
    rw [Raw.Env.eval, Raw.Env.eval_scale,
      Raw.Ty.eval_outer, hAEval, hGEval]

  have hEnv :
      Strictness.Env.Subtype
        (τ :: Strictness.Env.scale τ.outer Γ)
        (Raw.Env.eval ν E) := by
    rw [hEEval]
    exact envSubtype_refl _
  have hTy :
      Strictness.Ty.Subtype (A.eval ν) τ := by
    rw [hAEval]
    exact subtype_refl _

  exact completeNode
    (Γ := τ :: Strictness.Env.scale τ.outer Γ) (τ := τ)
    (start := start) (initial := initial) (limit := limit) (ν := ν)
    (Rule.var
      (allocatedEnv_variables Γ start)
      (allocatedTy_variables τ (start + envAnnotationCount Γ)))
    (by intro P hMem; simp at hMem)
    (Raw.UseConstraints.satisfies_nil ν)
    hLocalSat hEBound hABound
    (allocatedTy_variables τ (start + envAnnotationCount Γ))
    (constraintsBelow_nil limit)
    (lazyEnv_below hGBound)
    hEnv hTy
    (by dsimp [limit]; omega)
    (writeBoundary_agreeBelow Γ τ initial (Nat.le_refl start))

theorem buildable_varSkip
    {Γ : Strictness.Env} {τ σ : Strictness.Ty} {i : Nat}
    (hChild : Buildable Γ (.var i) τ)
    (hLazy : Strictness.Ty.IsLazy σ) :
    Buildable
      (Strictness.Ty.scale τ.outer σ :: Γ) (.var (i + 1)) τ := by
  intro start initial
  obtain ⟨w⟩ := hChild start initial
  let S := allocatedTy w.stop σ
  let ν := writeTy σ w.valuation w.stop
  let limit := w.stop + annotationCount σ
  have hAgree : AgreeBelow w.stop ν w.valuation :=
    writeTy_agreeBelow σ w.valuation (Nat.le_refl w.stop)
  let v := w.revalue hAgree

  have hLimit : v.stop ≤ limit := by
    change w.stop ≤ w.stop + annotationCount σ
    omega
  have hSVariables : VariableTy S :=
    allocatedTy_variables σ w.stop
  have hSEval : S.eval v.valuation = σ :=
    allocatedTy_eval_writeTy σ w.valuation w.stop
  have hSBound : TyBelow limit S :=
    allocatedTy_below σ w.stop
  have hTyBound := tyBelow_mono v.ty_below hLimit
  have hCtxBound := envBelow_mono v.ctx_below hLimit
  have hVariables := v.supported.toDerives.boundary_variables

  have hLocalSat : S.lazyConstraints.Satisfies v.valuation := by
    apply (Raw.Ty.eval_lazyConstraints v.valuation S).mpr
    rw [hSEval]
    exact hLazy

  let E := Raw.Ty.scale v.ty.outer S :: v.ctx
  have hEBound : EnvBelow limit E := by
    intro A hMem
    change A ∈ Raw.Ty.scale v.ty.outer S :: v.ctx at hMem
    rcases List.mem_cons.mp hMem with hHead | hTail
    · subst A
      exact tyBelow_scale (tyBelow_outer hTyBound) hSBound
    · exact hCtxBound A hTail

  have hEEval :
      Raw.Env.eval v.valuation E =
        Strictness.Ty.scale τ.outer σ :: Γ := by
    dsimp [E]
    rw [Raw.Env.eval, Raw.Ty.eval_scale, Raw.Ty.eval_outer,
      v.ty_eval, hSEval, v.ctx_eval]
  have hEnv :
      Strictness.Env.Subtype
        (Strictness.Ty.scale τ.outer σ :: Γ)
        (Raw.Env.eval v.valuation E) := by
    rw [hEEval]
    exact envSubtype_refl _
  have hTy :
      Strictness.Ty.Subtype (v.ty.eval v.valuation) τ := by
    rw [v.ty_eval]
    exact subtype_refl _

  exact completeUnary
    (start := start) (initial := initial)
    (limit := limit) (ν := v.valuation)
    (Rule.varSkip
      (Γ := v.ctx) (A := v.ty) (S := S)
      (i := i) (C := v.constraints) hSVariables)
    v.supported.toDerives v.satisfies
    (constraintsBelow_mono v.supported.constraints_below hLimit)
    hLocalSat hEBound hTyBound hVariables.2
    (lazyTy_below hSBound)
    hEnv hTy
    (Nat.le_trans v.stop_ge hLimit)
    v.preservesPrefix

theorem buildable_abs
    {Γ : Strictness.Env} {σ τ : Strictness.Ty}
    {u : Usage} {body : Term}
    (hChild : Buildable (σ :: Γ) body τ)
    (hu : u ≤ τ.outer) :
    Buildable (Strictness.Env.scale u Γ)
      (.lam body) (.arrow σ τ u) := by
  intro start initial
  obtain ⟨w⟩ := hChild start initial
  let p : Raw.Expr := .var w.stop
  let ν := setUsage w.valuation w.stop u
  let limit := w.stop + 1

  have hAgree : AgreeBelow w.stop ν w.valuation := by
    intro i hi
    have hNe : i ≠ w.stop := by omega
    simp [ν, setUsage, hNe]
  let v := w.revalue hAgree
  have hLimit : v.stop ≤ limit := by
    change w.stop ≤ w.stop + 1
    omega
  have hpEval : p.eval v.valuation = u := by
    change (setUsage w.valuation w.stop u) w.stop = u
    simp [setUsage]
  have hpBound : ExprBelow limit p := by
    change w.stop < w.stop + 1
    omega

  cases hCtx : v.ctx with
  | nil =>
      have hEval := v.ctx_eval
      rw [hCtx, Raw.Env.eval] at hEval
      cases hEval
  | cons A G =>
      have hCtxEval :
          A.eval v.valuation :: Raw.Env.eval v.valuation G = σ :: Γ := by
        simpa only [hCtx, Raw.Env.eval] using v.ctx_eval
      obtain ⟨hAEval, hGEval⟩ := List.cons.inj hCtxEval

      have hVariables := v.supported.toDerives.boundary_variables
      have hCtxVariables : VariableEnv (A :: G) := by
        simpa only [hCtx] using hVariables.1
      have hAVariables := hCtxVariables A (by simp)

      have hCtxBound : EnvBelow limit (A :: G) := by
        simpa only [hCtx] using envBelow_mono v.ctx_below hLimit
      have hABound := hCtxBound A (by simp)
      have hGBound : EnvBelow limit G := by
        intro B hMem
        exact hCtxBound B (List.mem_cons_of_mem _ hMem)
      have hBodyBound := tyBelow_mono v.ty_below hLimit

      let E := Raw.Env.scale p G
      let B : RTy := .arrow A v.ty p
      have hEBound := envBelow_scale hpBound hGBound
      have hBBound : TyBelow limit B :=
        ⟨hABound, hBodyBound, hpBound⟩
      have hBVariables : VariableTy B :=
        ⟨hAVariables, hVariables.2, True.intro⟩

      have hLocalSat :
        Raw.UseConstraints.Satisfies v.valuation
          ([⟨p, v.ty.outer⟩] : UC) := by
        intro c hc
        have hEq : c = ⟨p, v.ty.outer⟩ := List.mem_singleton.mp hc
        subst c
        change p.eval v.valuation ≤ v.ty.outer.eval v.valuation
        rw [hpEval, Raw.Ty.eval_outer, v.ty_eval]
        exact hu

      have hChildDerives :
          Derives (A :: G) body v.ty v.constraints := by
        simpa only [hCtx] using v.supported.toDerives
      have hEEval :
          Raw.Env.eval v.valuation E = Strictness.Env.scale u Γ := by
        dsimp [E]
        rw [Raw.Env.eval_scale, hpEval, hGEval]
      have hBEval : B.eval v.valuation = .arrow σ τ u := by
        change
          Strictness.Ty.arrow
            (A.eval v.valuation) (v.ty.eval v.valuation)
            (p.eval v.valuation) = .arrow σ τ u
        rw [hAEval, v.ty_eval, hpEval]

      have hEnv :
          Strictness.Env.Subtype
            (Strictness.Env.scale u Γ) (Raw.Env.eval v.valuation E) := by
        rw [hEEval]
        exact envSubtype_refl _
      have hTy :
          Strictness.Ty.Subtype (B.eval v.valuation) (.arrow σ τ u) := by
        rw [hBEval]
        exact subtype_refl _

      exact completeUnary
        (start := start) (initial := initial)
        (limit := limit) (ν := v.valuation)
        (Rule.abs
          (Γ := G) (A := A) (B := v.ty) (u := p)
          (e := body) (C := v.constraints) (by trivial))
        hChildDerives v.satisfies
        (constraintsBelow_mono v.supported.constraints_below hLimit)
        hLocalSat hEBound hBBound hBVariables
        (constraintsBelow_singleton hpBound (tyBelow_outer hBodyBound))
        hEnv hTy
        (Nat.le_trans v.stop_ge hLimit)
        v.preservesPrefix

theorem buildable_proj
    {Γ : Strictness.Env} {σ τ : Strictness.Ty}
    {u : Usage} {body : Term}
    (left : Bool)
    (hChild : Buildable Γ body (.prod σ τ u))
    (hu : u ≤ (if left then σ else τ).outer)
    (hLazy : Strictness.Ty.IsLazy (if left then τ else σ)) :
    Buildable Γ (.proj left body) (if left then σ else τ) := by
  intro start initial
  obtain ⟨w⟩ := hChild start initial
  obtain ⟨A, B, p, hShape, hAEval, hBEval, hpEval⟩ :=
    rawTy_prod_components w.ty_eval

  have hVariables := w.supported.toDerives.boundary_variables
  have hProdVariables : VariableTy (.prod A B p) := by
    rw [← hShape]
    exact hVariables.2
  have hProdBound : TyBelow w.stop (.prod A B p) := by
    rw [← hShape]
    exact w.ty_below

  let S := if left then A else B
  let O := if left then B else A

  have hSVariables : VariableTy S := by
    cases left with
    | false => exact hProdVariables.2.1
    | true => exact hProdVariables.1
  have hSBound : TyBelow w.stop S := by
    cases left with
    | false => exact hProdBound.2.1
    | true => exact hProdBound.1
  have hOBound : TyBelow w.stop O := by
    cases left with
    | false => exact hProdBound.1
    | true => exact hProdBound.2.1
  have hSEval :
      S.eval w.valuation = (if left then σ else τ) := by
    cases left with
    | false => exact hBEval
    | true => exact hAEval
  have hOEval :
      O.eval w.valuation = (if left then τ else σ) := by
    cases left with
    | false => exact hAEval
    | true => exact hBEval

  have hChildDerives :
      Derives w.ctx body (.prod A B p) w.constraints := by
    rw [← hShape]
    exact w.supported.toDerives

  have hRule :
      Rule [⟨w.ctx, body, .prod A B p, w.constraints⟩]
        (.proj left body) w.ctx S
        ([⟨p, S.outer⟩] ++ O.lazyConstraints) := by
    cases left with
    | false => exact Rule.projRight
    | true => exact Rule.projLeft

  have hUseSat :
    Raw.UseConstraints.Satisfies w.valuation
      ([⟨p, S.outer⟩] : UC) := by
    intro c hc
    have hEq : c = ⟨p, S.outer⟩ := List.mem_singleton.mp hc
    subst c
    change p.eval w.valuation ≤ S.outer.eval w.valuation
    rw [hpEval, Raw.Ty.eval_outer, hSEval]
    exact hu
  have hLazySat : O.lazyConstraints.Satisfies w.valuation := by
    apply (Raw.Ty.eval_lazyConstraints w.valuation O).mpr
    rw [hOEval]
    exact hLazy

  have hEnv :
      Strictness.Env.Subtype Γ (Raw.Env.eval w.valuation w.ctx) := by
    rw [w.ctx_eval]
    exact envSubtype_refl _
  have hTy :
      Strictness.Ty.Subtype
        (S.eval w.valuation) (if left then σ else τ) := by
    rw [hSEval]
    exact subtype_refl _

  exact completeUnary
    (start := start) (initial := initial)
    (limit := w.stop) (ν := w.valuation)
    hRule hChildDerives w.satisfies w.supported.constraints_below
    (Raw.UseConstraints.satisfies_append.mpr ⟨hUseSat, hLazySat⟩)
    w.ctx_below hSBound hSVariables
    (constraintsBelow_append
      (constraintsBelow_singleton hProdBound.2.2 (tyBelow_outer hSBound))
      (lazyTy_below hOBound))
    hEnv hTy w.stop_ge w.preservesPrefix

theorem buildable_sub
    {Γ Γ' : Strictness.Env}
    {τ τ' : Strictness.Ty} {e : Term}
    (hChild : Buildable Γ e τ)
    (hEnv : Strictness.Env.Subtype Γ' Γ)
    (hTy : Strictness.Ty.Subtype τ τ') :
    Buildable Γ' e τ' := by
  intro start initial
  obtain ⟨w⟩ := hChild start initial
  have hEnvBound :
      Strictness.Env.Subtype Γ' (Raw.Env.eval w.valuation w.ctx) := by
    rw [w.ctx_eval]
    exact hEnv
  have hTyBound :
      Strictness.Ty.Subtype (w.ty.eval w.valuation) τ' := by
    rw [w.ty_eval]
    exact hTy
  exact completeSupported
    w.supported w.satisfies hEnvBound hTyBound
    w.stop_ge w.preservesPrefix

end Strictness.RawInference.CoreBoundary
