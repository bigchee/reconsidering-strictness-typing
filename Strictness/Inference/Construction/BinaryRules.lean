import Strictness.Inference.Construction.Infrastructure

/-!
Completeness constructions for application, pairs, arithmetic and let.

Uses the shared preparation of two child witnesses and boundary completion.
-/

namespace Strictness.RawInference.CoreBoundary

open Raw

theorem buildable_app
    {Γ Γ₁ Γ₂ : Strictness.Env}
    {σ σ' τ : Strictness.Ty} {u : Usage}
    {e₁ e₂ : Term}
    (hFun : Buildable Γ₁ e₁ (.arrow σ τ u))
    (hArg : Buildable Γ₂ e₂ σ')
    (hSub : Strictness.Ty.Subtype σ' σ)
    (hu : u ≤ τ.outer)
    (hPlus :
      Strictness.Env.plus Γ₁ (Strictness.Env.scale u Γ₂) = some Γ) :
    Buildable Γ (.app e₁ e₂) τ := by
  intro start initial
  obtain ⟨limit, ν, v₁, v₂, hStart, hPrefix⟩ :=
    buildable_two hFun hArg start initial
  obtain ⟨A, B, p, hShape, hAEval, hBEval, hpEval⟩ :=
    rawTy_arrow_components v₁.ty_eval
  have hArrowVariables : VariableTy (.arrow A B p) := by
    rw [← hShape]
    exact v₁.variables.2
  have hArrowBound : TyBelow limit (.arrow A B p) := by
    rw [← hShape]
    exact v₁.ty_below

  have hRawSub :
      Strictness.Ty.Subtype (v₂.ty.eval ν) (A.eval ν) := by
    rw [v₂.ty_eval, hAEval]
    exact hSub
  obtain ⟨Csub, hExpandSub, hSubSat⟩ := rawSub_complete hRawSub

  have hConcretePlus :
      Strictness.Env.combine Boundary.CombineOp.plus.usage
        (Raw.Env.eval ν v₁.ctx)
        (Raw.Env.eval ν (Raw.Env.scale p v₂.ctx)) = some Γ := by
    change Strictness.Env.plus
      (Raw.Env.eval ν v₁.ctx)
      (Raw.Env.eval ν (Raw.Env.scale p v₂.ctx)) = some Γ
    rw [Raw.Env.eval_scale, v₁.ctx_eval, v₂.ctx_eval, hpEval]
    exact hPlus
  obtain ⟨E, Cplus, hCompose, hPlusSat, hEEval⟩ :=
    composeEnv_complete .plus hConcretePlus
  obtain ⟨hEBound, hPlusBound⟩ :=
    composeEnv_below .plus v₁.ctx_below
      (envBelow_scale hArrowBound.2.2 v₂.ctx_below) hCompose

  have hUseSat :
      Raw.UseConstraints.Satisfies ν [⟨p, B.outer⟩] := by
    apply singleton_satisfied
    rw [hpEval, Raw.Ty.eval_outer, hBEval]
    exact hu
  have hRule :
      Rule [v₁.toPremise, v₂.toPremise] (.app e₁ e₂) E B
        (Cplus ++ Csub ++ [⟨p, B.outer⟩]) := by
    simpa only [ReadyPremise.toPremise, hShape] using
      (Rule.app
        (e₁ := e₁) (e₂ := e₂)
        (C₁ := v₁.constraints) (C₂ := v₂.constraints)
        hCompose hExpandSub)

  have hEnv :
      Strictness.Env.Subtype Γ (Raw.Env.eval ν E) := by
    rw [hEEval]
    exact envSubtype_refl _
  have hTy : Strictness.Ty.Subtype (B.eval ν) τ := by
    rw [hBEval]
    exact subtype_refl _

  exact completeBinary v₁ v₂ hRule
    (Raw.UseConstraints.satisfies_append.mpr
      ⟨Raw.UseConstraints.satisfies_append.mpr
        ⟨hPlusSat, hSubSat⟩, hUseSat⟩)
    hEBound hArrowBound.2.1 hArrowVariables.2.1
    (constraintsBelow_three hPlusBound
      (subtypeConstraints_below v₂.ty_below hArrowBound.1 hExpandSub)
      (constraintsBelow_singleton
        hArrowBound.2.2 (tyBelow_outer hArrowBound.2.1)))
    hEnv hTy hStart hPrefix

theorem buildable_pair
    {Γ Γ₁ Γ₂ : Strictness.Env}
    {σ τ : Strictness.Ty} {u : Usage}
    {e₁ e₂ : Term}
    (hLeft : Buildable Γ₁ e₁ σ)
    (hRight : Buildable Γ₂ e₂ τ)
    (hσ : σ.outer ≤ u ⊔ Usage.lazy)
    (hτ : τ.outer ≤ u ⊔ Usage.lazy)
    (hPlus : Strictness.Env.plus Γ₁ Γ₂ = some Γ) :
    Buildable Γ (.pair e₁ e₂) (.prod σ τ u) := by
  intro start initial
  obtain ⟨k, ν₀, r₁, r₂, hStart, hPrefix⟩ :=
    buildable_two hLeft hRight start initial
  let p : Raw.Expr := .var k
  let ν := setUsage ν₀ k u
  let limit := k + 1
  have hAgree : AgreeBelow k ν ν₀ := setUsage_agreeBelow ν₀ k u
  have hLe : k ≤ limit := by dsimp [limit]; omega
  let v₁ := (r₁.revalue hAgree).weaken hLe
  let v₂ := (r₂.revalue hAgree).weaken hLe
  have hpEval : p.eval ν = u := by
    change (setUsage ν₀ k u) k = u
    simp [setUsage]
  have hpBound : ExprBelow limit p := by change k < k + 1; omega
  have hPrefix' : AgreeBelow start ν initial := by
    intro i hi
    exact (hAgree i (Nat.lt_of_lt_of_le hi hStart)).trans (hPrefix i hi)

  have hConcretePlus :
      Strictness.Env.combine Boundary.CombineOp.plus.usage
        (Raw.Env.eval ν v₁.ctx) (Raw.Env.eval ν v₂.ctx) = some Γ := by
    change Strictness.Env.plus
      (Raw.Env.eval ν v₁.ctx) (Raw.Env.eval ν v₂.ctx) = some Γ
    rw [v₁.ctx_eval, v₂.ctx_eval]
    exact hPlus
  obtain ⟨E, Cplus, hCompose, hPlusSat, hEEval⟩ :=
    composeEnv_complete .plus hConcretePlus
  obtain ⟨hEBound, hPlusBound⟩ :=
    composeEnv_below .plus v₁.ctx_below v₂.ctx_below hCompose

  have hUse₁ :
      Raw.UseConstraints.Satisfies ν
        [⟨v₁.ty.outer, .join p (.lit .lazy)⟩] := by
    apply singleton_satisfied
    simpa only [Raw.Ty.eval_outer, Raw.Expr.eval, v₁.ty_eval, hpEval] using hσ
  have hUse₂ :
      Raw.UseConstraints.Satisfies ν
        [⟨v₂.ty.outer, .join p (.lit .lazy)⟩] := by
    apply singleton_satisfied
    simpa only [Raw.Ty.eval_outer, Raw.Expr.eval, v₂.ty_eval, hpEval] using hτ
  have hUsesSat :
      Raw.UseConstraints.Satisfies ν
        [⟨v₁.ty.outer, .join p (.lit .lazy)⟩,
         ⟨v₂.ty.outer, .join p (.lit .lazy)⟩] := by
    change Raw.UseConstraints.Satisfies ν
      ([⟨v₁.ty.outer, .join p (.lit .lazy)⟩] ++
       [⟨v₂.ty.outer, .join p (.lit .lazy)⟩])
    exact Raw.UseConstraints.satisfies_append.mpr ⟨hUse₁, hUse₂⟩

  have hUsesBound :
      ConstraintsBelow limit
        [⟨v₁.ty.outer, .join p (.lit .lazy)⟩,
         ⟨v₂.ty.outer, .join p (.lit .lazy)⟩] := by
    change ConstraintsBelow limit
      ([⟨v₁.ty.outer, .join p (.lit .lazy)⟩] ++
       [⟨v₂.ty.outer, .join p (.lit .lazy)⟩])
    exact constraintsBelow_append
      (constraintsBelow_singleton (tyBelow_outer v₁.ty_below)
        ⟨hpBound, True.intro⟩)
      (constraintsBelow_singleton (tyBelow_outer v₂.ty_below)
        ⟨hpBound, True.intro⟩)

  let B : RTy := .prod v₁.ty v₂.ty p
  have hBEval : B.eval ν = .prod σ τ u := by
    change Strictness.Ty.prod
      (v₁.ty.eval ν) (v₂.ty.eval ν) (p.eval ν) = .prod σ τ u
    rw [v₁.ty_eval, v₂.ty_eval, hpEval]
  have hRule :
      Rule [v₁.toPremise, v₂.toPremise] (.pair e₁ e₂) E B
        (Cplus ++
          [⟨v₁.ty.outer, .join p (.lit .lazy)⟩,
           ⟨v₂.ty.outer, .join p (.lit .lazy)⟩]) :=
    Rule.pair hCompose
  have hEnv : Strictness.Env.Subtype Γ (Raw.Env.eval ν E) := by
    rw [hEEval]
    exact envSubtype_refl _
  have hTy :
      Strictness.Ty.Subtype (B.eval ν) (.prod σ τ u) := by
    rw [hBEval]
    exact subtype_refl _

  exact completeBinary v₁ v₂ hRule
    (Raw.UseConstraints.satisfies_append.mpr ⟨hPlusSat, hUsesSat⟩)
    hEBound
    ⟨v₁.ty_below, v₂.ty_below, hpBound⟩
    ⟨v₁.variables.2, v₂.variables.2, True.intro⟩
    (constraintsBelow_append hPlusBound hUsesBound)
    hEnv hTy (Nat.le_trans hStart hLe) hPrefix'

theorem buildable_op
    {Γ Γ₁ Γ₂ : Strictness.Env}
    {u₁ u₂ u : Usage} {e₁ e₂ : Term}
    (hLeft : Buildable Γ₁ e₁ (.int u₁))
    (hRight : Buildable Γ₂ e₂ (.int u₂))
    (hu₁ : u₁ ≤ u) (hu₂ : u₂ ≤ u)
    (hPlus : Strictness.Env.plus Γ₁ Γ₂ = some Γ) :
    Buildable Γ (.op o e₁ e₂) (.int u) := by
  intro start initial
  obtain ⟨k, ν₀, r₁, r₂, hStart, hPrefix⟩ :=
    buildable_two hLeft hRight start initial
  let p : Raw.Expr := .var k
  let ν := setUsage ν₀ k u
  let limit := k + 1
  have hAgree : AgreeBelow k ν ν₀ := setUsage_agreeBelow ν₀ k u
  have hLe : k ≤ limit := by dsimp [limit]; omega
  let v₁ := (r₁.revalue hAgree).weaken hLe
  let v₂ := (r₂.revalue hAgree).weaken hLe
  obtain ⟨p₁, hShape₁, hp₁Eval⟩ := rawTy_int_component v₁.ty_eval
  obtain ⟨p₂, hShape₂, hp₂Eval⟩ := rawTy_int_component v₂.ty_eval
  have hpEval : p.eval ν = u := by
    change (setUsage ν₀ k u) k = u
    simp [setUsage]
  have hpBound : ExprBelow limit p := by change k < k + 1; omega
  have hp₁Bound : ExprBelow limit p₁ := by
    have h := v₁.ty_below
    rw [hShape₁] at h
    exact h
  have hp₂Bound : ExprBelow limit p₂ := by
    have h := v₂.ty_below
    rw [hShape₂] at h
    exact h
  have hPrefix' : AgreeBelow start ν initial := by
    intro i hi
    exact (hAgree i (Nat.lt_of_lt_of_le hi hStart)).trans (hPrefix i hi)

  have hConcretePlus :
      Strictness.Env.combine Boundary.CombineOp.plus.usage
        (Raw.Env.eval ν v₁.ctx) (Raw.Env.eval ν v₂.ctx) = some Γ := by
    change Strictness.Env.plus
      (Raw.Env.eval ν v₁.ctx) (Raw.Env.eval ν v₂.ctx) = some Γ
    rw [v₁.ctx_eval, v₂.ctx_eval]
    exact hPlus
  obtain ⟨E, Cplus, hCompose, hPlusSat, hEEval⟩ :=
    composeEnv_complete .plus hConcretePlus
  obtain ⟨hEBound, hPlusBound⟩ :=
    composeEnv_below .plus v₁.ctx_below v₂.ctx_below hCompose

  have hUse₁ : Raw.UseConstraints.Satisfies ν [⟨p₁, p⟩] := by
    apply singleton_satisfied
    rw [hp₁Eval, hpEval]
    exact hu₁
  have hUse₂ : Raw.UseConstraints.Satisfies ν [⟨p₂, p⟩] := by
    apply singleton_satisfied
    rw [hp₂Eval, hpEval]
    exact hu₂
  have hUsesSat :
      Raw.UseConstraints.Satisfies ν [⟨p₁, p⟩, ⟨p₂, p⟩] := by
    change Raw.UseConstraints.Satisfies ν ([⟨p₁, p⟩] ++ [⟨p₂, p⟩])
    exact Raw.UseConstraints.satisfies_append.mpr ⟨hUse₁, hUse₂⟩
  have hUsesBound :
      ConstraintsBelow limit [⟨p₁, p⟩, ⟨p₂, p⟩] := by
    change ConstraintsBelow limit ([⟨p₁, p⟩] ++ [⟨p₂, p⟩])
    exact constraintsBelow_append
      (constraintsBelow_singleton hp₁Bound hpBound)
      (constraintsBelow_singleton hp₂Bound hpBound)

  have hRule :
      Rule [v₁.toPremise, v₂.toPremise] (.op o e₁ e₂) E (.int p)
        (Cplus ++ [⟨p₁, p⟩, ⟨p₂, p⟩]) := by
    simpa only [ReadyPremise.toPremise, hShape₁, hShape₂] using
      (Rule.op o
        (u₁ := p₁) (u₂ := p₂) (u := p)
        (e₁ := e₁) (e₂ := e₂)
        (C₁ := v₁.constraints) (C₂ := v₂.constraints) hCompose)
  have hEnv : Strictness.Env.Subtype Γ (Raw.Env.eval ν E) := by
    rw [hEEval]
    exact envSubtype_refl _
  have hTy :
      Strictness.Ty.Subtype ((Raw.Ty.int p).eval ν) (.int u) := by
    change Strictness.Ty.Subtype (.int (p.eval ν)) (.int u)
    rw [hpEval]
    exact subtype_refl _

  exact completeBinary v₁ v₂ hRule
    (Raw.UseConstraints.satisfies_append.mpr ⟨hPlusSat, hUsesSat⟩)
    hEBound hpBound (by trivial)
    (constraintsBelow_append hPlusBound hUsesBound)
    hEnv hTy (Nat.le_trans hStart hLe) hPrefix'

theorem buildable_let
    {Γ Γ₁ Γ₂ : Strictness.Env}
    {σ σ' τ : Strictness.Ty} {e₁ e₂ : Term}
    (hDef : Buildable Γ₁ e₁ σ)
    (hBody : Buildable (σ' :: Γ₂) e₂ τ)
    (hSub : Strictness.Ty.Subtype σ σ')
    (hPlus : Strictness.Env.plus Γ₁ Γ₂ = some Γ) :
    Buildable Γ (.letE e₁ e₂) τ := by
  intro start initial
  obtain ⟨limit, ν, v₁, v₂, hStart, hPrefix⟩ :=
    buildable_two hDef hBody start initial
  cases hCtx : v₂.ctx with
  | nil =>
      have hEval := v₂.ctx_eval
      rw [hCtx, Raw.Env.eval] at hEval
      cases hEval
  | cons A' G =>
      have hCtxEval :
          A'.eval ν :: Raw.Env.eval ν G = σ' :: Γ₂ := by
        simpa only [hCtx, Raw.Env.eval] using v₂.ctx_eval
      obtain ⟨hA'Eval, hGEval⟩ := List.cons.inj hCtxEval
      have hCtxBound : EnvBelow limit (A' :: G) := by
        simpa only [hCtx] using v₂.ctx_below
      have hA'Bound := hCtxBound A' (by simp)
      have hGBound : EnvBelow limit G := by
        intro A hMem
        exact hCtxBound A (List.mem_cons_of_mem _ hMem)

      have hRawSub :
          Strictness.Ty.Subtype (v₁.ty.eval ν) (A'.eval ν) := by
        rw [v₁.ty_eval, hA'Eval]
        exact hSub
      obtain ⟨Csub, hExpandSub, hSubSat⟩ := rawSub_complete hRawSub

      have hConcretePlus :
          Strictness.Env.combine Boundary.CombineOp.plus.usage
            (Raw.Env.eval ν v₁.ctx) (Raw.Env.eval ν G) = some Γ := by
        change Strictness.Env.plus
          (Raw.Env.eval ν v₁.ctx) (Raw.Env.eval ν G) = some Γ
        rw [v₁.ctx_eval, hGEval]
        exact hPlus
      obtain ⟨E, Cplus, hCompose, hPlusSat, hEEval⟩ :=
        composeEnv_complete .plus hConcretePlus
      obtain ⟨hEBound, hPlusBound⟩ :=
        composeEnv_below .plus v₁.ctx_below hGBound hCompose

      have hRule :
          Rule [v₁.toPremise, v₂.toPremise] (.letE e₁ e₂) E v₂.ty
            (Cplus ++ Csub) := by
        simpa only [ReadyPremise.toPremise, hCtx] using
          (Rule.letE
            (e₁ := e₁) (e₂ := e₂)
            (C₁ := v₁.constraints) (C₂ := v₂.constraints)
            hCompose hExpandSub)
      have hEnv :
          Strictness.Env.Subtype Γ (Raw.Env.eval ν E) := by
        rw [hEEval]
        exact envSubtype_refl _
      have hTy :
          Strictness.Ty.Subtype (v₂.ty.eval ν) τ := by
        rw [v₂.ty_eval]
        exact subtype_refl _

      exact completeBinary v₁ v₂ hRule
        (Raw.UseConstraints.satisfies_append.mpr ⟨hPlusSat, hSubSat⟩)
        hEBound v₂.ty_below v₂.variables.2
        (constraintsBelow_append hPlusBound
          (subtypeConstraints_below v₁.ty_below hA'Bound hExpandSub))
        hEnv hTy hStart hPrefix

end Strictness.RawInference.CoreBoundary
