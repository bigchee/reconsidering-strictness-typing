import Strictness.Inference.Construction.Infrastructure

/-!
Completeness constructions for conditionals and recursive expressions.

The fix construction accounts for outer strictness raising and the recursive
context. The conditional construction combines three prepared premises.
-/

namespace Strictness.RawInference.CoreBoundary

open Raw

theorem buildable_ite
    {Γ Γ₀ Γ₁ Γ₂ Γ₁₂ : Strictness.Env}
    {u : Usage} {τ₁ τ₂ τ : Strictness.Ty}
    {e₀ e₁ e₂ : Term}
    (hCond : Buildable Γ₀ e₀ (.int u))
    (hThen : Buildable Γ₁ e₁ τ₁)
    (hElse : Buildable Γ₂ e₂ τ₂)
    (hSubThen : Strictness.Ty.Subtype τ₁ τ)
    (hSubElse : Strictness.Ty.Subtype τ₂ τ)
    (hu : u ≤ τ.outer)
    (hCap : Strictness.Env.cap Γ₁ Γ₂ = some Γ₁₂)
    (hPlus : Strictness.Env.plus Γ₀ Γ₁₂ = some Γ) :
    Buildable Γ (.ite e₀ e₁ e₂) τ := by
  intro start initial
  obtain ⟨k, ν₀, r₀, r₁, r₂, hStart, hPrefix⟩ :=
    buildable_three hCond hThen hElse start initial

  let T := allocatedTy k τ
  let ν := writeTy τ ν₀ k
  let limit := k + annotationCount τ
  have hAgree : AgreeBelow k ν ν₀ :=
    writeTy_agreeBelow τ ν₀ (Nat.le_refl k)
  have hLe : k ≤ limit := by
    dsimp [limit]
    omega
  let v₀ := (r₀.revalue hAgree).weaken hLe
  let v₁ := (r₁.revalue hAgree).weaken hLe
  let v₂ := (r₂.revalue hAgree).weaken hLe

  have hTVariables : VariableTy T := allocatedTy_variables τ k
  have hTBound : TyBelow limit T := allocatedTy_below τ k
  have hTEval : T.eval ν = τ := allocatedTy_eval_writeTy τ ν₀ k

  obtain ⟨p, hCondShape, hpEval⟩ :=
    rawTy_int_component v₀.ty_eval
  have hpBound : ExprBelow limit p := by
    have h := v₀.ty_below
    rw [hCondShape] at h
    exact h
  have hPrefix' : AgreeBelow start ν initial := by
    intro i hi
    exact (hAgree i (Nat.lt_of_lt_of_le hi hStart)).trans (hPrefix i hi)

  have hRawSubThen :
      Strictness.Ty.Subtype (v₁.ty.eval ν) (T.eval ν) := by
    rw [v₁.ty_eval, hTEval]
    exact hSubThen
  have hRawSubElse :
      Strictness.Ty.Subtype (v₂.ty.eval ν) (T.eval ν) := by
    rw [v₂.ty_eval, hTEval]
    exact hSubElse
  obtain ⟨CA, hExpandA, hSatA⟩ := rawSub_complete hRawSubThen
  obtain ⟨CB, hExpandB, hSatB⟩ := rawSub_complete hRawSubElse

  have hConcreteCap :
      Strictness.Env.combine Boundary.CombineOp.cap.usage
        (Raw.Env.eval ν v₁.ctx) (Raw.Env.eval ν v₂.ctx) =
        some Γ₁₂ := by
    change Strictness.Env.cap
      (Raw.Env.eval ν v₁.ctx) (Raw.Env.eval ν v₂.ctx) = some Γ₁₂
    rw [v₁.ctx_eval, v₂.ctx_eval]
    exact hCap
  obtain ⟨E₁₂, Ccap, hComposeCap, hCapSat, hE₁₂Eval⟩ :=
    composeEnv_complete .cap hConcreteCap
  obtain ⟨hE₁₂Bound, hCapBound⟩ :=
    composeEnv_below .cap v₁.ctx_below v₂.ctx_below hComposeCap

  have hConcretePlus :
      Strictness.Env.combine Boundary.CombineOp.plus.usage
        (Raw.Env.eval ν v₀.ctx) (Raw.Env.eval ν E₁₂) = some Γ := by
    change Strictness.Env.plus
      (Raw.Env.eval ν v₀.ctx) (Raw.Env.eval ν E₁₂) = some Γ
    rw [v₀.ctx_eval, hE₁₂Eval]
    exact hPlus
  obtain ⟨E, Cplus, hComposePlus, hPlusSat, hEEval⟩ :=
    composeEnv_complete .plus hConcretePlus
  obtain ⟨hEBound, hPlusBound⟩ :=
    composeEnv_below .plus v₀.ctx_below hE₁₂Bound hComposePlus

  have hUseSat :
      Raw.UseConstraints.Satisfies ν [⟨p, T.outer⟩] := by
    apply singleton_satisfied
    rw [hpEval, Raw.Ty.eval_outer, hTEval]
    exact hu

  have hRule :
      Rule [v₀.toPremise, v₁.toPremise, v₂.toPremise]
        (.ite e₀ e₁ e₂) E T
        (Ccap ++ Cplus ++ CA ++ CB ++ [⟨p, T.outer⟩]) := by
    simpa only [ReadyPremise.toPremise, hCondShape] using
      (Rule.ite
        (u := p) (T := T)
        (e₀ := e₀) (e₁ := e₁) (e₂ := e₂)
        (C₀ := v₀.constraints)
        (C₁ := v₁.constraints)
        (C₂ := v₂.constraints)
        hTVariables hComposeCap hComposePlus hExpandA hExpandB)

  have hLocalSat :
      Raw.UseConstraints.Satisfies ν
        (Ccap ++ Cplus ++ CA ++ CB ++ [⟨p, T.outer⟩]) :=
    Raw.UseConstraints.satisfies_append.mpr
      ⟨Raw.UseConstraints.satisfies_append.mpr
         ⟨Raw.UseConstraints.satisfies_append.mpr
            ⟨Raw.UseConstraints.satisfies_append.mpr
               ⟨hCapSat, hPlusSat⟩,
             hSatA⟩,
          hSatB⟩,
       hUseSat⟩

  have hLocalBound :
      ConstraintsBelow limit
        (Ccap ++ Cplus ++ CA ++ CB ++ [⟨p, T.outer⟩]) :=
    constraintsBelow_append
      (constraintsBelow_append
        (constraintsBelow_append
          (constraintsBelow_append hCapBound hPlusBound)
          (subtypeConstraints_below v₁.ty_below hTBound hExpandA))
        (subtypeConstraints_below v₂.ty_below hTBound hExpandB))
      (constraintsBelow_singleton hpBound (tyBelow_outer hTBound))

  have hEnv : Strictness.Env.Subtype Γ (Raw.Env.eval ν E) := by
    rw [hEEval]
    exact envSubtype_refl _
  have hTy : Strictness.Ty.Subtype (T.eval ν) τ := by
    rw [hTEval]
    exact subtype_refl _

  exact completeTernary v₀ v₁ v₂ hRule
    hLocalSat hEBound hTBound hTVariables hLocalBound
    hEnv hTy (Nat.le_trans hStart hLe) hPrefix'

/-- Realize a declarative fix step using the same child's variable boundary. -/
theorem buildable_fix
    {Γ Δ : Strictness.Env} {σ τ : Strictness.Ty} {body : Term}
    (hChild : Buildable (σ :: Γ) body τ)
    (hSub : Strictness.Ty.Subtype τ (Strictness.Ty.raiseStrict σ))
    (hPlus : Strictness.Env.plus Γ
      (Strictness.Env.scale (Usage.scale σ.outer Usage.top) Γ) = some Δ) :
    Buildable Δ (.fix body) τ := by
  intro start initial
  obtain ⟨v⟩ := hChild start initial
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
      have hCtxBound : EnvBelow v.stop (A :: G) := by
        simpa only [hCtx] using v.ctx_below
      have hABound := hCtxBound A (by simp)
      have hGBound : EnvBelow v.stop G := by
        intro B hMem
        exact hCtxBound B (List.mem_cons_of_mem _ hMem)
      let p : Raw.Expr := .scale A.outer (.lit .top)
      have hpBound : ExprBelow v.stop p :=
        ⟨tyBelow_outer hABound, True.intro⟩
      have hOp : Strictness.Env.combine Boundary.CombineOp.plus.usage
          (Raw.Env.eval v.valuation G)
          ((Raw.Env.scale p G).eval v.valuation) = some Δ := by
        simpa only [Raw.Env.eval_scale, p, Raw.Expr.eval, Raw.Ty.eval_outer,
          hAEval, hGEval, Boundary.CombineOp.usage] using hPlus
      obtain ⟨E, Cplus, hCompose, hPlusSat, hEEval⟩ :=
        composeEnv_complete .plus hOp
      have hComparison : Strictness.Ty.Subtype
          (v.ty.eval v.valuation) (A.raiseStrict.eval v.valuation) := by
        simpa only [Raw.Ty.eval_raiseStrict, hAEval, v.ty_eval] using hSub
      obtain ⟨Csub, hRawSub, hSubSat⟩ := rawSub_complete hComparison
      obtain ⟨hEBound, hPlusBound⟩ :=
        composeEnv_below .plus hGBound (envBelow_scale hpBound hGBound) hCompose
      have hLocalBound : ConstraintsBelow v.stop (Cplus ++ Csub) :=
        constraintsBelow_append hPlusBound
          (subtypeConstraints_below v.ty_below (tyBelow_raiseStrict hABound) hRawSub)
      have hBodyDerives : Derives (A :: G) body v.ty v.constraints := by
        simpa only [hCtx] using v.supported.toDerives
      have hEnv : Strictness.Env.Subtype Δ (E.eval v.valuation) := by
        rw [hEEval]
        exact envSubtype_refl _
      have hTy : Strictness.Ty.Subtype (v.ty.eval v.valuation) τ := by
        rw [v.ty_eval]
        exact subtype_refl _
      exact completeUnary
        (Rule.fix hCompose hRawSub) hBodyDerives v.satisfies
        v.supported.constraints_below
        (Raw.UseConstraints.satisfies_append.mpr ⟨hPlusSat, hSubSat⟩)
        hEBound v.ty_below hVariables.2 hLocalBound hEnv hTy
        v.stop_ge v.preservesPrefix

end Strictness.RawInference.CoreBoundary
