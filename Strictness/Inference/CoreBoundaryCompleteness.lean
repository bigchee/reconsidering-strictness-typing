import Strictness.Inference.CoreBoundaryAllocation

namespace Strictness.RawInference.CoreBoundary

open Raw

/-- Sufficient fuel makes structural subtype expansion succeed. -/
private theorem subtypeFuel_exists
    {ν : Raw.Valuation} {n : Nat} {A B : RTy}
    (hFuel : sizeOf A + sizeOf B < n)
    (hSub :
      Strictness.Ty.Subtype (A.eval ν) (B.eval ν)) :
    ∃ C, Raw.Ty.subtypeConstraintsFuel n A B = some C := by
  induction n generalizing A B with
  | zero =>
      omega
  | succ n ih =>
      cases A with
      | int u =>
          cases B with
          | int v =>
              exact ⟨[⟨u, v⟩], rfl⟩
          | prod B₁ B₂ v =>
              cases hSub
          | arrow B₁ B₂ v =>
              cases hSub

      | prod A₁ A₂ u =>
          cases B with
          | int v =>
              cases hSub
          | arrow B₁ B₂ v =>
              cases hSub
          | prod B₁ B₂ v =>
              cases hSub with
              | prod h₁ h₂ hu =>
                  have hFuel₁ : sizeOf A₁ + sizeOf B₁ < n := by
                    simp at hFuel
                    omega
                  have hFuel₂ : sizeOf A₂ + sizeOf B₂ < n := by
                    simp at hFuel
                    omega
                  obtain ⟨C₁, hC₁⟩ := ih hFuel₁ h₁
                  obtain ⟨C₂, hC₂⟩ := ih hFuel₂ h₂
                  refine ⟨C₁ ++ C₂ ++ [⟨u, v⟩], ?_⟩
                  simp [Raw.Ty.subtypeConstraintsFuel, hC₁, hC₂]

      | arrow A₁ A₂ u =>
          cases B with
          | int v =>
              cases hSub
          | prod B₁ B₂ v =>
              cases hSub
          | arrow B₁ B₂ v =>
              cases hSub with
              | arrow h₁ h₂ hu =>
                  have hFuel₁ : sizeOf B₁ + sizeOf A₁ < n := by
                    simp at hFuel
                    omega
                  have hFuel₂ : sizeOf A₂ + sizeOf B₂ < n := by
                    simp at hFuel
                    omega
                  obtain ⟨C₁, hC₁⟩ := ih hFuel₁ h₁
                  obtain ⟨C₂, hC₂⟩ := ih hFuel₂ h₂
                  refine ⟨C₁ ++ C₂ ++ [⟨u, v⟩], ?_⟩
                  simp [Raw.Ty.subtypeConstraintsFuel, hC₁, hC₂]

/-- Every concrete subtype comparison has a satisfied constraint expansion. -/
theorem subtypeConstraints_complete
    {ν : Raw.Valuation} {A B : RTy}
    (hSub :
      Strictness.Ty.Subtype (A.eval ν) (B.eval ν)) :
    ∃ C,
      Raw.Ty.subtypeConstraints A B = some C ∧
      C.Satisfies ν := by
  obtain ⟨C, hC⟩ := subtypeFuel_exists
    (n := sizeOf A + sizeOf B + 1)
    (by omega) hSub
  have hExpand : Raw.Ty.subtypeConstraints A B = some C := hC
  exact ⟨C, hExpand,
    (Raw.Ty.eval_subtypeConstraints hExpand).mpr hSub⟩

theorem rawSub_complete
    {ν : Raw.Valuation} {A B : RTy}
    (hSub :
      Strictness.Ty.Subtype (A.eval ν) (B.eval ν)) :
    ∃ C, rawSub A B = some C ∧ C.Satisfies ν := by
  exact subtypeConstraints_complete hSub

theorem envSubtypeConstraints_complete
    {ν : Raw.Valuation} {Γ Δ : REnv}
    (hSub :
      Strictness.Env.Subtype (Γ.eval ν) (Δ.eval ν)) :
    ∃ C,
      Raw.Env.subtypeConstraints Γ Δ = some C ∧
      C.Satisfies ν := by
  induction Γ generalizing Δ with
  | nil =>
      cases Δ with
      | nil =>
          exact ⟨[], rfl, Raw.UseConstraints.satisfies_nil ν⟩
      | cons B Δ =>
          exact False.elim hSub
  | cons A Γ ih =>
      cases Δ with
      | nil =>
          exact False.elim hSub
      | cons B Δ =>
          rcases hSub with ⟨hHead, hTail⟩
          obtain ⟨CHead, hExpandHead, hSatHead⟩ :=
            subtypeConstraints_complete hHead
          obtain ⟨CTail, hExpandTail, hSatTail⟩ := ih hTail
          refine ⟨CHead ++ CTail, ?_, ?_⟩
          · simp [Raw.Env.subtypeConstraints, hExpandHead, hExpandTail]
          · exact Raw.UseConstraints.satisfies_append.mpr
              ⟨hSatHead, hSatTail⟩

/-- Concrete boundary comparisons suffice to construct Finish and its constraints. -/
theorem finish_exists
    {ν : Raw.Valuation}
    {E Δ : REnv} {B T : RTy}
    (hΔ : VariableEnv Δ)
    (hB : VariableTy B)
    (hT : VariableTy T)
    (hEnv :
      Strictness.Env.Subtype (Δ.eval ν) (E.eval ν))
    (hTy :
      Strictness.Ty.Subtype (B.eval ν) (T.eval ν)) :
    ∃ C, Finish E B Δ T C ∧ C.Satisfies ν := by
  obtain ⟨CΓ, hExpandΓ, hSatΓ⟩ :=
    envSubtypeConstraints_complete hEnv
  obtain ⟨Cτ, hExpandτ, hSatτ⟩ :=
    subtypeConstraints_complete hTy
  exact ⟨CΓ ++ Cτ,
    ⟨hΔ, hB, hT, CΓ, Cτ, hExpandΓ, hExpandτ, rfl⟩,
    Raw.UseConstraints.satisfies_append.mpr ⟨hSatΓ, hSatτ⟩⟩

theorem finish_exists_of_equal_eval
    {ν : Raw.Valuation}
    {E Δ : REnv} {B T : RTy}
    (hΔ : VariableEnv Δ)
    (hB : VariableTy B)
    (hT : VariableTy T)
    (hEnv : Δ.eval ν = E.eval ν)
    (hTy : B.eval ν = T.eval ν) :
    ∃ C, Finish E B Δ T C ∧ C.Satisfies ν := by
  apply finish_exists hΔ hB hT
  · rw [hEnv]
    exact envSubtype_refl _
  · rw [hTy]
    exact subtype_refl _

theorem equalTypes_complete
    {ν : Raw.Valuation} {A B : RTy}
    (hEqual : A.eval ν = B.eval ν) :
    ∃ C, Boundary.equalTypes A B = some C ∧ C.Satisfies ν := by
  have hAB :
      Strictness.Ty.Subtype (A.eval ν) (B.eval ν) := by
    rw [hEqual]
    exact subtype_refl _
  have hBA :
      Strictness.Ty.Subtype (B.eval ν) (A.eval ν) := by
    rw [hEqual]
    exact subtype_refl _
  obtain ⟨CAB, hExpandAB, hSatAB⟩ :=
    subtypeConstraints_complete hAB
  obtain ⟨CBA, hExpandBA, hSatBA⟩ :=
    subtypeConstraints_complete hBA
  refine ⟨CAB ++ CBA, ?_, ?_⟩
  · simp [Boundary.equalTypes, hExpandAB, hExpandBA]
  · exact Raw.UseConstraints.satisfies_append.mpr ⟨hSatAB, hSatBA⟩

private theorem composeTy_exists_satisfied
    {ν : Raw.Valuation}
    (op : Boundary.CombineOp)
    {A B : RTy}
    (hExists :
      ∃ R, Strictness.Ty.combine op.usage
        (A.eval ν) (B.eval ν) = some R) :
    ∃ D C,
      Boundary.composeTy op A B = some (D, C) ∧
      C.Satisfies ν := by
  induction A generalizing B with
  | int u =>
      obtain ⟨R, hOp⟩ := hExists
      cases B with
      | int v =>
          exact ⟨.int (op.expr u v), [], rfl,
            Raw.UseConstraints.satisfies_nil ν⟩
      | prod B₁ B₂ v =>
          simp [Raw.Ty.eval, Strictness.Ty.combine] at hOp
      | arrow B₁ B₂ v =>
          simp [Raw.Ty.eval, Strictness.Ty.combine] at hOp

  | prod A₁ A₂ u ih₁ ih₂ =>
      obtain ⟨R, hOp⟩ := hExists
      cases B with
      | int v =>
          simp [Raw.Ty.eval, Strictness.Ty.combine] at hOp
      | arrow B₁ B₂ v =>
          simp [Raw.Ty.eval, Strictness.Ty.combine] at hOp
      | prod B₁ B₂ v =>
          cases h₁ : Strictness.Ty.combine op.usage
              (A₁.eval ν) (B₁.eval ν) with
          | none =>
              simp [Raw.Ty.eval, Strictness.Ty.combine, h₁] at hOp
          | some R₁ =>
              cases h₂ : Strictness.Ty.combine op.usage
                  (A₂.eval ν) (B₂.eval ν) with
              | none =>
                  simp [Raw.Ty.eval, Strictness.Ty.combine, h₁, h₂]
                    at hOp
              | some R₂ =>
                  obtain ⟨D₁, C₁, hCompose₁, hSat₁⟩ :=
                    ih₁ ⟨R₁, h₁⟩
                  obtain ⟨D₂, C₂, hCompose₂, hSat₂⟩ :=
                    ih₂ ⟨R₂, h₂⟩
                  refine ⟨.prod D₁ D₂ (op.expr u v), C₁ ++ C₂, ?_, ?_⟩
                  · simp [Boundary.composeTy, hCompose₁, hCompose₂]
                  · exact Raw.UseConstraints.satisfies_append.mpr
                      ⟨hSat₁, hSat₂⟩

  | arrow A₁ A₂ u =>
      obtain ⟨R, hOp⟩ := hExists
      cases B with
      | int v =>
          simp [Raw.Ty.eval, Strictness.Ty.combine] at hOp
      | prod B₁ B₂ v =>
          simp [Raw.Ty.eval, Strictness.Ty.combine] at hOp
      | arrow B₁ B₂ v =>
          by_cases hDom : A₁.eval ν = B₁.eval ν
          · by_cases hCod : A₂.eval ν = B₂.eval ν
            · obtain ⟨C₁, hEqual₁, hSat₁⟩ :=
                equalTypes_complete hDom
              obtain ⟨C₂, hEqual₂, hSat₂⟩ :=
                equalTypes_complete hCod
              refine ⟨.arrow A₁ A₂ (op.expr u v), C₁ ++ C₂, ?_, ?_⟩
              · simp [Boundary.composeTy, hEqual₁, hEqual₂]
              · exact Raw.UseConstraints.satisfies_append.mpr
                  ⟨hSat₁, hSat₂⟩
            · simp [Raw.Ty.eval, Strictness.Ty.combine, hDom, hCod]
                at hOp
          · simp [Raw.Ty.eval, Strictness.Ty.combine, hDom] at hOp

theorem composeTy_complete
    {ν : Raw.Valuation}
    (op : Boundary.CombineOp)
    {A B : RTy} {R : Strictness.Ty}
    (hOp :
      Strictness.Ty.combine op.usage
        (A.eval ν) (B.eval ν) = some R) :
    ∃ D C,
      Boundary.composeTy op A B = some (D, C) ∧
      C.Satisfies ν ∧ D.eval ν = R := by
  obtain ⟨D, C, hCompose, hSat⟩ :=
    composeTy_exists_satisfied op ⟨R, hOp⟩
  have hEval := composeTy_sound op hCompose hSat
  have hResult : D.eval ν = R :=
    Option.some.inj (hEval.symm.trans hOp)
  exact ⟨D, C, hCompose, hSat, hResult⟩

private theorem composeEnv_exists_satisfied
    {ν : Raw.Valuation}
    (op : Boundary.CombineOp)
    {Γ Δ : REnv}
    (hExists :
      ∃ R, Strictness.Env.combine op.usage
        (Γ.eval ν) (Δ.eval ν) = some R) :
    ∃ E C,
      composeEnv op Γ Δ = some (E, C) ∧
      C.Satisfies ν := by
  induction Γ generalizing Δ with
  | nil =>
      obtain ⟨R, hOp⟩ := hExists
      cases Δ with
      | nil =>
          exact ⟨[], [], rfl, Raw.UseConstraints.satisfies_nil ν⟩
      | cons B Δ =>
          simp [Raw.Env.eval, Strictness.Env.combine] at hOp

  | cons A Γ ih =>
      obtain ⟨R, hOp⟩ := hExists
      cases Δ with
      | nil =>
          simp [Raw.Env.eval, Strictness.Env.combine] at hOp
      | cons B Δ =>
          cases hHead : Strictness.Ty.combine op.usage
              (A.eval ν) (B.eval ν) with
          | none =>
              simp [Raw.Env.eval, Strictness.Env.combine, hHead] at hOp
          | some RHead =>
                cases hTail : Strictness.Env.combine op.usage
                  (Raw.Env.eval ν Γ) (Raw.Env.eval ν Δ) with
              | none =>
                  simp [Raw.Env.eval, Strictness.Env.combine,
                    hHead, hTail] at hOp
              | some RTail =>
                  obtain ⟨D, CHead, hComposeHead, hSatHead, hEvalHead⟩ :=
                    composeTy_complete op hHead
                  obtain ⟨Ξ, CTail, hComposeTail, hSatTail⟩ :=
                    ih ⟨RTail, hTail⟩
                  refine ⟨D :: Ξ, CHead ++ CTail, ?_, ?_⟩
                  · simp [composeEnv, Boundary.composeEnv,
                      hComposeHead, hComposeTail]
                  · exact Raw.UseConstraints.satisfies_append.mpr
                      ⟨hSatHead, hSatTail⟩

theorem composeEnv_complete
    {ν : Raw.Valuation}
    (op : Boundary.CombineOp)
    {Γ Δ : REnv} {R : Strictness.Env}
    (hOp :
      Strictness.Env.combine op.usage
        (Γ.eval ν) (Δ.eval ν) = some R) :
    ∃ E C,
      composeEnv op Γ Δ = some (E, C) ∧
      C.Satisfies ν ∧ E.eval ν = R := by
  obtain ⟨E, C, hCompose, hSat⟩ :=
    composeEnv_exists_satisfied op ⟨R, hOp⟩
  have hEval := composeEnv_sound op hCompose hSat
  have hResult : E.eval ν = R :=
    Option.some.inj (hEval.symm.trans hOp)
  exact ⟨E, C, hCompose, hSat, hResult⟩

theorem subtype_trans
    {A B C : Strictness.Ty}
    (hAB : Strictness.Ty.Subtype A B)
    (hBC : Strictness.Ty.Subtype B C) :
    Strictness.Ty.Subtype A C := by
  induction B generalizing A C with
  | int u =>
      cases hAB with
      | int h₁ =>
          cases hBC with
          | int h₂ =>
              exact .int (Usage.le_trans h₁ h₂)
  | prod B₁ B₂ u ih₁ ih₂ =>
      cases hAB with
      | prod hA₁ hA₂ hU =>
          cases hBC with
          | prod hC₁ hC₂ hV =>
              exact .prod
                (ih₁ hA₁ hC₁)
                (ih₂ hA₂ hC₂)
                (Usage.le_trans hU hV)
  | arrow B₁ B₂ u ih₁ ih₂ =>
      cases hAB with
      | arrow hA₁ hA₂ hU =>
          cases hBC with
          | arrow hC₁ hC₂ hV =>
              exact .arrow
                (ih₁ hC₁ hA₁)
                (ih₂ hA₂ hC₂)
                (Usage.le_trans hU hV)

theorem envSubtype_trans
    {Γ Δ Θ : Strictness.Env}
    (hΓΔ : Strictness.Env.Subtype Γ Δ)
    (hΔΘ : Strictness.Env.Subtype Δ Θ) :
    Strictness.Env.Subtype Γ Θ := by
  induction Δ generalizing Γ Θ with
  | nil =>
      cases Γ with
      | nil =>
          cases Θ with
          | nil => trivial
          | cons C Θ => exact False.elim hΔΘ
      | cons A Γ =>
          exact False.elim hΓΔ
  | cons B Δ ih =>
      cases Γ with
      | nil =>
          exact False.elim hΓΔ
      | cons A Γ =>
          cases Θ with
          | nil =>
              exact False.elim hΔΘ
          | cons C Θ =>
              exact ⟨subtype_trans hΓΔ.1 hΔΘ.1,
                ih hΓΔ.2 hΔΘ.2⟩

/--
Replace only the root boundary.
Child derivations and the syntax-directed rule remain unchanged.
-/
theorem Derives.reboundary
    {ν : Raw.Valuation}
    {Γ Δ : REnv} {e : Term} {T T' : RTy} {C : UC}
    (d : Derives Γ e T C)
    (hSat : C.Satisfies ν)
    (hΔ : VariableEnv Δ)
    (hT' : VariableTy T')
    (hEnv :
      Strictness.Env.Subtype (Δ.eval ν) (Γ.eval ν))
    (hTy :
      Strictness.Ty.Subtype (T.eval ν) (T'.eval ν)) :
    ∃ C', Derives Δ e T' C' ∧ C'.Satisfies ν := by
  cases d with
  | node hRule hChildren hFinish =>
      rename_i ps E B CLocal CBoundary
      obtain ⟨hPremisesSat, hLocalSat, hBoundarySat⟩ :=
        node_constraints_satisfied hSat
      obtain ⟨hOldEnv, hOldTy⟩ :=
        finish_bounds hFinish hBoundarySat
      have hNewEnv :=
        envSubtype_trans hEnv hOldEnv
      have hNewTy :=
        subtype_trans hOldTy hTy
      obtain ⟨CNewBoundary, hNewFinish, hNewSat⟩ :=
        finish_exists hΔ hFinish.2.1 hT' hNewEnv hNewTy
      refine
        ⟨premiseConstraints ps ++ CLocal ++ CNewBoundary,
         Derives.node hRule hChildren hNewFinish, ?_⟩
      exact Raw.UseConstraints.satisfies_append.mpr
        ⟨Raw.UseConstraints.satisfies_append.mpr
           ⟨hPremisesSat, hLocalSat⟩,
         hNewSat⟩

end Strictness.RawInference.CoreBoundary
