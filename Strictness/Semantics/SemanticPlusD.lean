import Strictness.Semantics.SemanticPlus
import Strictness.Semantics.SemanticPairProjection

namespace Strictness

open Usage
open Term

/-- A D-component together with a V-component forms a D-pair under every
outer usage.  For `?` and `S` this follows from the corresponding pair branch;
for `L` a D-component witnesses non-Laziness of the whole product, making its
D-set the whole erased type; for `top` the D-set is the whole erased type. -/
theorem D_pair_left_intro_unconditional
    {σ τ : Ty} {u : Usage} {e₁ e₂ : Term}
    (hσ : D σ e₁) (hτ : V τ e₂) :
    D (.prod σ τ u) (.pair e₁ e₂) := by
  cases u with
  | unknown =>
      have hNotLazy : ¬ Ty.IsLazy (.prod σ τ unknown) := by
        intro hL
        rw [lazy_implies_D_empty hL.2.1] at hσ
        exact hσ
      unfold D LogicalModel.divergentSide operationalModel
      simp only [hNotLazy, Usage.not_lazy_le_unknown]
      exact Or.inr (Or.inl ⟨allTerms_pair (D_subset_allTerms σ hσ)
        (V_subset_allTerms τ hτ), e₁, e₂, Eval.pair, hσ, hτ⟩)
  | strict =>
      unfold D LogicalModel.divergentSide operationalModel
      simp [not_lazy_of_outer_strict (τ := .prod σ τ strict) rfl,
        Usage.Le]
      exact Or.inr (Or.inl ⟨allTerms_pair (D_subset_allTerms σ hσ)
        (V_subset_allTerms τ hτ), e₁, e₂, Eval.pair, hσ, hτ⟩)
  | lazy =>
      have hNotLazy : ¬ Ty.IsLazy (.prod σ τ lazy) := by
        intro hL
        rw [lazy_implies_D_empty hL.2.1] at hσ
        exact hσ
      rw [D_eq_allTerms_of_not_lazy hNotLazy Usage.lazy_le_lazy]
      exact allTerms_pair (D_subset_allTerms σ hσ) (V_subset_allTerms τ hτ)
  | top =>
      rw [D_eq_allTerms_of_outer_top rfl]
      exact allTerms_pair (D_subset_allTerms σ hσ) (V_subset_allTerms τ hτ)

/-- Symmetric version of `D_pair_left_intro_unconditional`. -/
theorem D_pair_right_intro_unconditional
    {σ τ : Ty} {u : Usage} {e₁ e₂ : Term}
    (hσ : V σ e₁) (hτ : D τ e₂) :
    D (.prod σ τ u) (.pair e₁ e₂) := by
  cases u with
  | unknown =>
      have hNotLazy : ¬ Ty.IsLazy (.prod σ τ unknown) := by
        intro hL
        rw [lazy_implies_D_empty hL.2.2] at hτ
        exact hτ
      unfold D LogicalModel.divergentSide operationalModel
      simp only [hNotLazy, Usage.not_lazy_le_unknown]
      exact Or.inr (Or.inr ⟨allTerms_pair (V_subset_allTerms σ hσ)
        (D_subset_allTerms τ hτ), e₁, e₂, Eval.pair, hσ, hτ⟩)
  | strict =>
      unfold D LogicalModel.divergentSide operationalModel
      simp [not_lazy_of_outer_strict (τ := .prod σ τ strict) rfl,
        Usage.Le]
      exact Or.inr (Or.inr ⟨allTerms_pair (V_subset_allTerms σ hσ)
        (D_subset_allTerms τ hτ), e₁, e₂, Eval.pair, hσ, hτ⟩)
  | lazy =>
      have hNotLazy : ¬ Ty.IsLazy (.prod σ τ lazy) := by
        intro hL
        rw [lazy_implies_D_empty hL.2.2] at hτ
        exact hτ
      rw [D_eq_allTerms_of_not_lazy hNotLazy Usage.lazy_le_lazy]
      exact allTerms_pair (V_subset_allTerms σ hσ) (D_subset_allTerms τ hτ)
  | top =>
      rw [D_eq_allTerms_of_outer_top rfl]
      exact allTerms_pair (V_subset_allTerms σ hσ) (D_subset_allTerms τ hτ)

/-- An evaluation to a retained pair is observationally equivalent to the
pair term itself. -/
theorem semEq_of_eval_pair {σ τ : SimpleTy} {e e₁ e₂ : Term}
    (hAll : AllTerms (.prod σ τ) e)
    (hPair : AllTerms (.prod σ τ) (.pair e₁ e₂))
    (hev : Eval e (.pair e₁ e₂)) :
    SemEq (.prod σ τ) e (.pair e₁ e₂) := by
  refine ⟨hAll, hPair, ?_⟩
  constructor
  · intro v
    constructor
    · intro hEval
      have hValue : v = .pair e₁ e₂ := eval_deterministic hEval hev
      cases hValue
      exact Eval.pair
    · intro hEval
      cases hEval
      exact hev
  · constructor
    · intro hErr
      exact False.elim (eval_not_evalErr hev hErr)
    · intro hErr
      exact False.elim (eval_not_evalErr Eval.pair hErr)

theorem D_pair_left_of_eval {σ τ : Ty} {u : Usage} {e e₁ e₂ : Term}
    (hAll : AllTerms (.prod σ.erase τ.erase) e)
    (hev : Eval e (.pair e₁ e₂))
    (hσ : D σ e₁) (hτ : V τ e₂) :
    D (.prod σ τ u) e := by
  have hPairAll : AllTerms (.prod σ.erase τ.erase) (.pair e₁ e₂) :=
    allTerms_pair (D_subset_allTerms σ hσ) (V_subset_allTerms τ hτ)
  have hEq := semEq_of_eval_pair hAll hPairAll hev
  exact (semantic_equiv_VD (τ := .prod σ τ u) hEq).2.mpr
    (D_pair_left_intro_unconditional (u := u) hσ hτ)

theorem D_pair_right_of_eval {σ τ : Ty} {u : Usage} {e e₁ e₂ : Term}
    (hAll : AllTerms (.prod σ.erase τ.erase) e)
    (hev : Eval e (.pair e₁ e₂))
    (hσ : V σ e₁) (hτ : D τ e₂) :
    D (.prod σ τ u) e := by
  have hPairAll : AllTerms (.prod σ.erase τ.erase) (.pair e₁ e₂) :=
    allTerms_pair (V_subset_allTerms σ hσ) (D_subset_allTerms τ hτ)
  have hEq := semEq_of_eval_pair hAll hPairAll hev
  exact (semantic_equiv_VD (τ := .prod σ τ u) hEq).2.mpr
    (D_pair_right_intro_unconditional (u := u) hσ hτ)
/-- If the result of a type `+` is not Lazy, at least one input is not Lazy.
This is the contrapositive of the structural preservation of Laziness. -/
theorem not_lazy_input_of_plus_not_lazy
    {σ τ ρ : Ty} (hplus : Ty.plus σ τ = some ρ)
    (hρ : ¬ Ty.IsLazy ρ) :
    ¬ Ty.IsLazy σ ∨ ¬ Ty.IsLazy τ := by
  by_cases hσ : Ty.IsLazy σ
  · right
    intro hτ
    exact hρ (plus_lazy_of_lazy hplus hσ hτ)
  · exact Or.inl hσ

/-- A divergent result of a non-Lazy `+` combination is inherited by at least
one of the two input D-sets. -/
theorem divergent_plus_D_split
    {σ τ ρ : Ty} (hplus : Ty.plus σ τ = some ρ)
    (hρ : ¬ Ty.IsLazy ρ) :
    TermSet.Subset (DivergentTerms ρ.erase)
      (TermSet.union (D σ) (D τ)) := by
  rcases not_lazy_input_of_plus_not_lazy hplus hρ with hσ | hτ
  · have hEq := Ty.combine_erase_of_some Usage.add hplus
    intro e he
    exact Or.inl (divergentTerms_subset_D_of_not_lazy hσ (by
      simpa [hEq.2] using he))
  · have hEq := Ty.combine_erase_of_some Usage.add hplus
    intro e he
    exact Or.inr (divergentTerms_subset_D_of_not_lazy hτ (by
      simpa [hEq.2, hEq.1] using he))

/-- D-side semantic containment for `+`.

The proof is by structural induction on successful pointwise composition.
Products recurse on their component combinations.  For arrows, type addition `+`
operation requires the domain and codomain types to agree exactly, so the
strict-function part is shared by the result and any strict operand. -/
theorem semantic_plus_D :
    ∀ {σ τ ρ : Ty}, Ty.plus σ τ = some ρ →
      TermSet.Subset (D ρ) (TermSet.union (D σ) (D τ))
  | .int u, .int v, .int w, h => by
      simp [Ty.plus, Ty.combine] at h
      subst w
      intro e he
      cases u <;> cases v
      all_goals
        simp [Usage.add, D, LogicalModel.divergentSide,
          operationalModel, Ty.IsLazy, Usage.Le, TermSet.union] at he ⊢
      · exact False.elim he
      · exact Or.inr (by simpa using he)
      · exact False.elim he
      · exact Or.inr (divergentTerms_subset_allTerms .int he)
      · exact Or.inl he
      · exact he
      · exact Or.inl (by simpa using he)
      · exact Or.inl (by simpa using he)
      · exact False.elim he
      · exact Or.inr (by simpa using he)
      · exact False.elim he
      · exact Or.inr he
      · exact Or.inl (divergentTerms_subset_allTerms .int he)
      · exact Or.inl (divergentTerms_subset_allTerms .int he)
      · exact Or.inl he
      · exact he
  | .prod σ₁ τ₁ u, .prod σ₂ τ₂ v, .prod ρ₁ ρ₂ w, h => by
      cases hσ : Ty.combine Usage.add σ₁ σ₂ with
      | none => simp [Ty.plus, Ty.combine, hσ] at h
      | some σ' =>
          cases hτ : Ty.combine Usage.add τ₁ τ₂ with
          | none => simp [Ty.plus, Ty.combine, hσ, hτ] at h
          | some τ' =>
              simp [Ty.plus, Ty.combine, hσ, hτ] at h
              rcases h with ⟨hσρ, hτρ, hUsage⟩
              subst σ'
              subst τ'
              subst w
              have hWhole :
                  Ty.plus (.prod σ₁ τ₁ u) (.prod σ₂ τ₂ v) =
                    some (.prod ρ₁ ρ₂ (Usage.add u v)) := by
                simp [Ty.plus, Ty.combine, hσ, hτ]
              have ihσ := semantic_plus_D hσ
              have ihτ := semantic_plus_D hτ
              have ihVσ := semantic_plus_V hσ
              have ihVτ := semantic_plus_V hτ
              have hEraseLeft := Ty.combine_erase_of_some Usage.add hσ
              have hEraseRight := Ty.combine_erase_of_some Usage.add hτ
              have hErasePairLeft :
                  ρ₁.erase.prod ρ₂.erase = σ₁.erase.prod τ₁.erase := by
                rw [hEraseLeft.2, hEraseRight.2]
              have hErasePairRight :
                  ρ₁.erase.prod ρ₂.erase = σ₂.erase.prod τ₂.erase := by
                rw [hEraseLeft.2, hEraseRight.2,
                  hEraseLeft.1, hEraseRight.1]
              cases hSum : Usage.add u v with
              | unknown =>
                  intro e he
                  by_cases hLazyR : Ty.IsLazy (.prod ρ₁ ρ₂ unknown)
                  · rw [lazy_implies_D_empty hLazyR] at he
                    exact False.elim he
                  · unfold D LogicalModel.divergentSide operationalModel at he
                    simp only [hLazyR, Usage.not_lazy_le_unknown] at he
                    have hNotLazyR : ¬ Ty.IsLazy (.prod ρ₁ ρ₂ unknown) := hLazyR
                    rcases he with hdiv | hpair
                    · exact divergent_plus_D_split hWhole
                        (by simpa [hSum] using hNotLazyR) hdiv
                    · rcases hpair with hleft | hright
                      · rcases hleft with ⟨hAll, e₁, e₂, hev, hD₁, hV₂⟩
                        rcases ihσ hD₁ with hD₁L | hD₁R
                        · exact Or.inl (D_pair_left_of_eval (u := u)
                            (by simpa [hEraseLeft.2, hEraseRight.2] using hAll) hev hD₁L
                            (ihVτ.1 hV₂))
                        · exact Or.inr (D_pair_left_of_eval (u := v)
                            (by simpa [hEraseLeft.2, hEraseRight.2,
                              hEraseLeft.1, hEraseRight.1] using hAll) hev hD₁R
                            (ihVτ.2 hV₂))
                      · rcases hright with ⟨hAll, e₁, e₂, hev, hV₁, hD₂⟩
                        rcases ihτ hD₂ with hD₂L | hD₂R
                        · exact Or.inl (D_pair_right_of_eval (u := u)
                            (by simpa [hEraseLeft.2, hEraseRight.2] using hAll) hev
                            (ihVσ.1 hV₁) hD₂L)
                        · exact Or.inr (D_pair_right_of_eval (u := v)
                            (by simpa [hEraseLeft.2, hEraseRight.2,
                              hEraseLeft.1, hEraseRight.1] using hAll) hev
                            (ihVσ.2 hV₁) hD₂R)
              | strict =>
                  intro e he
                  unfold D LogicalModel.divergentSide operationalModel at he
                  have hNotLazyR : ¬ Ty.IsLazy (.prod ρ₁ ρ₂ strict) :=
                    not_lazy_of_outer_strict rfl
                  simp [hNotLazyR, Usage.Le] at he
                  rcases he with hdiv | hpair
                  · exact divergent_plus_D_split hWhole
                      (by simpa [hSum] using hNotLazyR) hdiv
                  · rcases hpair with hleft | hright
                    · rcases hleft with ⟨hAll, e₁, e₂, hev, hD₁, hV₂⟩
                      rcases ihσ hD₁ with hD₁L | hD₁R
                      · exact Or.inl (D_pair_left_of_eval (u := u)
                          (by simpa [hEraseLeft.2, hEraseRight.2] using hAll) hev hD₁L
                          (ihVτ.1 hV₂))
                      · exact Or.inr (D_pair_left_of_eval (u := v)
                          (by simpa [hEraseLeft.2, hEraseRight.2,
                            hEraseLeft.1, hEraseRight.1] using hAll) hev hD₁R
                          (ihVτ.2 hV₂))
                    · rcases hright with ⟨hAll, e₁, e₂, hev, hV₁, hD₂⟩
                      rcases ihτ hD₂ with hD₂L | hD₂R
                      · exact Or.inl (D_pair_right_of_eval (u := u)
                          (by simpa [hEraseLeft.2, hEraseRight.2] using hAll) hev
                          (ihVσ.1 hV₁) hD₂L)
                      · exact Or.inr (D_pair_right_of_eval (u := v)
                          (by simpa [hEraseLeft.2, hEraseRight.2,
                            hEraseLeft.1, hEraseRight.1] using hAll) hev
                          (ihVσ.2 hV₁) hD₂R)
              | lazy =>
                  have huv : u = lazy ∧ v = lazy :=
                    Usage.add_eq_lazy_implies_both_lazy hSum
                  rcases huv with ⟨rfl, rfl⟩
                  intro e he
                  have hNotLazyR : ¬ Ty.IsLazy (.prod ρ₁ ρ₂ lazy) := by
                    intro hL
                    rw [lazy_implies_D_empty hL] at he
                    exact he
                  have hInput :
                      ¬ Ty.IsLazy (.prod σ₁ τ₁ lazy) ∨
                      ¬ Ty.IsLazy (.prod σ₂ τ₂ lazy) :=
                    not_lazy_input_of_plus_not_lazy hWhole hNotLazyR
                  have hErase := Ty.combine_erase_of_some Usage.add hWhole
                  rw [D_eq_allTerms_of_not_lazy hNotLazyR
                    Usage.lazy_le_lazy] at he
                  rcases hInput with hLeft | hRight
                  · apply Or.inl
                    rw [D_eq_allTerms_of_not_lazy hLeft
                      Usage.lazy_le_lazy]
                    change AllTerms (σ₁.erase.prod τ₁.erase) e
                    rw [← hErasePairLeft]
                    exact he
                  · apply Or.inr
                    rw [D_eq_allTerms_of_not_lazy hRight
                      Usage.lazy_le_lazy]
                    change AllTerms (σ₂.erase.prod τ₂.erase) e
                    rw [← hErasePairRight]
                    exact he
              | top =>
                  have hTop : u = top ∨ v = top :=
                    Usage.add_eq_top_implies_top_left_or_right hSum
                  intro e he
                  have hErase := Ty.combine_erase_of_some Usage.add hWhole
                  rw [D_eq_allTerms_of_outer_top rfl] at he
                  rcases hTop with hLeft | hRight
                  · subst u
                    apply Or.inl
                    rw [D_eq_allTerms_of_outer_top rfl]
                    change AllTerms (σ₁.erase.prod τ₁.erase) e
                    rw [← hErasePairLeft]
                    exact he
                  · subst v
                    apply Or.inr
                    rw [D_eq_allTerms_of_outer_top rfl]
                    change AllTerms (σ₂.erase.prod τ₂.erase) e
                    rw [← hErasePairRight]
                    exact he
  | .arrow σ₁ τ₁ u, .arrow σ₂ τ₂ v, .arrow ρ₁ ρ₂ w, h => by
      simp [Ty.plus, Ty.combine] at h
      rcases h with ⟨hσ, hτ, hσρ, hτρ, hUsage⟩
      subst σ₂
      subst τ₂
      subst ρ₁
      subst ρ₂
      subst w
      have hWhole :
          Ty.plus (.arrow σ₁ τ₁ u) (.arrow σ₁ τ₁ v) =
            some (.arrow σ₁ τ₁ (Usage.add u v)) := by
        simp [Ty.plus, Ty.combine]
      cases hSum : Usage.add u v with
      | unknown =>
          intro e he
          have hL : Ty.IsLazy (.arrow σ₁ τ₁ unknown) := by
            change Usage.Le unknown lazy
            trivial
          rw [lazy_implies_D_empty hL] at he
          exact False.elim he
      | lazy =>
          intro e he
          have hL : Ty.IsLazy (.arrow σ₁ τ₁ lazy) := by
            change Usage.Le lazy lazy
            exact Usage.le_refl lazy
          rw [lazy_implies_D_empty hL] at he
          exact False.elim he
      | top =>
          intro e he
          rw [D_eq_allTerms_of_outer_top rfl] at he
          have hTop : u = top ∨ v = top :=
            Usage.add_eq_top_implies_top_left_or_right hSum
          rcases hTop with hLeft | hRight
          · subst u
            apply Or.inl
            rw [D_eq_allTerms_of_outer_top rfl]
            exact he
          · subst v
            apply Or.inr
            rw [D_eq_allTerms_of_outer_top rfl]
            exact he
      | strict =>
          intro e he
          unfold D LogicalModel.divergentSide operationalModel at he
          have hNotLazy : ¬ Ty.IsLazy (.arrow σ₁ τ₁ strict) :=
            not_lazy_of_outer_strict rfl
          simp [hNotLazy, Usage.Le] at he
          rcases he with hdiv | hStrict
          · exact divergent_plus_D_split hWhole
              (by simpa [hSum] using hNotLazy) hdiv
          · have hChoice : u = strict ∨ u = top ∨ v = strict ∨ v = top :=
              Usage.add_eq_strict_implies_strict_or_top hSum
            rcases hChoice with hLeftS | hLeftT | hRightS | hRightT
            · subst u
              apply Or.inl
              unfold D LogicalModel.divergentSide operationalModel
              simp [not_lazy_of_outer_strict (τ := .arrow σ₁ τ₁ strict) rfl,
                Usage.Le]
              exact Or.inr hStrict
            · subst u
              apply Or.inl
              rw [D_eq_allTerms_of_outer_top rfl]
              exact V_subset_allTerms (.arrow σ₁ τ₁ strict) hStrict.1
            · subst v
              apply Or.inr
              unfold D LogicalModel.divergentSide operationalModel
              simp [not_lazy_of_outer_strict (τ := .arrow σ₁ τ₁ strict) rfl,
                Usage.Le]
              exact Or.inr hStrict
            · subst v
              apply Or.inr
              rw [D_eq_allTerms_of_outer_top rfl]
              exact V_subset_allTerms (.arrow σ₁ τ₁ strict) hStrict.1
  | .int _, .prod _ _ _, _, h => by simp [Ty.plus, Ty.combine] at h
  | .int _, .arrow _ _ _, _, h => by simp [Ty.plus, Ty.combine] at h
  | .prod _ _ _, .int _, _, h => by simp [Ty.plus, Ty.combine] at h
  | .prod _ _ _, .arrow _ _ _, _, h => by simp [Ty.plus, Ty.combine] at h
  | .arrow _ _ _, .int _, _, h => by simp [Ty.plus, Ty.combine] at h
  | .arrow _ _ _, .prod _ _ _, _, h => by simp [Ty.plus, Ty.combine] at h
  | .int _, .int _, .prod _ _ _, h => by simp [Ty.plus, Ty.combine] at h
  | .int _, .int _, .arrow _ _ _, h => by simp [Ty.plus, Ty.combine] at h
  | .prod σ₁ τ₁ u, .prod σ₂ τ₂ v, .int _, h => by
      cases hσ : Ty.combine Usage.add σ₁ σ₂ <;>
        cases hτ : Ty.combine Usage.add τ₁ τ₂ <;>
        simp [Ty.plus, Ty.combine, hσ, hτ] at h
  | .prod σ₁ τ₁ u, .prod σ₂ τ₂ v, .arrow _ _ _, h => by
      cases hσ : Ty.combine Usage.add σ₁ σ₂ <;>
        cases hτ : Ty.combine Usage.add τ₁ τ₂ <;>
        simp [Ty.plus, Ty.combine, hσ, hτ] at h
  | .arrow _ _ _, .arrow _ _ _, .int _, h => by
      simp [Ty.plus, Ty.combine] at h
  | .arrow _ _ _, .arrow _ _ _, .prod _ _ _, h => by
      simp [Ty.plus, Ty.combine] at h

end Strictness
