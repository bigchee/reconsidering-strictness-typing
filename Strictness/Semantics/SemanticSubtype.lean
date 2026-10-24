import Strictness.Semantics.SemanticBasic
import Strictness.Language.Erasure

namespace Strictness

open Usage
open Term

/-- Subtyping preserves the recursive `Lazy` property contravariantly:
if the target type is Lazy, then so is the source type. -/
theorem subtype_isLazy :
    ∀ {σ τ : Ty}, Ty.Subtype σ τ → Ty.IsLazy τ → Ty.IsLazy σ
  | .int u, .int v, .int huv, h => by
      change v ≤ lazy at h
      change u ≤ lazy
      exact Usage.le_trans huv h
  | .prod σ₁ τ₁ u, .prod σ₂ τ₂ v, .prod hσ hτ huv, h => by
      rcases h with ⟨hv, hσLazy, hτLazy⟩
      refine ⟨Usage.le_trans huv hv, ?_, ?_⟩
      · exact subtype_isLazy hσ hσLazy
      · exact subtype_isLazy hτ hτLazy
  | .arrow σ₁ τ₁ u, .arrow σ₂ τ₂ v, .arrow hdom hcod huv, h => by
      change v ≤ lazy at h
      change u ≤ lazy
      exact Usage.le_trans huv h

theorem V_eq_allTerms_of_outer_le {τ : Ty}
    (hOuter : lazy ≤ τ.outer) :
    V τ = AllTerms τ.erase := by
  rw [V_def]
  exact LogicalModel.acceptable_eq_allTerms_of_outer_lazy
    operationalModel hOuter

theorem allTerms_reindex {σ τ : SimpleTy}
    (hστ : σ = τ) :
    TermSet.Subset (AllTerms σ) (AllTerms τ) := by
  intro e he
  rw [← hστ]
  exact he

theorem divergentTerms_reindex {σ τ : SimpleTy}
    (hστ : σ = τ) :
    TermSet.Subset (DivergentTerms σ) (DivergentTerms τ) := by
  intro e he
  rw [← hστ]
  exact he

theorem functionTerms_mono_reindex
    {σ σ' τ τ' : SimpleTy}
    {VX VX' DX DX' VY VY' DY DY' : TermSet Term}
    (hσ : σ = σ')
    (hτ : τ = τ')
    (hVX : TermSet.Subset VX' VX)
    (hDX : TermSet.Subset DX' DX)
    (hVY : TermSet.Subset VY VY')
    (hDY : TermSet.Subset DY DY') :
    TermSet.Subset
      (FunctionTerms σ τ VX DX VY DY)
      (FunctionTerms σ' τ' VX' DX' VY' DY') := by
  rw [← hσ, ← hτ]
  exact functionTerms_mono hVX hDX hVY hDY

theorem strictFunctionTerms_mono_reindex
    {σ σ' τ τ' : SimpleTy}
    {VArrow VArrow' VX VX' DY DY' : TermSet Term}
    (hσ : σ = σ')
    (hτ : τ = τ')
    (hVArrow : TermSet.Subset VArrow VArrow')
    (hVX : TermSet.Subset VX' VX)
    (hDY : TermSet.Subset DY DY') :
    TermSet.Subset
      (StrictFunctionTerms σ τ VArrow VX DY)
      (StrictFunctionTerms σ' τ' VArrow' VX' DY') := by
  rw [← hσ, ← hτ]
  exact strictFunctionTerms_mono hVArrow hVX hDY

/-- Monotonicity of the value set for strictly annotated arrow types. -/
theorem arrow_strict_V_mono
    {σ₁ σ₂ τ₁ τ₂ : Ty}
    (hdom : Ty.Subtype σ₂ σ₁)
    (hcod : Ty.Subtype τ₁ τ₂)
    (hVdom : TermSet.Subset (V σ₂) (V σ₁))
    (hDdom : TermSet.Subset (D σ₂) (D σ₁))
    (hVcod : TermSet.Subset (V τ₁) (V τ₂))
    (hDcod : TermSet.Subset (D τ₁) (D τ₂)) :
    TermSet.Subset
      (V (Ty.arrow σ₁ τ₁ strict))
      (V (Ty.arrow σ₂ τ₂ strict)) := by
  have hσerase : σ₁.erase = σ₂.erase :=
    (Ty.subtype_erase hdom).symm
  have hτerase : τ₁.erase = τ₂.erase :=
    Ty.subtype_erase hcod

  intro e he
  unfold V LogicalModel.acceptable operationalModel at he ⊢
  simp only [Usage.not_lazy_le_strict] at he ⊢

  rcases he with hdiv | hfun
  · exact Or.inl (divergentTerms_reindex
      (by rw [hσerase, hτerase]) hdiv)
  · exact Or.inr (functionTerms_mono_reindex
      hσerase hτerase
      hVdom hDdom hVcod hDcod
      hfun)


theorem semantic_subtype : ∀ {σ τ : Ty}, Ty.Subtype σ τ →
    TermSet.Subset (V σ) (V τ) ∧ TermSet.Subset (D σ) (D τ)
  | .int u, .int v, .int huv => by
      constructor
      · intro e he
        unfold V LogicalModel.acceptable operationalModel at he ⊢
        by_cases hu : lazy ≤ u
        · have hv : lazy ≤ v := Usage.le_trans hu huv
          simp only [hu, hv, if_pos] at he ⊢
          exact he
        · by_cases hv : lazy ≤ v
          · simp only [hu, hv, if_pos] at he ⊢
            rcases he with hdiv | hnum
            · exact hdiv.1
            · exact ⟨hnum.1, hnum.2.1⟩
          · simp only [hu, hv] at he ⊢
            exact he
      · intro e he
        cases u <;> cases v <;>
          simp [D, LogicalModel.divergentSide, operationalModel,
            Ty.IsLazy, Usage.Le] at he ⊢
        all_goals first
        | exact he
        | exact divergentTerms_subset_allTerms SimpleTy.int he
        | (change False at huv; exact huv.elim)
        | (change False at he; exact he.elim)
  | Ty.prod σ₁ τ₁ u, Ty.prod σ₂ τ₂ v,
      Ty.Subtype.prod hσ hτ huv => by
      have hσerase : σ₁.erase = σ₂.erase :=
        Ty.subtype_erase hσ
      have hτerase : τ₁.erase = τ₂.erase :=
        Ty.subtype_erase hτ

      rcases semantic_subtype hσ with ⟨hVσ, hDσ⟩
      rcases semantic_subtype hτ with ⟨hVτ, hDτ⟩

      constructor
      · intro e he

        by_cases huLazy : lazy ≤ u
        · rcases Usage.le_lazy_iff.mp huLazy with rfl | rfl
          · rcases Usage.le_lazy_iff.mp huv with rfl | rfl
            · rw [V_eq_allTerms_of_outer_lazy rfl] at he ⊢
              change AllTerms (σ₁.erase.prod τ₁.erase) e at he
              change AllTerms (σ₂.erase.prod τ₂.erase) e
              rw [← hσerase, ← hτerase]
              exact he
            · rw [V_eq_allTerms_of_outer_lazy rfl] at he
              rw [V_eq_allTerms_of_outer_top rfl]
              change AllTerms (σ₁.erase.prod τ₁.erase) e at he
              change AllTerms (σ₂.erase.prod τ₂.erase) e
              rw [← hσerase, ← hτerase]
              exact he
          · have hv : v = top := Usage.le_top_iff.mp huv
            subst v
            rw [V_eq_allTerms_of_outer_top rfl] at he ⊢
            change AllTerms (σ₁.erase.prod τ₁.erase) e at he
            change AllTerms (σ₂.erase.prod τ₂.erase) e
            rw [← hσerase, ← hτerase]
            exact he

        · have huOuter : ¬ lazy ≤ u := huLazy

          by_cases hvLazy : lazy ≤ v
          · rcases Usage.le_lazy_iff.mp hvLazy with rfl | rfl
            · rw [V_eq_allTerms_of_outer_lazy rfl]
              have heAll :
                  AllTerms (σ₁.erase.prod τ₁.erase) e :=
                V_subset_allTerms (Ty.prod σ₁ τ₁ u) he
              change AllTerms (σ₂.erase.prod τ₂.erase) e
              rw [← hσerase, ← hτerase]
              exact heAll
            · rw [V_eq_allTerms_of_outer_top rfl]
              have heAll :
                  AllTerms (σ₁.erase.prod τ₁.erase) e :=
                V_subset_allTerms (Ty.prod σ₁ τ₁ u) he
              change AllTerms (σ₂.erase.prod τ₂.erase) e
              rw [← hσerase, ← hτerase]
              exact heAll

          · unfold V LogicalModel.acceptable operationalModel at he ⊢
            simp only [huOuter, hvLazy] at he ⊢
            rcases he with hdiv | hpair
            · rw [← hσerase, ← hτerase]
              exact Or.inl hdiv
            · rw [← hσerase, ← hτerase]
              exact Or.inr (pairTerms_mono hVσ hVτ hpair)

      · intro e he

        by_cases hSourceLazy :
            Ty.IsLazy (Ty.prod σ₁ τ₁ u)
        · rw [lazy_implies_D_empty hSourceLazy] at he
          exact False.elim he

        · by_cases hTargetLazy :
            Ty.IsLazy (Ty.prod σ₂ τ₂ v)
          · have hSourceLazy' :
                Ty.IsLazy (Ty.prod σ₁ τ₁ u) :=
              subtype_isLazy
                (Ty.Subtype.prod hσ hτ huv)
                hTargetLazy
            rw [lazy_implies_D_empty hSourceLazy'] at he
            exact False.elim he

          · by_cases hvOuter : lazy ≤ v
            · rw [D_eq_allTerms_of_not_lazy hTargetLazy hvOuter]
              have heAll :
                  AllTerms (σ₁.erase.prod τ₁.erase) e :=
                D_subset_allTerms (Ty.prod σ₁ τ₁ u) he
              change AllTerms (σ₂.erase.prod τ₂.erase) e
              rw [← hσerase, ← hτerase]
              exact heAll

            · have huOuter : ¬ lazy ≤ u := by
                intro hu
                exact hvOuter (Usage.le_trans hu huv)

              have hVV :
                  TermSet.Subset
                    (PairTerms σ₁.erase τ₁.erase (V σ₁) (V τ₁))
                    (PairTerms σ₁.erase τ₁.erase (V σ₂) (V τ₂)) :=
                pairTerms_mono hVσ hVτ

              have hDV :
                  TermSet.Subset
                    (PairTerms σ₁.erase τ₁.erase (D σ₁) (V τ₁))
                    (PairTerms σ₁.erase τ₁.erase (D σ₂) (V τ₂)) :=
                pairTerms_mono hDσ hVτ

              have hVD :
                  TermSet.Subset
                    (PairTerms σ₁.erase τ₁.erase (V σ₁) (D τ₁))
                    (PairTerms σ₁.erase τ₁.erase (V σ₂) (D τ₂)) :=
                pairTerms_mono hVσ hDτ

              cases u with
              | unknown =>
                  cases v with
                  | unknown =>
                      unfold D LogicalModel.divergentSide operationalModel at he ⊢
                      simp only [hSourceLazy, hTargetLazy,
                        huOuter] at he ⊢
                      rcases he with hdiv | hpair
                      · rw [← hσerase, ← hτerase]
                        exact Or.inl hdiv
                      · rcases hpair with hpair | hpair
                        · rw [← hσerase, ← hτerase]
                          exact Or.inr (Or.inl (hDV hpair))
                        · rw [← hσerase, ← hτerase]
                          exact Or.inr (Or.inr (hVD hpair))

                  | strict =>
                      unfold D LogicalModel.divergentSide operationalModel at he ⊢
                      simp only [hSourceLazy, hTargetLazy,
                        huOuter, hvOuter] at he ⊢
                      rcases he with hdiv | hpair
                      · rw [← hσerase, ← hτerase]
                        exact Or.inl hdiv
                      · rcases hpair with hpair | hpair
                        · rw [← hσerase, ← hτerase]
                          exact Or.inr (Or.inl (hDV hpair))
                        · rw [← hσerase, ← hτerase]
                          exact Or.inr (Or.inr (hVD hpair))

                  | lazy =>
                      exact False.elim (hvOuter Usage.lazy_le_lazy)

                  | top =>
                      exact False.elim (hvOuter Usage.lazy_le_top)

              | strict =>
                  cases v with
                  | unknown =>
                      exact False.elim (by
                        change strict ≤ unknown at huv
                        exact huv)

                  | strict =>
                      unfold D LogicalModel.divergentSide operationalModel at he ⊢
                      simp only [hSourceLazy, hTargetLazy,
                        huOuter] at he ⊢
                      rcases he with hdiv | hpair
                      · rw [← hσerase, ← hτerase]
                        exact Or.inl hdiv
                      · rcases hpair with hpair | hpair
                        · rw [← hσerase, ← hτerase]
                          exact Or.inr (Or.inl (hDV hpair))
                        · rw [← hσerase, ← hτerase]
                          exact Or.inr (Or.inr (hVD hpair))

                  | lazy =>
                      exact False.elim (hvOuter Usage.lazy_le_lazy)

                  | top =>
                      exact False.elim (hvOuter Usage.lazy_le_top)

              | lazy =>
                  exact False.elim (huOuter Usage.lazy_le_lazy)

              | top =>
                  exact False.elim (huOuter Usage.lazy_le_top)
  | Ty.arrow σ₁ τ₁ u, Ty.arrow σ₂ τ₂ v,
      Ty.Subtype.arrow hdom hcod huv => by
      have hσerase : σ₁.erase = σ₂.erase :=
        (Ty.subtype_erase hdom).symm
      have hτerase : τ₁.erase = τ₂.erase :=
        Ty.subtype_erase hcod
      have hErase :
          (σ₁.erase.arrow τ₁.erase) =
          (σ₂.erase.arrow τ₂.erase) := by
        rw [hσerase, hτerase]

      rcases semantic_subtype hdom with ⟨hVdom, hDdom⟩
      rcases semantic_subtype hcod with ⟨hVcod, hDcod⟩

      constructor

      · intro e he

        by_cases huLazy : lazy ≤ u
        · have hvLazy : lazy ≤ v :=
            Usage.le_trans huLazy huv

          rw [V_eq_allTerms_of_outer_le
                (τ := Ty.arrow σ₁ τ₁ u) huLazy] at he
          rw [V_eq_allTerms_of_outer_le
                (τ := Ty.arrow σ₂ τ₂ v) hvLazy]

          exact allTerms_reindex hErase he

        · have huOuter : ¬ lazy ≤ u := huLazy

          by_cases hvLazy : lazy ≤ v
          · rw [V_eq_allTerms_of_outer_le
                  (τ := Ty.arrow σ₂ τ₂ v) hvLazy]

            have heAll :
                AllTerms (σ₁.erase.arrow τ₁.erase) e :=
              V_subset_allTerms (Ty.arrow σ₁ τ₁ u) he

            exact allTerms_reindex hErase heAll

          · unfold V LogicalModel.acceptable operationalModel at he ⊢
            simp only [huOuter, hvLazy] at he ⊢

            rcases he with hdiv | hfun

            · exact Or.inl
                (divergentTerms_reindex hErase hdiv)

            · exact Or.inr
                (functionTerms_mono_reindex
                  hσerase hτerase
                  hVdom hDdom hVcod hDcod
                  hfun)

      · intro e he

        by_cases hSourceLazy :
            Ty.IsLazy (Ty.arrow σ₁ τ₁ u)

        · rw [lazy_implies_D_empty hSourceLazy] at he
          exact False.elim he

        · by_cases hTargetLazy :
            Ty.IsLazy (Ty.arrow σ₂ τ₂ v)

          · have hSourceLazy' :
                Ty.IsLazy (Ty.arrow σ₁ τ₁ u) :=
              subtype_isLazy
                (Ty.Subtype.arrow hdom hcod huv)
                hTargetLazy

            rw [lazy_implies_D_empty hSourceLazy'] at he
            exact False.elim he

          · by_cases hvOuter : lazy ≤ v
            · rw [D_eq_allTerms_of_not_lazy
                    hTargetLazy hvOuter]

              have heAll :
                  AllTerms (σ₁.erase.arrow τ₁.erase) e :=
                D_subset_allTerms (Ty.arrow σ₁ τ₁ u) he

              exact allTerms_reindex hErase heAll

            · have huOuter : ¬ lazy ≤ u := by
                intro hu
                exact hvOuter (Usage.le_trans hu huv)

              cases u with

              | unknown =>
                  exact False.elim
                    (hSourceLazy (by
                      simp [Ty.IsLazy, Usage.Le]))

              | lazy =>
                  exact False.elim
                    (huOuter Usage.lazy_le_lazy)

              | top =>
                  exact False.elim
                    (huOuter Usage.lazy_le_top)

              | strict =>
                  have hvStrict : v = strict := by
                    rcases Usage.le_strict_iff.mp huv with rfl | rfl
                    · rfl
                    · exact False.elim
                        (hvOuter Usage.lazy_le_top)

                  subst v

                  have hVArrow :
                      TermSet.Subset
                        (V (Ty.arrow σ₁ τ₁ strict))
                        (V (Ty.arrow σ₂ τ₂ strict)) :=
                    arrow_strict_V_mono
                      hdom hcod
                      hVdom hDdom hVcod hDcod

                  unfold D LogicalModel.divergentSide operationalModel at he ⊢
                  simp only [
                    hSourceLazy,
                    hTargetLazy,
                    huOuter,
                  ] at he ⊢

                  rcases he with hdiv | hfun

                  · exact Or.inl
                      (divergentTerms_reindex hErase hdiv)

                  · exact Or.inr
                      (strictFunctionTerms_mono_reindex
                        hσerase hτerase
                        hVArrow hVdom hDcod
                        hfun)


/-- Structural subtyping is reflexive. -/
theorem subtype_refl : ∀ τ : Ty, Ty.Subtype τ τ
  | .int u =>
      Ty.Subtype.int (Usage.le_refl u)
  | .prod σ τ u =>
      Ty.Subtype.prod
        (subtype_refl σ)
        (subtype_refl τ)
        (Usage.le_refl u)
  | .arrow σ τ u =>
      Ty.Subtype.arrow
        (subtype_refl σ)
        (subtype_refl τ)
        (Usage.le_refl u)

/-- If combining two annotated types with `meet` succeeds,
    the result is a subtype of the left operand. -/
theorem combine_meet_subtype_left :
    ∀ {σ τ ρ : Ty},
      Ty.combine Usage.meet σ τ = some ρ →
        Ty.Subtype ρ σ := by
  intro σ τ ρ h
  induction σ generalizing τ ρ with
  | int u =>
      cases τ with
      | int v =>
          simp [Ty.combine] at h
          cases h
          exact Ty.Subtype.int (by
            cases u <;> cases v <;> trivial)
      | prod σ₂ τ₂ v =>
          simp [Ty.combine] at h
      | arrow σ₂ τ₂ v =>
          simp [Ty.combine] at h

  | prod σ₁ τ₁ u ihσ ihτ =>
      cases τ with
      | int v =>
          simp [Ty.combine] at h
      | prod σ₂ τ₂ v =>
          cases hσ : Ty.combine Usage.meet σ₁ σ₂ with
          | none =>
              simp [Ty.combine, hσ] at h
          | some σ' =>
              cases hτ : Ty.combine Usage.meet τ₁ τ₂ with
              | none =>
                  simp [Ty.combine, hσ, hτ] at h
              | some τ' =>
                  simp [Ty.combine, hσ, hτ] at h
                  cases h
                  exact Ty.Subtype.prod
                    (ihσ hσ)
                    (ihτ hτ)
                    (by
                      cases u <;> cases v <;> trivial)
      | arrow σ₂ τ₂ v =>
          simp [Ty.combine] at h

  | arrow σ₁ τ₁ u =>
      cases τ with
      | int v =>
          simp [Ty.combine] at h
      | prod σ₂ τ₂ v =>
          simp [Ty.combine] at h
      | arrow σ₂ τ₂ v =>
          by_cases hσ : σ₁ = σ₂
          · by_cases hτ : τ₁ = τ₂
            · simp [Ty.combine, hσ, hτ] at h
              cases h
              exact Ty.Subtype.arrow
                (by rw [← hσ]; exact subtype_refl σ₁)
                (by rw [← hτ]; exact subtype_refl τ₁)
                (by
                  cases u <;> cases v <;> trivial)
            · simp [Ty.combine, hσ, hτ] at h
          · simp [Ty.combine, hσ] at h

/-- The meet-combination type is a subtype of the left operand. -/
theorem cap_subtype_left :
    ∀ {σ τ ρ : Ty}, Ty.cap σ τ = some ρ → Ty.Subtype ρ σ := by
  intro σ τ ρ h
  exact combine_meet_subtype_left (by
    simpa [Ty.cap] using h)


theorem combine_meet_subtype_right :
    ∀ {σ τ ρ : Ty},
      Ty.combine Usage.meet σ τ = some ρ →
        Ty.Subtype ρ τ := by
  intro σ τ ρ h
  induction σ generalizing τ ρ with
  | int u =>
      cases τ with
      | int v =>
          simp [Ty.combine] at h
          cases h
          exact Ty.Subtype.int (by
            cases u <;> cases v <;> trivial)
      | prod σ₂ τ₂ v =>
          simp [Ty.combine] at h
      | arrow σ₂ τ₂ v =>
          simp [Ty.combine] at h

  | prod σ₁ τ₁ u ihσ ihτ =>
      cases τ with
      | int v =>
          simp [Ty.combine] at h
      | prod σ₂ τ₂ v =>
          cases hσ : Ty.combine Usage.meet σ₁ σ₂ with
          | none =>
              simp [Ty.combine, hσ] at h
          | some σ' =>
              cases hτ : Ty.combine Usage.meet τ₁ τ₂ with
              | none =>
                  simp [Ty.combine, hσ, hτ] at h
              | some τ' =>
                  simp [Ty.combine, hσ, hτ] at h
                  cases h
                  exact Ty.Subtype.prod
                    (ihσ hσ)
                    (ihτ hτ)
                    (by
                      cases u <;> cases v <;> trivial)
      | arrow σ₂ τ₂ v =>
          simp [Ty.combine] at h

  | arrow σ₁ τ₁ u =>
      cases τ with
      | int v =>
          simp [Ty.combine] at h
      | prod σ₂ τ₂ v =>
          simp [Ty.combine] at h
      | arrow σ₂ τ₂ v =>
          by_cases hσ : σ₁ = σ₂
          · by_cases hτ : τ₁ = τ₂
            · simp [Ty.combine, hσ, hτ] at h
              cases h
              exact Ty.Subtype.arrow
                (by
                  rw [← hσ]
                  exact subtype_refl σ₁)
                (by
                  rw [← hτ]
                  exact subtype_refl τ₁)
                (by
                  cases u <;> cases v <;> trivial)
            · simp [Ty.combine, hσ, hτ] at h
          · simp [Ty.combine, hσ] at h

theorem cap_subtype_right :
    ∀ {σ τ ρ : Ty}, Ty.cap σ τ = some ρ → Ty.Subtype ρ τ := by
  intro σ τ ρ h
  exact combine_meet_subtype_right (by
    simpa [Ty.cap] using h)

end Strictness
