import Strictness.Semantics.SemanticPairProjection
import Strictness.Semantics.SemanticCap

namespace Strictness

open Usage
open Term

/-- A successful `+` combination of two Lazy types is Lazy.  This is the
structural fact needed when the resulting outer usage is `L` but the result
itself might still be non-Lazy because of a product component. -/
theorem plus_lazy_of_lazy :
    ∀ {σ τ ρ : Ty}, Ty.plus σ τ = some ρ →
      Ty.IsLazy σ → Ty.IsLazy τ → Ty.IsLazy ρ
  | .int u, .int v, .int w, h, hu, hv => by
      simp [Ty.plus, Ty.combine] at h
      subst w
      cases u <;> cases v <;>
        simp_all [Ty.IsLazy, Usage.add, Usage.Le]
  | .prod σ₁ τ₁ u, .prod σ₂ τ₂ v, .prod ρ₁ ρ₂ w, h, hu, hv => by
      cases hσ : Ty.combine Usage.add σ₁ σ₂ with
      | none => simp [Ty.plus, Ty.combine, hσ] at h
      | some σ' =>
          cases hτ : Ty.combine Usage.add τ₁ τ₂ with
          | none => simp [Ty.plus, Ty.combine, hσ, hτ] at h
          | some τ' =>
              simp [Ty.plus, Ty.combine, hσ, hτ] at h
              rcases h with ⟨hσρ, hτρ, hUsage⟩
              subst ρ₁
              subst ρ₂
              subst w
              rcases hu with ⟨hu, hσL, hτL⟩
              rcases hv with ⟨hv, hσR, hτR⟩
              refine ⟨?_, plus_lazy_of_lazy hσ hσL hσR,
                plus_lazy_of_lazy hτ hτL hτR⟩
              cases u <;> cases v <;>
                simp_all [Usage.add, Usage.Le]
  | .arrow σ₁ τ₁ u, .arrow σ₂ τ₂ v, .arrow ρ₁ ρ₂ w, h, hu, hv => by
      simp [Ty.plus, Ty.combine] at h
      rcases h with ⟨hσ, hτ, hσρ, hτρ, hUsage⟩
      subst σ₂
      subst τ₂
      subst ρ₁
      subst ρ₂
      subst w
      cases u <;> cases v <;>
        simp_all [Ty.IsLazy, Usage.add, Usage.Le]
  | .int _, .prod _ _ _, _, h, _, _ => by simp [Ty.plus, Ty.combine] at h
  | .int _, .arrow _ _ _, _, h, _, _ => by simp [Ty.plus, Ty.combine] at h
  | .prod _ _ _, .int _, _, h, _, _ => by simp [Ty.plus, Ty.combine] at h
  | .prod _ _ _, .arrow _ _ _, _, h, _, _ => by simp [Ty.plus, Ty.combine] at h
  | .arrow _ _ _, .int _, _, h, _, _ => by simp [Ty.plus, Ty.combine] at h
  | .arrow _ _ _, .prod _ _ _, _, h, _, _ => by simp [Ty.plus, Ty.combine] at h
  | .int _, .int _, .prod _ _ _, h, _, _ => by simp [Ty.plus, Ty.combine] at h
  | .int _, .int _, .arrow _ _ _, h, _, _ => by simp [Ty.plus, Ty.combine] at h
  | .prod σ₁ τ₁ u, .prod σ₂ τ₂ v, .int _, h, _, _ => by
      cases hσ : Ty.combine Usage.add σ₁ σ₂ <;>
        cases hτ : Ty.combine Usage.add τ₁ τ₂ <;>
        simp [Ty.plus, Ty.combine, hσ, hτ] at h
  | .prod σ₁ τ₁ u, .prod σ₂ τ₂ v, .arrow _ _ _, h, _, _ => by
      cases hσ : Ty.combine Usage.add σ₁ σ₂ <;>
        cases hτ : Ty.combine Usage.add τ₁ τ₂ <;>
        simp [Ty.plus, Ty.combine, hσ, hτ] at h
  | .arrow _ _ _, .arrow _ _ _, .int _, h, _, _ => by
      simp [Ty.plus, Ty.combine] at h
  | .arrow _ _ _, .arrow _ _ _, .prod _ _ _, h, _, _ => by
      simp [Ty.plus, Ty.combine] at h

/-- Transfer a V-member to a target type whose outer usage is lazy or top,
when the erased simple types agree. -/
theorem V_transfer_to_lazy_top {σ τ : Ty} {e : Term}
    (hErase : σ.erase = τ.erase)
    (hTarget : τ.outer = lazy ∨ τ.outer = top)
    (he : V σ e) : V τ e := by
  have hAll : AllTerms σ.erase e := V_subset_allTerms σ he
  rcases hTarget with hLazy | hTop
  · rw [V_eq_allTerms_of_outer_lazy hLazy]
    simpa [hErase] using hAll
  · rw [V_eq_allTerms_of_outer_top hTop]
    simpa [hErase] using hAll

/-- V-side plus soundness, for the value-side interpretation. -/
theorem semantic_plus_V :
    ∀ {σ τ ρ : Ty}, Ty.plus σ τ = some ρ →
      TermSet.Subset (V ρ) (V σ) ∧
      TermSet.Subset (V ρ) (V τ)
  | .int u, .int v, .int w, h => by
      simp [Ty.plus, Ty.combine] at h
      subst w
      constructor <;> intro e he
      · cases u with
        | unknown =>
            cases v <;> simpa [V, LogicalModel.acceptable,
              Usage.add, Usage.Le] using he
        | strict =>
            cases v <;> simpa [V, LogicalModel.acceptable,
              Usage.add, Usage.Le] using he
        | lazy =>
            exact V_transfer_to_lazy_top
              (σ := .int (Usage.add lazy v)) (τ := .int lazy)
              rfl (Or.inl rfl) he
        | top =>
            exact V_transfer_to_lazy_top
              (σ := .int (Usage.add top v)) (τ := .int top)
              rfl (Or.inr rfl) he
      · cases v with
        | unknown =>
            cases u <;> simpa [V, LogicalModel.acceptable,
              Usage.add, Usage.Le] using he
        | strict =>
            cases u <;> simpa [V, LogicalModel.acceptable,
              Usage.add, Usage.Le] using he
        | lazy =>
            exact V_transfer_to_lazy_top
              (σ := .int (Usage.add u lazy)) (τ := .int lazy)
              rfl (Or.inl rfl) he
        | top =>
            exact V_transfer_to_lazy_top
              (σ := .int (Usage.add u top)) (τ := .int top)
              rfl (Or.inr rfl) he
  | .arrow σ₁ τ₁ u, .arrow σ₂ τ₂ v, .arrow ρ₁ ρ₂ w, h => by
      simp [Ty.plus, Ty.combine] at h
      rcases h with ⟨hσ, hτ, hσρ, hτρ, hUsage⟩
      subst σ₂
      subst τ₂
      subst ρ₁
      subst ρ₂
      subst w
      constructor <;> intro e he
      · cases u with
        | unknown =>
            cases v <;> simpa [V, LogicalModel.acceptable,
              Usage.add, Usage.Le] using he
        | strict =>
            cases v <;> simpa [V, LogicalModel.acceptable,
              Usage.add, Usage.Le] using he
        | lazy =>
            exact V_transfer_to_lazy_top
              (σ := .arrow σ₁ τ₁ (Usage.add lazy v))
              (τ := .arrow σ₁ τ₁ lazy) rfl (Or.inl rfl) he
        | top =>
            exact V_transfer_to_lazy_top
              (σ := .arrow σ₁ τ₁ (Usage.add top v))
              (τ := .arrow σ₁ τ₁ top) rfl (Or.inr rfl) he
      · cases v with
        | unknown =>
            cases u <;> simpa [V, LogicalModel.acceptable,
              Usage.add, Usage.Le] using he
        | strict =>
            cases u <;> simpa [V, LogicalModel.acceptable,
              Usage.add, Usage.Le] using he
        | lazy =>
            exact V_transfer_to_lazy_top
              (σ := .arrow σ₁ τ₁ (Usage.add u lazy))
              (τ := .arrow σ₁ τ₁ lazy) rfl (Or.inl rfl) he
        | top =>
            exact V_transfer_to_lazy_top
              (σ := .arrow σ₁ τ₁ (Usage.add u top))
              (τ := .arrow σ₁ τ₁ top) rfl (Or.inr rfl) he
  | .prod σ₁ τ₁ u, .prod σ₂ τ₂ v, .prod ρ₁ ρ₂ w, h => by
      cases hσ : Ty.combine Usage.add σ₁ σ₂ with
      | none => simp [Ty.plus, Ty.combine, hσ] at h
      | some σ' =>
          cases hτ : Ty.combine Usage.add τ₁ τ₂ with
          | none => simp [Ty.plus, Ty.combine, hσ, hτ] at h
          | some τ' =>
              simp [Ty.plus, Ty.combine, hσ, hτ] at h
              rcases h with ⟨hσρ, hτρ, hUsage⟩
              subst ρ₁
              subst ρ₂
              subst w
              have ihσ := semantic_plus_V hσ
              have ihτ := semantic_plus_V hτ
              have hEraseLeft := Ty.combine_erase_of_some Usage.add hσ
              have hEraseRight := Ty.combine_erase_of_some Usage.add hτ
              have hVPairLeft :
                  TermSet.Subset
                    (PairTerms σ'.erase τ'.erase (V σ') (V τ'))
                    (PairTerms σ₁.erase τ₁.erase (V σ₁) (V τ₁)) := by
                rw [hEraseLeft.2, hEraseRight.2]
                exact pairTerms_mono ihσ.1 ihτ.1
              have hVPairRight :
                  TermSet.Subset
                    (PairTerms σ'.erase τ'.erase (V σ') (V τ'))
                    (PairTerms σ₂.erase τ₂.erase (V σ₂) (V τ₂)) := by
                rw [hEraseLeft.2, hEraseRight.2,
                  hEraseLeft.1, hEraseRight.1]
                exact pairTerms_mono ihσ.2 ihτ.2
              have hWholeLeft :
                  (Ty.prod σ' τ' (Usage.add u v)).erase =
                    (Ty.prod σ₁ τ₁ u).erase := by
                simp only [Ty.erase]
                rw [hEraseLeft.2, hEraseRight.2]
              have hWholeRight :
                  (Ty.prod σ' τ' (Usage.add u v)).erase =
                    (Ty.prod σ₂ τ₂ v).erase := by
                simp only [Ty.erase]
                rw [hEraseLeft.2, hEraseRight.2, hEraseLeft.1, hEraseRight.1]
              constructor
              · intro e he
                cases u with
                | lazy =>
                    exact V_transfer_to_lazy_top hWholeLeft (Or.inl rfl) he
                | top =>
                    exact V_transfer_to_lazy_top hWholeLeft (Or.inr rfl) he
                | unknown | strict =>
                    cases v <;>
                      (unfold V LogicalModel.acceptable operationalModel at he ⊢
                       simp [Usage.add, Usage.Le] at he ⊢
                       rcases he with hdiv | hpair
                       · exact Or.inl (by
                           simpa [hEraseLeft.2, hEraseRight.2] using hdiv)
                       · exact Or.inr (hVPairLeft hpair))
              · intro e he
                cases v with
                | lazy =>
                    exact V_transfer_to_lazy_top hWholeRight (Or.inl rfl) he
                | top =>
                    exact V_transfer_to_lazy_top hWholeRight (Or.inr rfl) he
                | unknown | strict =>
                    cases u <;>
                      (unfold V LogicalModel.acceptable operationalModel at he ⊢
                       simp [Usage.add, Usage.Le] at he ⊢
                       rcases he with hdiv | hpair
                       · exact Or.inl (by
                           simpa [hEraseLeft.2, hEraseRight.2,
                             hEraseLeft.1, hEraseRight.1] using hdiv)
                       · exact Or.inr (hVPairRight hpair))
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
