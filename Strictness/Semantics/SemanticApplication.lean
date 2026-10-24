import Strictness.Semantics.SemanticEquivalence
import Strictness.Semantics.SemanticBasic

namespace Strictness

open Usage
open Term

/-- Applying a divergent function in CBN remains divergent: the function is
forced before the argument is touched. -/
theorem diverges_app {f a : Term} :
    Term.Diverges f → Term.Diverges (.app f a) := by
  intro hF
  constructor
  · intro hEval
    rcases hEval with ⟨v, hEval⟩
    cases hEval with
    | app hFun _ =>
        exact hF.1 ⟨_, hFun⟩
  · intro hErr
    cases hErr with
    | appFun hFun => exact hF.2 hFun
    | appBody hFun _ => exact hF.1 ⟨_, hFun⟩

/-- Simple typing of an application of two simply typed closed terms. -/
theorem allTerms_app {σ τ : SimpleTy} {f a : Term} :
    AllTerms (.arrow σ τ) f → AllTerms σ a →
    AllTerms τ (.app f a) := by
  rintro ⟨hfClosed, hfType⟩ ⟨haClosed, haType⟩
  exact ⟨⟨hfClosed, haClosed⟩, Term.HasType.app hfType haType⟩

/-- Every divergent term of a type whose outer usage is strict or top belongs
 to its D-set.  This is the part of D needed when a function itself diverges
 in a strict application. -/
theorem divergentTerms_subset_D_of_outer_strict_or_top {τ : Ty}
    (hOuter : τ.outer = strict ∨ τ.outer = top) :
    TermSet.Subset (DivergentTerms τ.erase) (D τ) := by
  cases τ with
  | int u =>
      rcases hOuter with hOuter | hOuter
      · change u = strict at hOuter
        subst u
        intro e he
        unfold D LogicalModel.divergentSide operationalModel
        simp only [not_lazy_of_outer_strict (τ := .int strict) rfl]
        have : ¬ (lazy ≤ strict) := Usage.not_lazy_le_strict
        simp [this]
        exact he
      · change u = top at hOuter
        subst u
        intro e he
        rw [D_eq_allTerms_of_outer_top rfl]
        exact he.1
  | prod σ τ u =>
      rcases hOuter with hOuter | hOuter
      · change u = strict at hOuter
        subst u
        intro e he
        unfold D LogicalModel.divergentSide operationalModel
        simp only [not_lazy_of_outer_strict (τ := .prod σ τ strict) rfl]
        have : ¬ (lazy ≤ strict) := Usage.not_lazy_le_strict
        simp [this]
        exact Or.inl he
      · change u = top at hOuter
        subst u
        intro e he
        rw [D_eq_allTerms_of_outer_top rfl]
        exact he.1
  | arrow σ τ u =>
      rcases hOuter with hOuter | hOuter
      · change u = strict at hOuter
        subst u
        intro e he
        unfold D LogicalModel.divergentSide operationalModel
        simp only [not_lazy_of_outer_strict (τ := .arrow σ τ strict) rfl]
        have : ¬ (lazy ≤ strict) := Usage.not_lazy_le_strict
        simp [this]
        exact Or.inl he
      · change u = top at hOuter
        subst u
        intro e he
        rw [D_eq_allTerms_of_outer_top rfl]
        exact he.1

/-- If a function has a V-meaning and the result usage permits its function
usage, then applying it to a V-argument yields a V-result. -/
theorem V_arrow_apply
    {σ τ : Ty} {u : Usage} {f a : Term}
    (hu : u ≤ τ.outer)
    (hF : V (.arrow σ τ u) f)
    (hA : V σ a) :
    V τ (.app f a) := by
  cases u with
  | unknown =>
      unfold V LogicalModel.acceptable operationalModel at hF
      simp only [Usage.not_lazy_le_unknown] at hF
      rcases hF with hDiv | hFun
      · apply divergentTerms_subset_V τ
        exact ⟨allTerms_app hDiv.1 (V_subset_allTerms σ hA), diverges_app hDiv.2⟩
      · rcases hFun with ⟨hTyped, body, hev, hV, hD⟩
        exact hV a hA
  | strict =>
      unfold V LogicalModel.acceptable operationalModel at hF
      simp only [Usage.not_lazy_le_strict] at hF
      rcases hF with hDiv | hFun
      · apply divergentTerms_subset_V τ
        exact ⟨allTerms_app hDiv.1 (V_subset_allTerms σ hA), diverges_app hDiv.2⟩
      · rcases hFun with ⟨hTyped, body, hev, hV, hD⟩
        exact hV a hA
  | lazy =>
      have hOuter : τ.outer = lazy ∨ τ.outer = top := by
        cases τ with
        | int v =>
            cases v with
            | unknown => exact False.elim (by cases hu)
            | strict => exact False.elim (by cases hu)
            | lazy => exact Or.inl rfl
            | top => exact Or.inr rfl
        | prod σ τ v =>
            cases v with
            | unknown => exact False.elim (by cases hu)
            | strict => exact False.elim (by cases hu)
            | lazy => exact Or.inl rfl
            | top => exact Or.inr rfl
        | arrow σ τ v =>
            cases v with
            | unknown => exact False.elim (by cases hu)
            | strict => exact False.elim (by cases hu)
            | lazy => exact Or.inl rfl
            | top => exact Or.inr rfl
      rcases hOuter with hLazy | hTop
      · rw [V_eq_allTerms_of_outer_lazy hLazy]
        exact allTerms_app (V_subset_allTerms (.arrow σ τ lazy) hF)
          (V_subset_allTerms σ hA)
      · rw [V_eq_allTerms_of_outer_top hTop]
        exact allTerms_app (V_subset_allTerms (.arrow σ τ lazy) hF)
          (V_subset_allTerms σ hA)
  | top =>
      have hOuter : τ.outer = top := Usage.le_top_iff.mp hu
      rw [V_eq_allTerms_of_outer_top hOuter]
      exact allTerms_app (V_subset_allTerms (.arrow σ τ top) hF)
        (V_subset_allTerms σ hA)

/-- If a function is on the D-side and the result usage permits its function
usage, then applying it to a V-argument yields a D-result. -/
theorem D_arrow_apply
    {σ τ : Ty} {u : Usage} {f a : Term}
    (hu : u ≤ τ.outer)
    (hF : D (.arrow σ τ u) f)
    (hA : V σ a) :
    D τ (.app f a) := by
  cases u with
  | unknown =>
      rw [D_arrow_unknown_eq_empty] at hF
      exact False.elim hF
  | lazy =>
      have hLazy : Ty.IsLazy (.arrow σ τ lazy) := by
        change Usage.Le lazy lazy
        exact Usage.le_refl lazy
      rw [lazy_implies_D_empty hLazy] at hF
      exact False.elim hF
  | strict =>
      rcases Usage.le_strict_iff.mp hu with hOuter | hOuter
      · unfold D LogicalModel.divergentSide operationalModel at hF
        have hNot : ¬ (lazy ≤ strict) := Usage.not_lazy_le_strict
        simp [not_lazy_of_outer_strict
          (τ := .arrow σ τ strict) rfl, hNot] at hF
        rcases hF with hDiv | hStrict
        · apply divergentTerms_subset_D_of_outer_strict_or_top (τ := τ)
          · exact Or.inl hOuter
          · exact ⟨allTerms_app hDiv.1 (V_subset_allTerms σ hA),
              diverges_app hDiv.2⟩
        · rcases hStrict with ⟨hTyped, body, hev, hAppD⟩
          exact hAppD a hA
      · unfold D LogicalModel.divergentSide operationalModel at hF
        have hNot : ¬ (lazy ≤ strict) := Usage.not_lazy_le_strict
        simp [not_lazy_of_outer_strict
          (τ := .arrow σ τ strict) rfl, hNot] at hF
        rw [D_eq_allTerms_of_outer_top hOuter]
        rcases hF with hDiv | hStrict
        · exact allTerms_app hDiv.1 (V_subset_allTerms σ hA)
        · rcases hStrict with ⟨hTyped, body, hev, hAppD⟩
          exact D_subset_allTerms τ (hAppD a hA)
  | top =>
      have hOuter : τ.outer = top := Usage.le_top_iff.mp hu
      rw [D_eq_allTerms_of_outer_top hOuter]
      exact allTerms_app (D_subset_allTerms (.arrow σ τ top) hF)
        (V_subset_allTerms σ hA)


/-- A V-function with a D-argument yields a D-result in the only usage classes
that can be reached by a D-satisfying argument environment: `S` and `⊤`.
The `S` case uses the D-obligation of `FunctionTerms`; the `⊤` case is an
all-terms result. -/
theorem V_arrow_apply_D
    {σ τ : Ty} {u : Usage} {f a : Term}
    (hu : u ≤ τ.outer)
    (huClass : u = strict ∨ u = top)
    (hF : V (.arrow σ τ u) f)
    (hA : D σ a) :
    D τ (.app f a) := by
  rcases huClass with rfl | rfl
  · change Usage.Le strict τ.outer at hu
    rcases Usage.le_strict_iff.mp hu with hOuter | hOuter
    · unfold V LogicalModel.acceptable operationalModel at hF
      simp only [Usage.not_lazy_le_strict] at hF
      rcases hF with hDiv | hFun
      · apply divergentTerms_subset_D_of_outer_strict_or_top (τ := τ)
        · exact Or.inl hOuter
        · exact ⟨allTerms_app hDiv.1 (D_subset_allTerms σ hA),
            diverges_app hDiv.2⟩
      · rcases hFun with ⟨hTyped, body, hev, hV, hD⟩
        exact hD a hA
    · unfold V LogicalModel.acceptable operationalModel at hF
      simp only [Usage.not_lazy_le_strict] at hF
      rw [D_eq_allTerms_of_outer_top hOuter]
      rcases hF with hDiv | hFun
      · exact allTerms_app hDiv.1 (D_subset_allTerms σ hA)
      · rcases hFun with ⟨hTyped, body, hev, hV, hD⟩
        exact D_subset_allTerms τ (hD a hA)
  · have hτTop : τ.outer = top := Usage.le_top_iff.mp hu
    rw [D_eq_allTerms_of_outer_top hτTop]
    exact allTerms_app (V_subset_allTerms (.arrow σ τ top) hF)
      (D_subset_allTerms σ hA)

end Strictness
