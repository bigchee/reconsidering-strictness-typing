import Strictness.Semantics.SemanticApplication
import Strictness.Semantics.SemanticCap

namespace Strictness

open Usage
open Term

/-- Simple typing of a pair constructed from two closed, simply typed terms. -/
theorem allTerms_pair {σ τ : SimpleTy} {e₁ e₂ : Term} :
    AllTerms σ e₁ → AllTerms τ e₂ →
    AllTerms (.prod σ τ) (.pair e₁ e₂) := by
  rintro ⟨h₁c, h₁t⟩ ⟨h₂c, h₂t⟩
  exact ⟨⟨h₁c, h₂c⟩, Term.HasType.pair h₁t h₂t⟩

/-- Projection of a divergent scrutinee remains divergent. -/
theorem diverges_proj {b : Bool} {e : Term} :
    Term.Diverges e → Term.Diverges (.proj b e) := by
  intro h
  constructor
  · intro hev
    rcases hev with ⟨v, hev⟩
    cases hev with
    | projLeft hScrut _ =>
        exact h.1 ⟨_, hScrut⟩
    | projRight hScrut _ =>
        exact h.1 ⟨_, hScrut⟩
  · intro herr
    cases herr with
    | projScrutinee hs =>
        exact h.2 hs
    | projLeftComponent hScrut _ =>
        exact h.1 ⟨_, hScrut⟩
    | projRightComponent hScrut _ =>
        exact h.1 ⟨_, hScrut⟩

/-- V-membership for pair construction. -/
theorem V_pair_intro {σ τ : Ty} {u : Usage} {e₁ e₂ : Term}
    (hσ : V σ e₁) (hτ : V τ e₂) :
    V (.prod σ τ u) (.pair e₁ e₂) := by
  cases u with
  | unknown =>
      unfold V LogicalModel.acceptable operationalModel
      simp only [Usage.not_lazy_le_unknown]
      exact Or.inr ⟨allTerms_pair (V_subset_allTerms σ hσ)
        (V_subset_allTerms τ hτ), e₁, e₂, Eval.pair, hσ, hτ⟩
  | strict =>
      unfold V LogicalModel.acceptable operationalModel
      simp only [Usage.not_lazy_le_strict]
      exact Or.inr ⟨allTerms_pair (V_subset_allTerms σ hσ)
        (V_subset_allTerms τ hτ), e₁, e₂, Eval.pair, hσ, hτ⟩
  | lazy =>
      rw [V_eq_allTerms_of_outer_lazy rfl]
      exact allTerms_pair (V_subset_allTerms σ hσ) (V_subset_allTerms τ hτ)
  | top =>
      rw [V_eq_allTerms_of_outer_top rfl]
      exact allTerms_pair (V_subset_allTerms σ hσ) (V_subset_allTerms τ hτ)

/-- D-membership for pair construction when the left component supplies the
D-witness.  The pair typing inequalities are needed in the `?` case. -/
theorem D_pair_left_intro {σ τ : Ty} {u : Usage} {e₁ e₂ : Term}
    (hσ : D σ e₁) (hτ : V τ e₂)
    (hσOuter : σ.outer ≤ u ⊔ lazy)
    (hτOuter : τ.outer ≤ u ⊔ lazy) :
    D (.prod σ τ u) (.pair e₁ e₂) := by
  cases u with
  | unknown =>
      have hNotLazyProd : ¬ Ty.IsLazy (.prod σ τ unknown) := by
        intro hL
        have hσempty := hσ
        rw [lazy_implies_D_empty hL.2.1] at hσempty
        exact hσempty
      unfold D LogicalModel.divergentSide operationalModel
      simp only [hNotLazyProd, Usage.not_lazy_le_unknown] at *
      apply Or.inr
      apply Or.inl
      exact ⟨allTerms_pair (D_subset_allTerms σ hσ)
        (V_subset_allTerms τ hτ), e₁, e₂, Eval.pair, hσ, hτ⟩
  | lazy =>
      have hNotLazyProd : ¬ Ty.IsLazy (.prod σ τ lazy) := by
        intro hL
        have hσempty := hσ
        rw [lazy_implies_D_empty hL.2.1] at hσempty
        exact hσempty
      rw [D_eq_allTerms_of_not_lazy hNotLazyProd Usage.lazy_le_lazy]
      exact allTerms_pair (D_subset_allTerms σ hσ)
        (V_subset_allTerms τ hτ)
  | strict =>
      unfold D LogicalModel.divergentSide operationalModel
      simp only [not_lazy_of_outer_strict (τ := .prod σ τ strict) rfl] at *
      simp;
      have hnot : ¬ (lazy ≤ strict) := Usage.not_lazy_le_strict
      simp [hnot]
      apply Or.inr
      apply Or.inl
      exact ⟨allTerms_pair (D_subset_allTerms σ hσ)
        (V_subset_allTerms τ hτ), e₁, e₂, Eval.pair, hσ, hτ⟩
  | top =>
      rw [D_eq_allTerms_of_outer_top rfl]
      exact allTerms_pair (D_subset_allTerms σ hσ) (V_subset_allTerms τ hτ)

/-- Symmetric D-membership for pair construction. -/
theorem D_pair_right_intro {σ τ : Ty} {u : Usage} {e₁ e₂ : Term}
    (hσ : V σ e₁) (hτ : D τ e₂)
    (hσOuter : σ.outer ≤ u ⊔ lazy)
    (hτOuter : τ.outer ≤ u ⊔ lazy) :
    D (.prod σ τ u) (.pair e₁ e₂) := by
  cases u with
  | unknown =>
      have hNotLazyProd : ¬ Ty.IsLazy (.prod σ τ unknown) := by
        intro hL
        have hτempty := hτ
        rw [lazy_implies_D_empty hL.2.2] at hτempty
        exact hτempty
      unfold D LogicalModel.divergentSide operationalModel
      simp only [hNotLazyProd, Usage.not_lazy_le_unknown] at *
      apply Or.inr
      apply Or.inr
      exact ⟨allTerms_pair (V_subset_allTerms σ hσ)
        (D_subset_allTerms τ hτ), e₁, e₂, Eval.pair, hσ, hτ⟩

  | lazy =>
      have hNotLazyProd : ¬ Ty.IsLazy (.prod σ τ lazy) := by
        intro hL
        have hτempty := hτ
        rw [lazy_implies_D_empty hL.2.2] at hτempty
        exact hτempty
      rw [D_eq_allTerms_of_not_lazy hNotLazyProd Usage.lazy_le_lazy]
      exact allTerms_pair (V_subset_allTerms σ hσ)
        (D_subset_allTerms τ hτ)

  | strict =>
      have hNotLazyProd : ¬ Ty.IsLazy (.prod σ τ strict) :=
        not_lazy_of_outer_strict (τ := .prod σ τ strict) rfl
      unfold D LogicalModel.divergentSide operationalModel
      simp only [hNotLazyProd, Usage.not_lazy_le_strict]
      apply Or.inr
      apply Or.inr
      exact ⟨allTerms_pair (V_subset_allTerms σ hσ)
        (D_subset_allTerms τ hτ), e₁, e₂, Eval.pair, hσ, hτ⟩

  | top =>
      rw [D_eq_allTerms_of_outer_top rfl]
      exact allTerms_pair (V_subset_allTerms σ hσ)
        (D_subset_allTerms τ hτ)

/-- V-side projection for the left component. -/
theorem V_proj_left {σ τ : Ty} {u : Usage} {e : Term}
    (hu : u ≤ σ.outer) (_ : Ty.IsLazy τ)
    (hE : V (.prod σ τ u) e) :
    V σ (.proj true e) := by
  cases u with
  | unknown =>
      unfold V LogicalModel.acceptable operationalModel at hE
      simp only [Usage.not_lazy_le_unknown] at hE
      rcases hE with hDiv | hPair
      · apply divergentTerms_subset_V σ
        exact ⟨⟨hDiv.1.1,
          Term.HasType.projLeft hDiv.1.2⟩,
          diverges_proj hDiv.2⟩
      · rcases hPair with ⟨hAll, e₁, e₂, hev, h₁, h₂⟩
        have hEq := semEq_proj_left hAll (V_subset_allTerms σ h₁)
          (V_subset_allTerms τ h₂) hev
        exact (semantic_equiv_VD hEq).1.mpr h₁
  | strict =>
      unfold V LogicalModel.acceptable operationalModel at hE
      simp only [Usage.not_lazy_le_strict] at hE
      rcases hE with hDiv | hPair
      · apply divergentTerms_subset_V σ
        exact ⟨⟨hDiv.1.1,
          Term.HasType.projLeft hDiv.1.2⟩,
          diverges_proj hDiv.2⟩
      · rcases hPair with ⟨hAll, e₁, e₂, hev, h₁, h₂⟩
        have hEq := semEq_proj_left hAll (V_subset_allTerms σ h₁)
          (V_subset_allTerms τ h₂) hev
        exact (semantic_equiv_VD hEq).1.mpr h₁
  | lazy =>
      have hs : σ.outer = lazy ∨ σ.outer = top := by
        cases σ with
        | int u =>
            cases u <;> simp_all [Ty.outer, Usage.Le]
        | prod a b u =>
            cases u <;> simp_all [Ty.outer, Usage.Le]
        | arrow a b u =>
            cases u <;> simp_all [Ty.outer, Usage.Le]
      rcases hs with hs | hs
      · rw [V_eq_allTerms_of_outer_lazy hs]
        exact ⟨(V_subset_allTerms (.prod σ τ lazy) hE).1,
          Term.HasType.projLeft (V_subset_allTerms (.prod σ τ lazy) hE).2⟩
      · rw [V_eq_allTerms_of_outer_top hs]
        exact ⟨(V_subset_allTerms (.prod σ τ lazy) hE).1,
          Term.HasType.projLeft (V_subset_allTerms (.prod σ τ lazy) hE).2⟩
  | top =>
      have hs : σ.outer = top := by
        cases σ with
        | int u =>
            cases u <;> simp_all [Ty.outer, Usage.Le]
        | prod a b u =>
            cases u <;> simp_all [Ty.outer, Usage.Le]
        | arrow a b u =>
            cases u <;> simp_all [Ty.outer, Usage.Le]
      rw [V_eq_allTerms_of_outer_top hs]
      exact ⟨(V_subset_allTerms (.prod σ τ top) hE).1,
        Term.HasType.projLeft (V_subset_allTerms (.prod σ τ top) hE).2⟩

/-- V-side projection for the right component. -/
theorem V_proj_right {σ τ : Ty} {u : Usage} {e : Term}
    (hu : u ≤ τ.outer) (_ : Ty.IsLazy σ)
    (hE : V (.prod σ τ u) e) :
    V τ (.proj false e) := by
  cases u with
  | unknown =>
      unfold V LogicalModel.acceptable operationalModel at hE
      simp only [Usage.not_lazy_le_unknown] at hE
      rcases hE with hDiv | hPair
      · apply divergentTerms_subset_V τ
        exact ⟨⟨hDiv.1.1,
          Term.HasType.projRight hDiv.1.2⟩,
          diverges_proj hDiv.2⟩
      · rcases hPair with ⟨hAll, e₁, e₂, hev, h₁, h₂⟩
        have hEq := semEq_proj_right hAll
          (V_subset_allTerms σ h₁)
          (V_subset_allTerms τ h₂) hev
        exact (semantic_equiv_VD hEq).1.mpr h₂

  | strict =>
      unfold V LogicalModel.acceptable operationalModel at hE
      simp only [Usage.not_lazy_le_strict] at hE
      rcases hE with hDiv | hPair
      · apply divergentTerms_subset_V τ
        exact ⟨⟨hDiv.1.1,
          Term.HasType.projRight hDiv.1.2⟩,
          diverges_proj hDiv.2⟩
      · rcases hPair with ⟨hAll, e₁, e₂, hev, h₁, h₂⟩
        have hEq := semEq_proj_right hAll
          (V_subset_allTerms σ h₁)
          (V_subset_allTerms τ h₂) hev
        exact (semantic_equiv_VD hEq).1.mpr h₂

  | lazy =>
      have hs : τ.outer = lazy ∨ τ.outer = top := by
        cases τ with
        | int u =>
            cases u <;> simp_all [Ty.outer, Usage.Le]
        | prod a b u =>
            cases u <;> simp_all [Ty.outer, Usage.Le]
        | arrow a b u =>
            cases u <;> simp_all [Ty.outer, Usage.Le]
      rcases hs with hs | hs
      · rw [V_eq_allTerms_of_outer_lazy hs]
        exact ⟨(V_subset_allTerms (.prod σ τ lazy) hE).1,
          Term.HasType.projRight (V_subset_allTerms (.prod σ τ lazy) hE).2⟩
      · rw [V_eq_allTerms_of_outer_top hs]
        exact ⟨(V_subset_allTerms (.prod σ τ lazy) hE).1,
          Term.HasType.projRight (V_subset_allTerms (.prod σ τ lazy) hE).2⟩

  | top =>
      have hs : τ.outer = top := by
        cases τ with
        | int u =>
            cases u <;> simp_all [Ty.outer, Usage.Le]
        | prod a b u =>
            cases u <;> simp_all [Ty.outer, Usage.Le]
        | arrow a b u =>
            cases u <;> simp_all [Ty.outer, Usage.Le]
      rw [V_eq_allTerms_of_outer_top hs]
      exact ⟨(V_subset_allTerms (.prod σ τ top) hE).1,
        Term.HasType.projRight (V_subset_allTerms (.prod σ τ top) hE).2⟩

/-- D-side projection for the left component. -/
theorem D_proj_left {σ τ : Ty} {u : Usage} {e : Term}
    (hu : u ≤ σ.outer) (hLazy : Ty.IsLazy τ)
    (hE : D (.prod σ τ u) e) :
    D σ (.proj true e) := by
  cases u with
  | unknown =>
      have hNotLazyProd : ¬ Ty.IsLazy (.prod σ τ unknown) := by
        intro hL
        have hσempty := hE
        rw [lazy_implies_D_empty hL] at hσempty
        exact hσempty

      have hNotLazyσ : ¬ Ty.IsLazy σ := by
        intro hσL
        exact hNotLazyProd (by
          exact ⟨by trivial, hσL, hLazy⟩)

      unfold D LogicalModel.divergentSide operationalModel at hE
      simp only [hNotLazyProd, Usage.not_lazy_le_unknown] at hE

      rcases hE with hDiv | hPair
      · rcases hDiv with ⟨hAll, hDiverges⟩
        rcases hAll with ⟨hClosed, hTy⟩
        apply divergentTerms_subset_D_of_not_lazy hNotLazyσ
        exact ⟨⟨hClosed, Term.HasType.projLeft hTy⟩,
          diverges_proj hDiverges⟩
      · rcases hPair with hLeft | hRight
        · rcases hLeft with ⟨hAll, e₁, e₂, hev, h₁, h₂⟩
          have hEq := semEq_proj_left hAll
            (D_subset_allTerms σ h₁)
            (V_subset_allTerms τ h₂)
            hev
          exact (semantic_equiv_VD hEq).2.mpr h₁
        · rcases hRight with ⟨e₁, e₂, hev, h₁, h₂⟩
          exact False.elim (by
            have hτempty : D τ hev := h₂.2
            rw [lazy_implies_D_empty hLazy] at hτempty
            exact hτempty)

  | strict =>
      have hs : σ.outer = strict ∨ σ.outer = top := by
        cases σ with
        | int v =>
            cases v <;> simp_all [Ty.outer, Usage.Le]
        | prod a b v =>
            cases v <;> simp_all [Ty.outer, Usage.Le]
        | arrow a b v =>
            cases v <;> simp_all [Ty.outer, Usage.Le]

      have hNotLazyProd : ¬ Ty.IsLazy (.prod σ τ strict) :=
        not_lazy_of_outer_strict (τ := .prod σ τ strict) rfl

      unfold D LogicalModel.divergentSide operationalModel at hE
      simp only [hNotLazyProd, Usage.not_lazy_le_strict] at hE

      rcases hE with hDiv | hPair
      · rcases hDiv with ⟨hAll, hDiverges⟩
        rcases hAll with ⟨hClosed, hTy⟩
        apply divergentTerms_subset_D_of_outer_strict_or_top hs
        exact ⟨⟨hClosed, Term.HasType.projLeft hTy⟩,
          diverges_proj hDiverges⟩
      · rcases hPair with hLeft | hRight
        · rcases hLeft with ⟨hAll, e₁, e₂, hev, h₁, h₂⟩
          have hEq := semEq_proj_left hAll
            (D_subset_allTerms σ h₁)
            (V_subset_allTerms τ h₂)
            hev
          exact (semantic_equiv_VD hEq).2.mpr h₁
        · rcases hRight with ⟨e₁, e₂, hev, h₁, h₂⟩
          exact False.elim (by
            have hτempty : D τ hev := h₂.2
            rw [lazy_implies_D_empty hLazy] at hτempty
            exact hτempty)

  | lazy =>
      have hs : σ.outer = lazy ∨ σ.outer = top := by
        cases σ with
        | int v =>
            cases v <;> simp_all [Ty.outer, Usage.Le]
        | prod a b v =>
            cases v <;> simp_all [Ty.outer, Usage.Le]
        | arrow a b v =>
            cases v <;> simp_all [Ty.outer, Usage.Le]

      have hNotProd : ¬ Ty.IsLazy (.prod σ τ lazy) := by
        intro hp
        have hEempty := hE
        rw [lazy_implies_D_empty hp] at hEempty
        exact hEempty

      rw [D_eq_allTerms_of_not_lazy hNotProd Usage.lazy_le_lazy] at hE

      rcases hs with hs | hs
      · have hNotσ : ¬ Ty.IsLazy σ := by
          intro hσL
          exact hNotProd (by
            exact ⟨Usage.lazy_le_lazy, hσL, hLazy⟩)
        have hOuter : lazy ≤ σ.outer := by
          simpa [hs] using Usage.lazy_le_lazy
        rw [D_eq_allTerms_of_not_lazy hNotσ hOuter]
        exact ⟨hE.1, Term.HasType.projLeft hE.2⟩
      · rw [D_eq_allTerms_of_outer_top hs]
        exact ⟨hE.1, Term.HasType.projLeft hE.2⟩

  | top =>
      have hs : σ.outer = top := by
        cases σ with
        | int v =>
            cases v <;> simp_all [Ty.outer, Usage.Le]
        | prod a b v =>
            cases v <;> simp_all [Ty.outer, Usage.Le]
        | arrow a b v =>
            cases v <;> simp_all [Ty.outer, Usage.Le]

      rw [D_eq_allTerms_of_outer_top hs]
      exact ⟨(D_subset_allTerms (.prod σ τ top) hE).1,
        Term.HasType.projLeft (D_subset_allTerms (.prod σ τ top) hE).2⟩

/-- D-side projection for the right component. -/
theorem D_proj_right {σ τ : Ty} {u : Usage} {e : Term}
    (hu : u ≤ τ.outer) (hLazy : Ty.IsLazy σ)
    (hE : D (.prod σ τ u) e) :
    D τ (.proj false e) := by
  cases u with
  | unknown =>
      have hNotLazyProd : ¬ Ty.IsLazy (.prod σ τ unknown) := by
        intro hL
        have hEempty := hE
        rw [lazy_implies_D_empty hL] at hEempty
        exact hEempty
      have hNotLazyτ : ¬ Ty.IsLazy τ := by
        intro hτL
        exact hNotLazyProd (by exact ⟨by trivial, hLazy, hτL⟩)
      unfold D LogicalModel.divergentSide operationalModel at hE
      simp only [hNotLazyProd, Usage.not_lazy_le_unknown] at hE
      rcases hE with hDiv | hPair
      · rcases hDiv with ⟨hAll, hDiverges⟩
        rcases hAll with ⟨hClosed, hTy⟩
        apply divergentTerms_subset_D_of_not_lazy hNotLazyτ
        exact ⟨⟨hClosed, Term.HasType.projRight hTy⟩,
          diverges_proj hDiverges⟩
      · rcases hPair with hLeft | hRight
        · rcases hLeft with ⟨e₁, e₂, hev, h₁, h₂⟩
          exact False.elim (by
            have hσempty : D σ e₂ := h₂.1
            rw [lazy_implies_D_empty hLazy] at hσempty
            exact hσempty)
        · rcases hRight with ⟨hAll, e₁, e₂, hev, h₁, h₂⟩
          have hEq := semEq_proj_right hAll
            (V_subset_allTerms σ h₁)
            (D_subset_allTerms τ h₂)
            hev
          exact (semantic_equiv_VD hEq).2.mpr h₂
  | strict =>
      have hs : τ.outer = strict ∨ τ.outer = top := by
        cases τ with
        | int v => cases v <;> simp_all [Ty.outer, Usage.Le]
        | prod a b v => cases v <;> simp_all [Ty.outer, Usage.Le]
        | arrow a b v => cases v <;> simp_all [Ty.outer, Usage.Le]
      have hNotLazyProd : ¬ Ty.IsLazy (.prod σ τ strict) :=
        not_lazy_of_outer_strict (τ := .prod σ τ strict) rfl
      unfold D LogicalModel.divergentSide operationalModel at hE
      simp only [hNotLazyProd, Usage.not_lazy_le_strict] at hE
      rcases hE with hDiv | hPair
      · rcases hDiv with ⟨hAll, hDiverges⟩
        rcases hAll with ⟨hClosed, hTy⟩
        apply divergentTerms_subset_D_of_outer_strict_or_top hs
        exact ⟨⟨hClosed, Term.HasType.projRight hTy⟩,
          diverges_proj hDiverges⟩
      · rcases hPair with hLeft | hRight
        · rcases hLeft with ⟨e₁, e₂, hev, h₁, h₂⟩
          exact False.elim (by
            have hσempty : D σ e₂ := h₂.1
            rw [lazy_implies_D_empty hLazy] at hσempty
            exact hσempty)
        · rcases hRight with ⟨hAll, e₁, e₂, hev, h₁, h₂⟩
          have hEq := semEq_proj_right hAll
            (V_subset_allTerms σ h₁)
            (D_subset_allTerms τ h₂)
            hev
          exact (semantic_equiv_VD hEq).2.mpr h₂
  | lazy =>
      have hs : τ.outer = lazy ∨ τ.outer = top := by
        cases τ with
        | int v => cases v <;> simp_all [Ty.outer, Usage.Le]
        | prod a b v => cases v <;> simp_all [Ty.outer, Usage.Le]
        | arrow a b v => cases v <;> simp_all [Ty.outer, Usage.Le]
      have hNotProd : ¬ Ty.IsLazy (.prod σ τ lazy) := by
        intro hp
        have hEempty := hE
        rw [lazy_implies_D_empty hp] at hEempty
        exact hEempty
      rw [D_eq_allTerms_of_not_lazy hNotProd Usage.lazy_le_lazy] at hE
      rcases hs with hs | hs
      · have hNotτ : ¬ Ty.IsLazy τ := by
          intro hτL
          exact hNotProd (by exact ⟨Usage.lazy_le_lazy, hLazy, hτL⟩)
        have hOuter : lazy ≤ τ.outer := by
          simpa [hs] using Usage.lazy_le_lazy
        rw [D_eq_allTerms_of_not_lazy hNotτ hOuter]
        exact ⟨hE.1, Term.HasType.projRight hE.2⟩
      · rw [D_eq_allTerms_of_outer_top hs]
        exact ⟨hE.1, Term.HasType.projRight hE.2⟩
  | top =>
      have hs : τ.outer = top := by
        cases τ with
        | int v => cases v <;> simp_all [Ty.outer, Usage.Le]
        | prod a b v => cases v <;> simp_all [Ty.outer, Usage.Le]
        | arrow a b v => cases v <;> simp_all [Ty.outer, Usage.Le]
      rw [D_eq_allTerms_of_outer_top hs]
      exact ⟨(D_subset_allTerms (.prod σ τ top) hE).1,
        Term.HasType.projRight (D_subset_allTerms (.prod σ τ top) hE).2⟩

end Strictness
