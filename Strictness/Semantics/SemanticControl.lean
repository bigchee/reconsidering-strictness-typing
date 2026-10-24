import Strictness.Semantics.SemanticEquivalence
import Strictness.Semantics.SemanticPairProjection
import Strictness.Operational.BigStep

namespace Strictness

open Usage
open Term

/-- Divergence of the left operand forces divergence of an arithmetic operation. -/
theorem diverges_op_left {e₁ e₂ : Term} :
    Term.Diverges e₁ → Term.Diverges (.op o e₁ e₂) := by
  intro h
  constructor
  · intro hev
    rcases hev with ⟨v, hv⟩
    cases hv with
    | op o h₁ _ => exact h.1 ⟨_, h₁⟩
  · intro herr
    cases herr with
    | opLeft o hErr => exact h.2 hErr
    | opRight o h₁ _ => exact h.1 ⟨_, h₁⟩

/-- Divergence of the right operand forces divergence of an arithmetic operation when the
left operand cannot produce the semantic error marker. -/
theorem diverges_op_right {e₁ e₂ : Term} :
    ¬ EvalErr e₁ →
    Term.Diverges e₂ →
    Term.Diverges (.op o e₁ e₂) := by
  intro hNoErr h
  constructor
  · intro hev
    rcases hev with ⟨v, hv⟩
    cases hv with
    | op o _ h₂ => exact h.1 ⟨_, h₂⟩
  · intro herr
    cases herr with
    | opLeft o hErr => exact False.elim (hNoErr hErr)
    | opRight o _ hErr => exact h.2 hErr

/-- A simply typed arithmetic operation built from two simply typed closed operands. -/
theorem allTerms_op {e₁ e₂ : Term} :
    AllTerms .int e₁ → AllTerms .int e₂ →
    AllTerms .int (.op o e₁ e₂) := by
  rintro ⟨hc₁, ht₁⟩ ⟨hc₂, ht₂⟩
  exact ⟨⟨hc₁, hc₂⟩, Term.HasType.op o ht₁ ht₂⟩

/-- An arithmetic operation preserves the V-side when all three usage annotations are
non-lazy.  For an integer type, the V-side is the union of divergent terms
and numeral terms in this case. -/
theorem V_op_nonlazy
    {u₁ u₂ u : Usage} {e₁ e₂ : Term}
    (h1nl : ¬ lazy ≤ u₁)
    (h2nl : ¬ lazy ≤ u₂)
    (hnl : ¬ lazy ≤ u)
    (h₁ : V (.int u₁) e₁)
    (h₂ : V (.int u₂) e₂) :
    V (.int u) (.op o e₁ e₂) := by
  unfold V LogicalModel.acceptable operationalModel at h₁ h₂ ⊢
  simp only [h1nl, h2nl, hnl] at h₁ h₂ ⊢
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · exact Or.inl ⟨allTerms_op h₁.1 h₂.1, diverges_op_left h₁.2⟩
    · exact Or.inl ⟨allTerms_op h₁.1 ⟨h₂.1, h₂.2.1⟩,
          diverges_op_left h₁.2⟩
  · rcases h₂ with h₂ | h₂
    · rcases h₁.2.2 with ⟨n₁, hn₁⟩
      exact Or.inl ⟨allTerms_op ⟨h₁.1, h₁.2.1⟩ h₂.1,
          diverges_op_right (eval_not_evalErr hn₁) h₂.2⟩
    · rcases h₁.2.2 with ⟨n₁, hn₁⟩
      rcases h₂.2.2 with ⟨n₂, hn₂⟩
      exact Or.inr ⟨⟨h₁.1, h₂.1⟩,
        Term.HasType.op o h₁.2.1 h₂.2.1,
        ⟨o.eval n₁ n₂, Eval.op o hn₁ hn₂⟩⟩

/-- V-side soundness of arithmetic operations. -/
theorem V_op
    {u₁ u₂ u : Usage} {e₁ e₂ : Term}
    (hu₁ : u₁ ≤ u) (hu₂ : u₂ ≤ u)
    (h₁ : V (.int u₁) e₁) (h₂ : V (.int u₂) e₂) :
    V (.int u) (.op o e₁ e₂) := by
  cases u with
  | unknown =>
      have hu₁' : u₁ = unknown := Usage.le_unknown_iff.mp hu₁
      have hu₂' : u₂ = unknown := Usage.le_unknown_iff.mp hu₂
      subst u₁
      subst u₂
      exact V_op_nonlazy
        (by simp [Usage.Le])
        (by simp [Usage.Le])
        (by simp [Usage.Le])
        h₁ h₂
  | strict =>
      have h1nl : ¬ lazy ≤ u₁ := by
        intro h
        exact Usage.not_lazy_le_strict (Usage.le_trans h hu₁)
      have h2nl : ¬ lazy ≤ u₂ := by
        intro h
        exact Usage.not_lazy_le_strict (Usage.le_trans h hu₂)
      exact V_op_nonlazy
        h1nl
        h2nl
        (by simp [Usage.Le])
        h₁ h₂
  | lazy =>
      rw [V_eq_allTerms_of_outer_lazy rfl]
      exact allTerms_op
        (V_subset_allTerms _ h₁)
        (V_subset_allTerms _ h₂)
  | top =>
      rw [V_eq_allTerms_of_outer_top rfl]
      exact allTerms_op
        (V_subset_allTerms _ h₁)
        (V_subset_allTerms _ h₂)

/-- D-side soundness of arithmetic operations when the left operand supplies the D witness. -/
theorem D_op_left
    {u₁ u₂ u : Usage} {e₁ e₂ : Term}
    (hu₁ : u₁ ≤ u) (hu₂ : u₂ ≤ u)
    (h₁ : D (.int u₁) e₁) (h₂ : V (.int u₂) e₂) :
    D (.int u) (.op o e₁ e₂) := by
  cases u with
  | unknown =>
      have hu₁' : u₁ = unknown := Usage.le_unknown_iff.mp hu₁
      subst u₁
      rw [D_int_unknown_eq_empty] at h₁
      exact False.elim h₁
  | lazy =>
      cases u₁ with
      | unknown =>
          rw [D_int_unknown_eq_empty] at h₁
          exact False.elim h₁
      | strict =>
          exact False.elim hu₁
      | lazy =>
          rw [lazy_implies_D_empty (τ := .int lazy)
            (Usage.le_refl lazy)] at h₁
          exact False.elim h₁
      | top =>
          exact False.elim hu₁
  | strict =>
      cases u₁ with
      | unknown =>
          rw [D_int_unknown_eq_empty] at h₁
          exact False.elim h₁
      | strict =>
          unfold D LogicalModel.divergentSide operationalModel at h₁ ⊢
          simp only [not_lazy_of_outer_strict (τ := .int strict) rfl,
            Usage.not_lazy_le_strict] at h₁ ⊢
          exact ⟨allTerms_op h₁.1 (V_subset_allTerms _ h₂),
            diverges_op_left h₁.2⟩
      | lazy =>
          exact False.elim hu₁
      | top =>
          exact False.elim hu₁
  | top =>
      rw [D_eq_allTerms_of_outer_top rfl]
      exact allTerms_op
        (D_subset_allTerms _ h₁)
        (V_subset_allTerms _ h₂)

/-- D-side soundness of arithmetic operations when the right operand supplies the D witness. -/
theorem D_op_right
    {u₁ u₂ u : Usage} {e₁ e₂ : Term}
    (hu₁ : u₁ ≤ u) (hu₂ : u₂ ≤ u)
    (h₁ : V (.int u₁) e₁) (h₂ : D (.int u₂) e₂) :
    D (.int u) (.op o e₁ e₂) := by
  cases u with
  | unknown =>
      have hu₂' : u₂ = unknown := Usage.le_unknown_iff.mp hu₂
      subst u₂
      rw [D_int_unknown_eq_empty] at h₂
      exact False.elim h₂
  | lazy =>
      cases u₂ with
      | unknown =>
          rw [D_int_unknown_eq_empty] at h₂
          exact False.elim h₂
      | strict =>
          exact False.elim hu₂
      | lazy =>
          rw [lazy_implies_D_empty (τ := .int lazy)
            (Usage.le_refl lazy)] at h₂
          exact False.elim h₂
      | top =>
          exact False.elim hu₂
  | strict =>
      cases u₂ with
      | unknown =>
          rw [D_int_unknown_eq_empty] at h₂
          exact False.elim h₂
      | strict =>
          have h1nl : ¬ lazy ≤ u₁ := by
            intro h
            exact Usage.not_lazy_le_strict (Usage.le_trans h hu₁)
          unfold V LogicalModel.acceptable operationalModel at h₁
          simp only [h1nl] at h₁
          unfold D LogicalModel.divergentSide operationalModel at h₂ ⊢
          simp only [not_lazy_of_outer_strict (τ := .int strict) rfl,
            Usage.not_lazy_le_strict] at h₂ ⊢
          rcases h₁ with h₁ | h₁
          · exact ⟨allTerms_op h₁.1 h₂.1,
              diverges_op_left h₁.2⟩
          · rcases h₁.2.2 with ⟨n, hn⟩
            exact ⟨allTerms_op ⟨h₁.1, h₁.2.1⟩ h₂.1,
              diverges_op_right (eval_not_evalErr hn) h₂.2⟩
      | lazy =>
          exact False.elim hu₂
      | top =>
          exact False.elim hu₂
  | top =>
      rw [D_eq_allTerms_of_outer_top rfl]
      exact allTerms_op
        (V_subset_allTerms _ h₁)
        (D_subset_allTerms _ h₂)

/-- Divergence of the conditional makes the whole conditional diverge. -/
theorem diverges_if_cond {e₀ e₁ e₂ : Term} :
    Term.Diverges e₀ → Term.Diverges (.ite e₀ e₁ e₂) := by
  intro h
  constructor
  · intro hev
    rcases hev with ⟨v, hv⟩
    cases hv with
    | ifZero hCond _ _ => exact h.1 ⟨_, hCond⟩
    | ifNonzero hCond _ _ => exact h.1 ⟨_, hCond⟩
  · intro herr
    cases herr with
    | ifCond hErr => exact h.2 hErr
    | ifZeroBranch hCond _ _ => exact h.1 ⟨_, hCond⟩
    | ifNonzeroBranch hCond _ _ => exact h.1 ⟨_, hCond⟩

/-- Divergence of a selected conditional branch makes the whole conditional diverge. -/
theorem diverges_if_zero_branch {e₀ e₁ e₂ : Term} {n : Int} :
    Eval e₀ (.int n) → n = 0 → Term.Diverges e₂ →
    Term.Diverges (.ite e₀ e₁ e₂) := by
  intro hCond hn h
  constructor
  · intro hev
    rcases hev with ⟨v, hv⟩
    cases hv with
    | ifZero hCond' hz hb =>
        exact h.1 ⟨_, hb⟩
    | ifNonzero hCond' hnz _ =>
        have hN := eval_deterministic hCond hCond'
        cases hN
        exact False.elim (hnz hn)
  · intro herr
    cases herr with
    | ifCond hErr =>
        exact (eval_not_evalErr hCond) hErr
    | ifZeroBranch _ _ hBranchErr =>
        exact h.2 hBranchErr
    | ifNonzeroBranch hCond' hnz _ =>
        have hN := eval_deterministic hCond hCond'
        cases hN
        exact False.elim (hnz hn)

/-- Divergence of a selected conditional branch makes the whole conditional diverge. -/
theorem diverges_if_nonzero_branch {e₀ e₁ e₂ : Term} {n : Int} :
    Eval e₀ (.int n) → n ≠ 0 → Term.Diverges e₁ →
    Term.Diverges (.ite e₀ e₁ e₂) := by
  intro hCond hn h
  constructor
  · intro hev
    rcases hev with ⟨v, hv⟩
    cases hv with
    | ifZero hCond' hz _ =>
        have hN := eval_deterministic hCond hCond'
        cases hN
        exact False.elim (hn hz)
    | ifNonzero hCond' hnz hb =>
        exact h.1 ⟨_, hb⟩
  · intro herr
    cases herr with
    | ifCond hErr =>
        exact (eval_not_evalErr hCond) hErr
    | ifZeroBranch hCond' hz _ =>
        have hN := eval_deterministic hCond hCond'
        cases hN
        exact False.elim (hn hz)
    | ifNonzeroBranch _ _ hBranchErr =>
        exact h.2 hBranchErr

/-- A simply typed conditional from a condition and two branches of the same type. -/
theorem allTerms_if {σ : SimpleTy} {e₀ e₁ e₂ : Term} :
    AllTerms .int e₀ → AllTerms σ e₁ → AllTerms σ e₂ →
    AllTerms σ (.ite e₀ e₁ e₂) := by
  rintro ⟨hc, ht⟩ ⟨h1c, h1t⟩ ⟨h2c, h2t⟩
  exact ⟨⟨hc, h1c, h2c⟩, Term.HasType.ite ht h1t h2t⟩

theorem V_if
    {u : Usage} {τ τ₁ τ₂ : Ty} {e₀ e₁ e₂ : Term}
    (hu : u ≤ τ.outer)
    (h0 : V (.int u) e₀)
    (h1 : V τ₁ e₁) (h2 : V τ₂ e₂)
    (hs1 : Ty.Subtype τ₁ τ) (hs2 : Ty.Subtype τ₂ τ) :
    V τ (.ite e₀ e₁ e₂) := by
  have h1τ : V τ e₁ := (semantic_subtype hs1).1 h1
  have h2τ : V τ e₂ := (semantic_subtype hs2).1 h2
  by_cases hLazy : lazy ≤ τ.outer
  · have hOuter : τ.outer = lazy ∨ τ.outer = top :=
      Usage.le_lazy_iff.mp hLazy
    rcases hOuter with hL | hT
    · rw [V_eq_allTerms_of_outer_lazy hL]
      exact allTerms_if
        (V_subset_allTerms _ h0)
        (V_subset_allTerms _ h1τ)
        (V_subset_allTerms _ h2τ)
    · rw [V_eq_allTerms_of_outer_top hT]
      exact allTerms_if
        (V_subset_allTerms _ h0)
        (V_subset_allTerms _ h1τ)
        (V_subset_allTerms _ h2τ)
  · have h0NonLazy : ¬ lazy ≤ u := by
      intro h
      exact hLazy (Usage.le_trans h hu)
    unfold V LogicalModel.acceptable operationalModel at h0
    simp only [h0NonLazy] at h0
    rcases h0 with hDiv | hNum
    · cases τ with
        | int uτ =>
            have hLazy' : ¬ lazy ≤ uτ := by
              simpa [Ty.outer] using hLazy
            unfold V LogicalModel.acceptable operationalModel
            simp only [hLazy']
            exact Or.inl ⟨
              allTerms_if hDiv.1
                (V_subset_allTerms _ h1τ)
                (V_subset_allTerms _ h2τ),
              diverges_if_cond hDiv.2⟩

        | prod σ τ uτ =>
            have hLazy' : ¬ lazy ≤ uτ := by
              simpa [Ty.outer] using hLazy
            unfold V LogicalModel.acceptable operationalModel
            simp only [hLazy']
            exact Or.inl ⟨
              allTerms_if hDiv.1
                (V_subset_allTerms _ h1τ)
                (V_subset_allTerms _ h2τ),
              diverges_if_cond hDiv.2⟩

        | arrow σ τ uτ =>
            have hLazy' : ¬ lazy ≤ uτ := by
              simpa [Ty.outer] using hLazy
            unfold V LogicalModel.acceptable operationalModel
            simp only [hLazy']
            exact Or.inl ⟨
              allTerms_if hDiv.1
                (V_subset_allTerms _ h1τ)
                (V_subset_allTerms _ h2τ),
              diverges_if_cond hDiv.2⟩
    · rcases hNum.2.2 with ⟨n, hn⟩
      have hCondAll : AllTerms .int e₀ :=
        ⟨hNum.1, hNum.2.1⟩
      have hIfAll : AllTerms τ.erase (.ite e₀ e₁ e₂) :=
        allTerms_if hCondAll
          (V_subset_allTerms _ h1τ)
          (V_subset_allTerms _ h2τ)
      by_cases hn0 : n = 0
      · subst n
        have hEq := semEq_if_zero (σ := τ.erase) hn
          (V_subset_allTerms _ h2τ)
          hIfAll
        exact (semantic_equiv_VD (τ := τ) hEq).1.mpr h2τ
      · have hEq := semEq_if_nonzero (σ := τ.erase) hn hn0
          (V_subset_allTerms _ h1τ)
          hIfAll
        exact (semantic_equiv_VD (τ := τ) hEq).1.mpr h1τ

/-- D-side soundness of an `if` when the condition supplies the D witness. -/
theorem D_if_from_condition
    {u : Usage} {τ τ₁ τ₂ : Ty} {e₀ e₁ e₂ : Term}
    (hu : u ≤ τ.outer)
    (h0 : D (.int u) e₀)
    (h1 : V τ₁ e₁) (h2 : V τ₂ e₂)
    (hs1 : Ty.Subtype τ₁ τ) (hs2 : Ty.Subtype τ₂ τ) :
    D τ (.ite e₀ e₁ e₂) := by
  have h1τ : V τ e₁ := (semantic_subtype hs1).1 h1
  have h2τ : V τ e₂ := (semantic_subtype hs2).1 h2
  cases u with
  | unknown =>
      rw [D_int_unknown_eq_empty] at h0
      exact False.elim h0
  | lazy =>
      have hEmpty : D (.int lazy) = TermSet.empty :=
        lazy_implies_D_empty (τ := .int lazy)
          (by
            change Usage.Le lazy lazy
            exact Usage.le_refl lazy)
      rw [hEmpty] at h0
      exact False.elim h0
  | top =>
      have hτTop : τ.outer = top := Usage.le_top_iff.mp hu
      rw [D_eq_allTerms_of_outer_top hτTop]
      exact allTerms_if (D_subset_allTerms _ h0)
        (V_subset_allTerms _ h1τ)
        (V_subset_allTerms _ h2τ)
  | strict =>
      have hτ : τ.outer = strict ∨ τ.outer = top :=
        Usage.le_strict_iff.mp hu
      rcases hτ with hS | hT
      · unfold D LogicalModel.divergentSide operationalModel at h0
        simp only [not_lazy_of_outer_strict (τ := .int strict) rfl,
          Usage.not_lazy_le_strict, if_false] at h0
        apply divergentTerms_subset_D_of_outer_strict_or_top (τ := τ)
        · exact Or.inl hS
        ·
          have hAll :
              AllTerms τ.erase (.ite e₀ e₁ e₂) :=
            allTerms_if h0.1
              (V_subset_allTerms _ h1τ)
              (V_subset_allTerms _ h2τ)
          have hDiv :
              Term.Diverges (.ite e₀ e₁ e₂) :=
            diverges_if_cond h0.2
          exact And.intro hAll hDiv
      · rw [D_eq_allTerms_of_outer_top hT]
        exact allTerms_if
          (D_subset_allTerms _ h0)
          (V_subset_allTerms _ h1τ)
          (V_subset_allTerms _ h2τ)

/-- D-side soundness of an `if` when both branches supply the D witness. -/
theorem D_if_from_branches
    {u : Usage} {τ τ₁ τ₂ : Ty} {e₀ e₁ e₂ : Term}
    (hu : u ≤ τ.outer)
    (h0 : V (.int u) e₀)
    (h1 : D τ₁ e₁) (h2 : D τ₂ e₂)
    (hs1 : Ty.Subtype τ₁ τ) (hs2 : Ty.Subtype τ₂ τ) :
    D τ (.ite e₀ e₁ e₂) := by
  have h1τ : D τ e₁ := (semantic_subtype hs1).2 h1
  have h2τ : D τ e₂ := (semantic_subtype hs2).2 h2
  by_cases hFullLazy : Ty.IsLazy τ
  · rw [lazy_implies_D_empty hFullLazy] at h1τ
    exact False.elim h1τ
  · by_cases hOuterLazy : lazy ≤ τ.outer
    · have hOuter : τ.outer = lazy ∨ τ.outer = top :=
        Usage.le_lazy_iff.mp hOuterLazy
      rcases hOuter with hL | hT
      · rw [D_eq_allTerms_of_not_lazy hFullLazy (by simpa [hL] using Usage.lazy_le_lazy) ]
        exact allTerms_if
          (V_subset_allTerms _ h0)
          (D_subset_allTerms _ h1τ)
          (D_subset_allTerms _ h2τ)
      · rw [D_eq_allTerms_of_outer_top hT]
        exact allTerms_if
          (V_subset_allTerms _ h0)
          (D_subset_allTerms _ h1τ)
          (D_subset_allTerms _ h2τ)
    · have h0NonLazy : ¬ lazy ≤ u := by
        intro h
        exact hOuterLazy (Usage.le_trans h hu)
      unfold V LogicalModel.acceptable operationalModel at h0
      simp only [h0NonLazy] at h0
      rcases h0 with hDiv | hNum
      · apply divergentTerms_subset_D_of_not_lazy (τ := τ) hFullLazy
        exact ⟨allTerms_if hDiv.1
          (D_subset_allTerms _ h1τ)
          (D_subset_allTerms _ h2τ),
          diverges_if_cond hDiv.2⟩
      · rcases hNum.2.2 with ⟨n, hn⟩
        have hCondAll : AllTerms .int e₀ :=
          ⟨hNum.1, hNum.2.1⟩
        have hIfAll : AllTerms τ.erase (.ite e₀ e₁ e₂) :=
          allTerms_if hCondAll
            (D_subset_allTerms _ h1τ)
            (D_subset_allTerms _ h2τ)
        by_cases hn0 : n = 0
        · subst n
          have hEq := semEq_if_zero (σ := τ.erase) hn
            (D_subset_allTerms _ h2τ)
            hIfAll
          exact (semantic_equiv_VD (τ := τ) hEq).2.mpr h2τ
        · have hEq := semEq_if_nonzero (σ := τ.erase) hn hn0
            (D_subset_allTerms _ h1τ)
            hIfAll
          exact (semantic_equiv_VD (τ := τ) hEq).2.mpr h1τ


end Strictness
