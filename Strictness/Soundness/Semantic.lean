import Strictness.Soundness.Fundamental

namespace Strictness

open Usage
open Term

/-- The semantic substitution obtained from an S-annotated single variable is
valid whenever the substituted closed term is on the variable's D-side. -/
theorem valid_single_of_D
    {σ : Ty} {a : Term}
    (ha : D (σ.reannotate strict) a) :
    Valid [σ.reannotate strict] (singleSubst a) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact D_closed ha
  · intro i τ hLookup
    cases i with
    | zero =>
        simp only [Env.lookup] at hLookup
        cases hLookup
        exact D_subset_V (σ.reannotate strict) ha
    | succ i =>
        simp only [Env.lookup] at hLookup
        cases hLookup

/-- An `err` term is a valid V-substitution for an L-annotated single
variable, because the whole V-set of an outer-L type is the erased simple-type
set. -/
theorem valid_single_err_lazy
    {σ : Ty} :
    Valid [σ.reannotate lazy] (singleSubst .err) := by
  refine ⟨?_, ?_⟩
  · intro i
    trivial
  · intro i τ hLookup
    cases i with
    | zero =>
        simp only [Env.lookup] at hLookup
        cases hLookup
        rw [V_reannotate_lazy_eq_allTerms σ]
        exact ⟨by trivial, Term.HasType.err⟩
    | succ i =>
        simp only [Env.lookup] at hLookup
        cases hLookup

/-- `err` also satisfies the D-side of an outer-⊤ single-variable type. -/
theorem satisfiesD_single_err_top
    {σ : Ty} :
    SatisfiesD [σ.reannotate top] (singleSubst .err) := by
  refine ⟨0, σ.reannotate top, rfl, ?_⟩
  rw [D_reannotate_top_eq_allTerms σ]
  exact ⟨by trivial, Term.HasType.err⟩

/-- Strict case in a semantic form: replacing the single free
variable by any D-admissible closed term makes the result diverge. -/
theorem strict_semantic
    {σ : Ty} {e : Term}
    (hTyping : Typing [σ.reannotate strict] e (.int strict))
    {a : Term}
    (ha : D (σ.reannotate strict) a) :
    Term.Diverges (Substitution.apply (singleSubst a) e) := by
  have hValid := valid_single_of_D ha
  have hDenv : SatisfiesD [σ.reannotate strict] (singleSubst a) := by
    exact ⟨0, σ.reannotate strict, rfl, ha⟩
  have hFund := fundamental hTyping (singleSubst a) hValid
  have hD := hFund.2 hDenv
  unfold D LogicalModel.divergentSide operationalModel at hD
  have hDivergent : DivergentTerms .int
      (Substitution.apply (singleSubst a) e) := by
    simpa only [not_lazy_of_outer_strict (τ := .int strict) rfl,
      Usage.not_lazy_le_strict, if_false] using hD
  exact hDivergent.2

/-- If an expression typed with an outer-L single variable has result type
`Int^S`, replacing that variable by `err` cannot itself evaluate to `err`.
This is the semantic core needed for the lazy observation case. -/
theorem lazy_no_error
    {σ : Ty} {e : Term}
    (hTyping : Typing [σ.reannotate lazy] e (.int strict)) :
    ¬ EvalErr (Substitution.apply (singleSubst .err) e) := by
  have hValid := valid_single_err_lazy (σ := σ)
  have hFund := fundamental hTyping (singleSubst .err) hValid
  have hV := hFund.1
  unfold V LogicalModel.acceptable operationalModel at hV
  simp only [Usage.not_lazy_le_strict] at hV
  rcases hV with hDiv | hNum
  · exact hDiv.2.2
  · rcases hNum.2.2 with ⟨n, hn⟩
    exact (eval_not_evalErr (e := Substitution.apply (singleSubst .err) e)
      (v := .int n) hn)

/-- Top case in semantic form: replacing the single free variable by
`err` yields divergence at the final strict integer observation. -/
theorem top_semantic
    {σ : Ty} {e : Term}
    (hTyping : Typing [σ.reannotate top] e (.int strict)) :
    Term.Diverges (Substitution.apply (singleSubst .err) e) := by
  have hValid : Valid [σ.reannotate top] (singleSubst .err) := by
    refine ⟨?_, ?_⟩
    · intro i
      trivial
    · intro i τ hLookup
      cases i with
      | zero =>
          simp only [Env.lookup] at hLookup
          cases hLookup
          rw [V_reannotate_top_eq_allTerms σ]
          exact ⟨by trivial, Term.HasType.err⟩
      | succ i =>
          simp only [Env.lookup] at hLookup
          cases hLookup
  have hDenv := satisfiesD_single_err_top (σ := σ)
  have hFund := fundamental hTyping (singleSubst .err) hValid
  have hD := hFund.2 hDenv
  unfold D LogicalModel.divergentSide operationalModel at hD
  have hDivergent : DivergentTerms .int
      (Substitution.apply (singleSubst .err) e) := by
    simpa only [not_lazy_of_outer_strict (τ := .int strict) rfl,
      Usage.not_lazy_le_strict, if_false] using hD
  exact hDivergent.2

end Strictness
