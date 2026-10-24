import Strictness.Semantics.SemanticEquivalence
import Strictness.Language.SimpleInstantiation

namespace Strictness

/-- A fix term and its one-step unfolding have the same value and error
observations. This does not assert termination or admissibility. -/
theorem rawEq_fix (body : Term) :
    RawEq (.fix body) (Term.instantiate body (.fix body)) := by
  constructor
  · intro v
    constructor
    · intro h
      cases h with
      | fix hBody => exact hBody
    · intro h
      exact Eval.fix h
  · constructor
    · intro h
      cases h with
      | fix hBody => exact hBody
    · intro h
      exact EvalErr.fix h

/-- One-step unfolding is typed observational equivalence for a closed,
simply typed fix term. -/
theorem semEq_fix {A : SimpleTy} {body : Term}
    (hFix : AllTerms A (.fix body)) :
    SemEq A (.fix body) (Term.instantiate body (.fix body)) := by
  have hUnfold : Term.HasType []
      (Term.instantiate body (.fix body)) A := by
    cases hFix.2 with
    | fix hBody =>
        exact hasType_instantiate_open hBody hFix.2
  have hUnfoldAll : AllTerms A
      (Term.instantiate body (.fix body)) :=
    ⟨Term.hasType_nil_closed hUnfold, hUnfold⟩
  exact ⟨hFix, hUnfoldAll, rawEq_fix body⟩

/-- Both semantic interpretations are invariant under one-step fix
unfolding, at every annotated type. -/
theorem semantic_fix_unfold_VD {τ : Ty} {body : Term}
    (hFix : AllTerms τ.erase (.fix body)) :
    (V τ (.fix body) ↔ V τ (Term.instantiate body (.fix body))) ∧
    (D τ (.fix body) ↔ D τ (Term.instantiate body (.fix body))) := by
  exact semantic_equiv_VD (τ := τ) (semEq_fix hFix)

/-- The canonical source-language loop has no finite value or error outcome. -/
theorem fix_self_diverges : Term.Diverges (.fix (.var 0)) := by
  have noValue : ∀ {e : Term} {v : Value},
      Eval e v → e = .fix (.var 0) → False := by
    intro e v h
    induction h with
    | fix hBody ih =>
        intro hEq
        cases hEq
        exact ih rfl
    | int => intro hEq; cases hEq
    | lam => intro hEq; cases hEq
    | pair => intro hEq; cases hEq
    | app hFun hBody ihFun ihBody => intro hEq; cases hEq
    | projLeft hScrut hComp ihScrut ihComp => intro hEq; cases hEq
    | projRight hScrut hComp ihScrut ihComp => intro hEq; cases hEq
    | op o hLeft hRight ihLeft ihRight => intro hEq; cases hEq
    | ifZero hCond hZero hBranch ihCond ihBranch => intro hEq; cases hEq
    | ifNonzero hCond hNonzero hBranch ihCond ihBranch => intro hEq; cases hEq
    | letE hBody ihBody => intro hEq; cases hEq
  have noError : ∀ {e : Term},
      EvalErr e → e = .fix (.var 0) → False := by
    intro e h
    induction h with
    | fix hBody ih =>
        intro hEq
        cases hEq
        exact ih rfl
    | err => intro hEq; cases hEq
    | appFun hFun ih => intro hEq; cases hEq
    | appBody hFun hBody ih => intro hEq; cases hEq
    | projScrutinee hScrut ih => intro hEq; cases hEq
    | projLeftComponent hScrut hComp ih => intro hEq; cases hEq
    | projRightComponent hScrut hComp ih => intro hEq; cases hEq
    | opLeft o hLeft ih => intro hEq; cases hEq
    | opRight o hLeft hRight ih => intro hEq; cases hEq
    | ifCond hCond ih => intro hEq; cases hEq
    | ifZeroBranch hCond hZero hBranch ih => intro hEq; cases hEq
    | ifNonzeroBranch hCond hNonzero hBranch ih => intro hEq; cases hEq
    | letBody hBody ih => intro hEq; cases hEq
  constructor
  · intro h
    rcases h with ⟨v, hv⟩
    exact noValue hv rfl
  · intro h
    exact noError h rfl

/-- The canonical loop is closed and simply typable at every simple type. -/
theorem fix_self_mem_allTerms (A : SimpleTy) :
    AllTerms A (.fix (.var 0)) := by
  constructor
  · change 0 < 1
    decide
  · exact Term.HasType.fix (Term.HasType.var rfl)

/-- The canonical loop is acceptable at every annotated type. -/
theorem fix_self_mem_V (τ : Ty) :
    V τ (.fix (.var 0)) := by
  have hDiv : DivergentTerms τ.erase (.fix (.var 0)) :=
    ⟨fix_self_mem_allTerms τ.erase, fix_self_diverges⟩
  exact divergentTerms_subset_V τ hDiv

/-- At every non-lazy type, the canonical loop is also on the D-side. -/
theorem fix_self_mem_D {τ : Ty} (hNotLazy : ¬ Ty.IsLazy τ) :
    D τ (.fix (.var 0)) := by
  have hDiv : DivergentTerms τ.erase (.fix (.var 0)) :=
    ⟨fix_self_mem_allTerms τ.erase, fix_self_diverges⟩
  exact divergentTerms_subset_D_of_not_lazy hNotLazy hDiv

/-- Closing the outer variables of a simply typed fix body gives a closed,
simply typed fix term. -/
theorem allTerms_fix_closed
    {Γ : Term.Ctx} {A : SimpleTy} {body : Term} {ρ : Substitution}
    (hBody : Term.HasType (A :: Γ) body A)
    (hρ : ∀ i σ, Term.lookup Γ i = some σ → Term.HasType [] (ρ i) σ) :
    AllTerms A (Substitution.apply ρ (.fix body)) := by
  have hTyped : Term.HasType [] (Substitution.apply ρ (.fix body)) A :=
    Term.hasType_apply (Term.HasType.fix hBody) hρ
  exact ⟨Term.hasType_nil_closed hTyped, hTyped⟩

/-- Closing a fix term is observationally equivalent to closing its body
with the recursive variable mapped to the resulting closed fix term. -/
theorem semEq_fix_closed
    {A : SimpleTy} (ρ : Substitution) (body : Term)
    (hρ : ∀ i, Term.Closed (ρ i))
    (hFix : AllTerms A (Substitution.apply ρ (.fix body))) :
    SemEq A
      (Substitution.apply ρ (.fix body))
      (Substitution.apply
        (Substitution.extend ρ (Substitution.apply ρ (.fix body))) body) := by
  rw [Substitution.apply_extend_eq_instantiate_of_closed
    ρ (Substitution.apply ρ (.fix body)) body hρ hFix.1]
  exact semEq_fix hFix

/-- The closing-substitution form of fix unfolding preserves V and D. -/
theorem semantic_fix_closed_VD
    {τ : Ty} (ρ : Substitution) (body : Term)
    (hρ : ∀ i, Term.Closed (ρ i))
    (hFix : AllTerms τ.erase (Substitution.apply ρ (.fix body))) :
    (V τ (Substitution.apply ρ (.fix body)) ↔
      V τ (Substitution.apply
        (Substitution.extend ρ (Substitution.apply ρ (.fix body))) body)) ∧
    (D τ (Substitution.apply ρ (.fix body)) ↔
      D τ (Substitution.apply
        (Substitution.extend ρ (Substitution.apply ρ (.fix body))) body)) := by
  exact semantic_equiv_VD (τ := τ) (semEq_fix_closed ρ body hρ hFix)

end Strictness
