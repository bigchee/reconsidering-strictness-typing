import Strictness.Semantics.TermApproximation

namespace Strictness

namespace Term

/-- Structural approximation is transitive. -/
theorem Approx.trans {e₁ e₂ e₃ : Term}
    (h₁₂ : Approx e₁ e₂) (h₂₃ : Approx e₂ e₃) : Approx e₁ e₃ := by
  induction h₁₂ generalizing e₃ with
  | bottom => exact Approx.bottom
  | var i => cases h₂₃; exact Approx.var i
  | int n => cases h₂₃; exact Approx.int n
  | err => cases h₂₃; exact Approx.err
  | lam h ih =>
      cases h₂₃ with
      | lam h' => exact Approx.lam (ih h')
  | fix h ih =>
      cases h₂₃ with
      | fix h' => exact Approx.fix (ih h')
  | app hf ha ihf iha =>
      cases h₂₃ with
      | app hf' ha' => exact Approx.app (ihf hf') (iha ha')
  | pair ha hb iha ihb =>
      cases h₂₃ with
      | pair ha' hb' => exact Approx.pair (iha ha') (ihb hb')
  | proj h ih =>
      cases h₂₃ with
      | proj h' => exact Approx.proj (ih h')
  | op o ha hb iha ihb =>
      cases h₂₃ with
      | op o ha' hb' => exact Approx.op o (iha ha') (ihb hb')
  | ite hc ht hf ihc iht ihf =>
      cases h₂₃ with
      | ite hc' ht' hf' => exact Approx.ite (ihc hc') (iht ht') (ihf hf')
  | letE ha hb iha ihb =>
      cases h₂₃ with
      | letE ha' hb' => exact Approx.letE (iha ha') (ihb hb')

/-- Each finite unfolding structurally approximates the next one. -/
theorem fixApprox_step (body : Term) (n : Nat) :
    Approx (fixApprox body n) (fixApprox body (n + 1)) := by
  induction n with
  | zero => exact Approx.bottom
  | succ n ih =>
      exact Approx.instantiate (Approx.refl body) ih

/-- Finite unfoldings are monotone in their unfolding depth. -/
theorem fixApprox_mono (body : Term) {n m : Nat} (h : n ≤ m) :
    Approx (fixApprox body n) (fixApprox body m) := by
  induction m generalizing n with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero h
      subst n
      exact Approx.refl _
  | succ m ih =>
      by_cases hn : n = m + 1
      · subst n
        exact Approx.refl _
      · have hnm : n ≤ m := by omega
        exact Approx.trans (ih hnm) (fixApprox_step body m)

end Term

namespace Value

/-- Approximation of weak-head values retains the outer value constructor.
Integer values agree; pair components and lambda bodies may gain information. -/
inductive Approx : Value → Value → Prop where
  | int (n : Int) : Approx (.int n) (.int n)
  | pair {a a' b b' : Term} :
      Term.Approx a a' → Term.Approx b b' →
      Approx (.pair a b) (.pair a' b')
  | lam {body body' : Term} :
      Term.Approx body body' → Approx (.lam body) (.lam body')

end Value

/-- A finite value evaluation survives replacing omega subterms by more
informative terms. Retained unevaluated terms are related by Value.Approx. -/
theorem eval_approx
    {e e' : Term} {v : Value}
    (hEval : Eval e v) (hApprox : Term.Approx e e') :
    ∃ v', Eval e' v' ∧ Value.Approx v v' := by
  induction hEval generalizing e' with
  | int =>
      cases hApprox with
      | int => exact ⟨_, Eval.int, Value.Approx.int _⟩
  | lam =>
      cases hApprox with
      | lam hBody => exact ⟨_, Eval.lam, Value.Approx.lam hBody⟩
  | pair =>
      cases hApprox with
      | pair hLeft hRight =>
          exact ⟨_, Eval.pair, Value.Approx.pair hLeft hRight⟩
  | app hFun hBody ihFun ihBody =>
      cases hApprox with
      | app hFunApprox hArgApprox =>
          rcases ihFun hFunApprox with ⟨vFun, hFun', hFunValue⟩
          cases hFunValue with
          | lam hBodyApprox =>
              have hInst := Term.Approx.instantiate hBodyApprox hArgApprox
              rcases ihBody hInst with ⟨v', hBody', hValue⟩
              exact ⟨v', Eval.app hFun' hBody', hValue⟩
  | projLeft hScrut hComp ihScrut ihComp =>
      cases hApprox with
      | proj hScrutApprox =>
          rcases ihScrut hScrutApprox with ⟨vPair, hPair', hPairValue⟩
          cases hPairValue with
          | pair hLeftApprox hRightApprox =>
              rcases ihComp hLeftApprox with ⟨v', hComp', hValue⟩
              exact ⟨v', Eval.projLeft hPair' hComp', hValue⟩
  | projRight hScrut hComp ihScrut ihComp =>
      cases hApprox with
      | proj hScrutApprox =>
          rcases ihScrut hScrutApprox with ⟨vPair, hPair', hPairValue⟩
          cases hPairValue with
          | pair hLeftApprox hRightApprox =>
              rcases ihComp hRightApprox with ⟨v', hComp', hValue⟩
              exact ⟨v', Eval.projRight hPair' hComp', hValue⟩
  | op o hLeft hRight ihLeft ihRight =>
      cases hApprox with
      | op o hLeftApprox hRightApprox =>
          rcases ihLeft hLeftApprox with ⟨vLeft, hLeft', hLeftValue⟩
          rcases ihRight hRightApprox with ⟨vRight, hRight', hRightValue⟩
          cases hLeftValue with
          | int nLeft =>
              cases hRightValue with
              | int nRight =>
                  exact ⟨_, Eval.op o hLeft' hRight', Value.Approx.int _⟩
  | ifZero hCond hZero hBranch ihCond ihBranch =>
      cases hApprox with
      | ite hCondApprox hThenApprox hElseApprox =>
          rcases ihCond hCondApprox with ⟨vCond, hCond', hCondValue⟩
          cases hCondValue with
          | int n =>
              rcases ihBranch hElseApprox with ⟨v', hBranch', hValue⟩
              exact ⟨v', Eval.ifZero hCond' hZero hBranch', hValue⟩
  | ifNonzero hCond hNonzero hBranch ihCond ihBranch =>
      cases hApprox with
      | ite hCondApprox hThenApprox hElseApprox =>
          rcases ihCond hCondApprox with ⟨vCond, hCond', hCondValue⟩
          cases hCondValue with
          | int n =>
              rcases ihBranch hThenApprox with ⟨v', hBranch', hValue⟩
              exact ⟨v', Eval.ifNonzero hCond' hNonzero hBranch', hValue⟩
  | letE hBody ihBody =>
      cases hApprox with
      | letE hDefApprox hBodyApprox =>
          have hInst := Term.Approx.instantiate hBodyApprox hDefApprox
          rcases ihBody hInst with ⟨v', hBody', hValue⟩
          exact ⟨v', Eval.letE hBody', hValue⟩
  | fix hBody ihBody =>
      cases hApprox with
      | fix hBodyApprox =>
          have hInst := Term.Approx.instantiate hBodyApprox (Term.Approx.fix hBodyApprox)
          rcases ihBody hInst with ⟨v', hBody', hValue⟩
          exact ⟨v', Eval.fix hBody', hValue⟩

/-- A finite error evaluation also survives structural approximation. -/
theorem evalErr_approx
    {e e' : Term}
    (hErr : EvalErr e) (hApprox : Term.Approx e e') : EvalErr e' := by
  induction hErr generalizing e' with
  | err =>
      cases hApprox with
      | err => exact EvalErr.err
  | appFun hFun ihFun =>
      cases hApprox with
      | app hFunApprox hArgApprox =>
          exact EvalErr.appFun (ihFun hFunApprox)
  | appBody hFun hBody ihBody =>
      cases hApprox with
      | app hFunApprox hArgApprox =>
          rcases eval_approx hFun hFunApprox with ⟨vFun, hFun', hFunValue⟩
          cases hFunValue with
          | lam hBodyApprox =>
              exact EvalErr.appBody hFun'
                (ihBody (Term.Approx.instantiate hBodyApprox hArgApprox))
  | projScrutinee hScrut ihScrut =>
      cases hApprox with
      | proj hScrutApprox =>
          exact EvalErr.projScrutinee (ihScrut hScrutApprox)
  | projLeftComponent hScrut hComp ihComp =>
      cases hApprox with
      | proj hScrutApprox =>
          rcases eval_approx hScrut hScrutApprox with ⟨vPair, hPair', hPairValue⟩
          cases hPairValue with
          | pair hLeftApprox hRightApprox =>
              exact EvalErr.projLeftComponent hPair' (ihComp hLeftApprox)
  | projRightComponent hScrut hComp ihComp =>
      cases hApprox with
      | proj hScrutApprox =>
          rcases eval_approx hScrut hScrutApprox with ⟨vPair, hPair', hPairValue⟩
          cases hPairValue with
          | pair hLeftApprox hRightApprox =>
              exact EvalErr.projRightComponent hPair' (ihComp hRightApprox)
  | opLeft o hLeft ihLeft =>
      cases hApprox with
      | op o hLeftApprox hRightApprox =>
          exact EvalErr.opLeft o (ihLeft hLeftApprox)
  | opRight o hLeft hRight ihRight =>
      cases hApprox with
      | op o hLeftApprox hRightApprox =>
          rcases eval_approx hLeft hLeftApprox with ⟨vLeft, hLeft', hLeftValue⟩
          cases hLeftValue with
          | int n => exact EvalErr.opRight o hLeft' (ihRight hRightApprox)
  | ifCond hCond ihCond =>
      cases hApprox with
      | ite hCondApprox hThenApprox hElseApprox =>
          exact EvalErr.ifCond (ihCond hCondApprox)
  | ifZeroBranch hCond hZero hBranch ihBranch =>
      cases hApprox with
      | ite hCondApprox hThenApprox hElseApprox =>
          rcases eval_approx hCond hCondApprox with ⟨vCond, hCond', hCondValue⟩
          cases hCondValue with
          | int n => exact EvalErr.ifZeroBranch hCond' hZero (ihBranch hElseApprox)
  | ifNonzeroBranch hCond hNonzero hBranch ihBranch =>
      cases hApprox with
      | ite hCondApprox hThenApprox hElseApprox =>
          rcases eval_approx hCond hCondApprox with ⟨vCond, hCond', hCondValue⟩
          cases hCondValue with
          | int n => exact EvalErr.ifNonzeroBranch hCond' hNonzero (ihBranch hThenApprox)
  | letBody hBody ihBody =>
      cases hApprox with
      | letE hDefApprox hBodyApprox =>
          exact EvalErr.letBody (ihBody (Term.Approx.instantiate hBodyApprox hDefApprox))
  | fix hBody ihBody =>
      cases hApprox with
      | fix hBodyApprox =>
          exact EvalErr.fix
            (ihBody (Term.Approx.instantiate hBodyApprox (Term.Approx.fix hBodyApprox)))

end Strictness
