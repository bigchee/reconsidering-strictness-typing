import Strictness.Operational.BigStep

namespace Strictness

open Term

theorem eval_deterministic_pre : ∀ {e v w}, Eval e v → Eval e w → v = w := by
  intro e v w h
  induction h generalizing w with
  | int =>
      intro h
      cases h
      rfl
  | lam =>
      intro h
      cases h
      rfl
  | pair =>
      intro h
      cases h
      rfl
  | app hFun hBody ihFun ihBody =>
      intro h2
      cases h2 with
      | app hFun2 hBody2 =>
          have hFunEq := ihFun hFun2
          cases hFunEq
          exact ihBody hBody2
  | projLeft hScrut hComp ihScrut ihComp =>
      intro h2
      cases h2 with
      | projLeft hScrut2 hComp2 =>
          have hPairEq := ihScrut hScrut2
          cases hPairEq
          exact ihComp hComp2
  | projRight hScrut hComp ihScrut ihComp =>
      intro h2
      cases h2 with
      | projRight hScrut2 hComp2 =>
          have hPairEq := ihScrut hScrut2
          cases hPairEq
          exact ihComp hComp2
  | op o h₁ h₂ ih₁ ih₂ =>
      intro h
      cases h with
      | op o h₁' h₂' =>
          have h₁Eq := ih₁ h₁'
          have h₂Eq := ih₂ h₂'
          cases h₁Eq
          cases h₂Eq
          rfl
  | ifZero hCond hZero hBranch ihCond ihBranch =>
      intro h
      cases h with
      | ifZero hCond' hZero' hBranch' =>
          have hN := ihCond hCond'
          cases hN
          exact ihBranch hBranch'
      | ifNonzero hCond' hNonzero hBranch' =>
          have hN := ihCond hCond'
          cases hN
          exfalso
          exact hNonzero hZero
  | ifNonzero hCond hNonzero hBranch ihCond ihBranch =>
      intro h
      cases h with
      | ifZero hCond' hZero hBranch' =>
          have hN := ihCond hCond'
          cases hN
          exfalso
          exact hNonzero hZero
      | ifNonzero hCond' hNonzero' hBranch' =>
          have hN := ihCond hCond'
          cases hN
          exact ihBranch hBranch'
  | letE hBody ihBody =>
      intro h
      cases h with
      | letE hBody' =>
          exact ihBody hBody'
  | fix hBody ihBody =>
      intro h
      cases h with
      | fix hBody' =>
          exact ihBody hBody'

/-- A term cannot both evaluate to a value and reach the semantic error marker. -/
theorem eval_not_evalErr : ∀ {e v}, Eval e v → ¬ EvalErr e := by
  intro e v hev
  induction hev with
  | int =>
      intro herr
      cases herr
  | lam =>
      intro herr
      cases herr
  | pair =>
      intro herr
      cases herr
  | app hFun hBody ihFun ihBody =>
      intro herr
      cases herr with
      | appFun hErrFun =>
          exact ihFun hErrFun
      | appBody hEvalFun hErrBody =>
          have hFunEq := eval_deterministic_pre hFun hEvalFun
          cases hFunEq
          exact ihBody hErrBody
  | projLeft hScrut hComp ihScrut ihComp =>
      intro herr
      cases herr with
      | projScrutinee hErrScrut =>
          exact ihScrut hErrScrut
      | projLeftComponent hEvalScrut hErrComp =>
          have hPairEq := eval_deterministic_pre hScrut hEvalScrut
          cases hPairEq
          exact ihComp hErrComp
  | projRight hScrut hComp ihScrut ihComp =>
      intro herr
      cases herr with
      | projScrutinee hErrScrut =>
          exact ihScrut hErrScrut
      | projRightComponent hEvalScrut hErrComp =>
          have hPairEq := eval_deterministic_pre hScrut hEvalScrut
          cases hPairEq
          exact ihComp hErrComp
  | op o h₁ h₂ ih₁ ih₂ =>
      intro herr
      cases herr with
      | opLeft o hErr₁ =>
          exact ih₁ hErr₁
      | opRight o hEval₁ hErr₂ =>
          exact ih₂ hErr₂
  | ifZero hCond hZero hBranch ihCond ihBranch =>
      intro herr
      cases herr with
      | ifCond hErrCond =>
          exact ihCond hErrCond
      | ifZeroBranch hEvalCond _ hErrBranch =>
          exact ihBranch hErrBranch
      | ifNonzeroBranch hEvalCond hNonzero hErrBranch =>
          have hCondEq := eval_deterministic_pre hCond hEvalCond
          cases hCondEq
          exact hNonzero hZero
  | ifNonzero hCond hNonzero hBranch ihCond ihBranch =>
      intro herr
      cases herr with
      | ifCond hErrCond =>
          exact ihCond hErrCond
      | ifNonzeroBranch hEvalCond _ hErrBranch =>
          exact ihBranch hErrBranch
      | ifZeroBranch hEvalCond hZero hErrBranch =>
          have hCondEq := eval_deterministic_pre hCond hEvalCond
          cases hCondEq
          exact hNonzero hZero
  | letE hBody ihBody =>
      intro herr
      cases herr with
      | letBody hErrBody =>
          exact ihBody hErrBody
  | fix hBody ihBody =>
      intro herr
      cases herr with
      | fix hErrBody =>
          exact ihBody hErrBody

end Strictness

namespace Strictness

open Term

/-- Determinism of the CBN big-step value semantics. -/
theorem eval_deterministic : ∀ {e v w}, Eval e v → Eval e w → v = w := by
  exact eval_deterministic_pre

end Strictness
