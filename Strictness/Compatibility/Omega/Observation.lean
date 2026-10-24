import Strictness.Compatibility.Omega.Representation
import Strictness.Compatibility.Operational

/-!
Value, error and divergence observations under loop representation changes.

Related values have the same head constructor but may differ in retained
syntax. Complete expansion therefore translates the resulting value as well
as the input term. Finite observations need no typing assumption. Infinite
execution is preserved and reflected for closed simply typed terms.
-/

namespace Strictness

namespace Value

/-- Related values retain their outer constructor and differ only in selected
representations of the divergence marker inside retained terms. -/
inductive OmegaEq : Value → Value → Prop where
  | int (n : Int) : OmegaEq (.int n) (.int n)
  | pair {a a' b b' : Term} :
      Term.OmegaEq a a' → Term.OmegaEq b b' →
      OmegaEq (.pair a b) (.pair a' b')
  | lam {body body' : Term} :
      Term.OmegaEq body body' → OmegaEq (.lam body) (.lam body')

end Value

/-- A finite value evaluation survives changing selected representations of
the divergence marker. Retained unevaluated terms are related by Value.OmegaEq. -/
theorem eval_omegaEq
    {e e' : Term} {v : Value}
    (hEval : Eval e v) (hOmegaEq : Term.OmegaEq e e') :
    ∃ v', Eval e' v' ∧ Value.OmegaEq v v' := by
  induction hEval generalizing e' with
  | int =>
      cases hOmegaEq with
      | int => exact ⟨_, Eval.int, Value.OmegaEq.int _⟩
  | lam =>
      cases hOmegaEq with
      | lam hBody => exact ⟨_, Eval.lam, Value.OmegaEq.lam hBody⟩
  | pair =>
      cases hOmegaEq with
      | pair hLeft hRight =>
          exact ⟨_, Eval.pair, Value.OmegaEq.pair hLeft hRight⟩
  | app hFun hBody ihFun ihBody =>
      cases hOmegaEq with
      | app hFunOmegaEq hArgOmegaEq =>
          rcases ihFun hFunOmegaEq with ⟨vFun, hFun', hFunValue⟩
          cases hFunValue with
          | lam hBodyOmegaEq =>
              have hInst := Term.OmegaEq.instantiate hBodyOmegaEq hArgOmegaEq
              rcases ihBody hInst with ⟨v', hBody', hValue⟩
              exact ⟨v', Eval.app hFun' hBody', hValue⟩
  | projLeft hScrut hComp ihScrut ihComp =>
      cases hOmegaEq with
      | proj hScrutOmegaEq =>
          rcases ihScrut hScrutOmegaEq with ⟨vPair, hPair', hPairValue⟩
          cases hPairValue with
          | pair hLeftOmegaEq hRightOmegaEq =>
              rcases ihComp hLeftOmegaEq with ⟨v', hComp', hValue⟩
              exact ⟨v', Eval.projLeft hPair' hComp', hValue⟩
  | projRight hScrut hComp ihScrut ihComp =>
      cases hOmegaEq with
      | proj hScrutOmegaEq =>
          rcases ihScrut hScrutOmegaEq with ⟨vPair, hPair', hPairValue⟩
          cases hPairValue with
          | pair hLeftOmegaEq hRightOmegaEq =>
              rcases ihComp hRightOmegaEq with ⟨v', hComp', hValue⟩
              exact ⟨v', Eval.projRight hPair' hComp', hValue⟩
  | op o hLeft hRight ihLeft ihRight =>
      cases hOmegaEq with
      | op o hLeftOmegaEq hRightOmegaEq =>
          rcases ihLeft hLeftOmegaEq with ⟨vLeft, hLeft', hLeftValue⟩
          rcases ihRight hRightOmegaEq with ⟨vRight, hRight', hRightValue⟩
          cases hLeftValue with
          | int nLeft =>
              cases hRightValue with
              | int nRight =>
                  exact ⟨_, Eval.op o hLeft' hRight', Value.OmegaEq.int _⟩
  | ifZero hCond hZero hBranch ihCond ihBranch =>
      cases hOmegaEq with
      | ite hCondOmegaEq hThenOmegaEq hElseOmegaEq =>
          rcases ihCond hCondOmegaEq with ⟨vCond, hCond', hCondValue⟩
          cases hCondValue with
          | int n =>
              rcases ihBranch hElseOmegaEq with ⟨v', hBranch', hValue⟩
              exact ⟨v', Eval.ifZero hCond' hZero hBranch', hValue⟩
  | ifNonzero hCond hNonzero hBranch ihCond ihBranch =>
      cases hOmegaEq with
      | ite hCondOmegaEq hThenOmegaEq hElseOmegaEq =>
          rcases ihCond hCondOmegaEq with ⟨vCond, hCond', hCondValue⟩
          cases hCondValue with
          | int n =>
              rcases ihBranch hThenOmegaEq with ⟨v', hBranch', hValue⟩
              exact ⟨v', Eval.ifNonzero hCond' hNonzero hBranch', hValue⟩
  | letE hBody ihBody =>
      cases hOmegaEq with
      | letE hDefOmegaEq hBodyOmegaEq =>
          have hInst := Term.OmegaEq.instantiate hBodyOmegaEq hDefOmegaEq
          rcases ihBody hInst with ⟨v', hBody', hValue⟩
          exact ⟨v', Eval.letE hBody', hValue⟩
  | fix hBody ihBody =>
      cases hOmegaEq with
      | contract => exact False.elim (fix_self_diverges.1 ⟨_, Eval.fix hBody⟩)
      | fix hBodyOmegaEq =>
          have hInst := Term.OmegaEq.instantiate hBodyOmegaEq (Term.OmegaEq.fix hBodyOmegaEq)
          rcases ihBody hInst with ⟨v', hBody', hValue⟩
          exact ⟨v', Eval.fix hBody', hValue⟩

/-- Error evaluation is preserved by replacement of divergence markers. -/
theorem evalErr_omegaEq
    {e e' : Term}
    (hErr : EvalErr e) (hOmegaEq : Term.OmegaEq e e') : EvalErr e' := by
  induction hErr generalizing e' with
  | err =>
      cases hOmegaEq with
      | err => exact EvalErr.err
  | appFun hFun ihFun =>
      cases hOmegaEq with
      | app hFunOmegaEq hArgOmegaEq =>
          exact EvalErr.appFun (ihFun hFunOmegaEq)
  | appBody hFun hBody ihBody =>
      cases hOmegaEq with
      | app hFunOmegaEq hArgOmegaEq =>
          rcases eval_omegaEq hFun hFunOmegaEq with ⟨vFun, hFun', hFunValue⟩
          cases hFunValue with
          | lam hBodyOmegaEq =>
              exact EvalErr.appBody hFun'
                (ihBody (Term.OmegaEq.instantiate hBodyOmegaEq hArgOmegaEq))
  | projScrutinee hScrut ihScrut =>
      cases hOmegaEq with
      | proj hScrutOmegaEq =>
          exact EvalErr.projScrutinee (ihScrut hScrutOmegaEq)
  | projLeftComponent hScrut hComp ihComp =>
      cases hOmegaEq with
      | proj hScrutOmegaEq =>
          rcases eval_omegaEq hScrut hScrutOmegaEq with ⟨vPair, hPair', hPairValue⟩
          cases hPairValue with
          | pair hLeftOmegaEq hRightOmegaEq =>
              exact EvalErr.projLeftComponent hPair' (ihComp hLeftOmegaEq)
  | projRightComponent hScrut hComp ihComp =>
      cases hOmegaEq with
      | proj hScrutOmegaEq =>
          rcases eval_omegaEq hScrut hScrutOmegaEq with ⟨vPair, hPair', hPairValue⟩
          cases hPairValue with
          | pair hLeftOmegaEq hRightOmegaEq =>
              exact EvalErr.projRightComponent hPair' (ihComp hRightOmegaEq)
  | opLeft o hLeft ihLeft =>
      cases hOmegaEq with
      | op o hLeftOmegaEq hRightOmegaEq =>
          exact EvalErr.opLeft o (ihLeft hLeftOmegaEq)
  | opRight o hLeft hRight ihRight =>
      cases hOmegaEq with
      | op o hLeftOmegaEq hRightOmegaEq =>
          rcases eval_omegaEq hLeft hLeftOmegaEq with ⟨vLeft, hLeft', hLeftValue⟩
          cases hLeftValue with
          | int n => exact EvalErr.opRight o hLeft' (ihRight hRightOmegaEq)
  | ifCond hCond ihCond =>
      cases hOmegaEq with
      | ite hCondOmegaEq hThenOmegaEq hElseOmegaEq =>
          exact EvalErr.ifCond (ihCond hCondOmegaEq)
  | ifZeroBranch hCond hZero hBranch ihBranch =>
      cases hOmegaEq with
      | ite hCondOmegaEq hThenOmegaEq hElseOmegaEq =>
          rcases eval_omegaEq hCond hCondOmegaEq with ⟨vCond, hCond', hCondValue⟩
          cases hCondValue with
          | int n => exact EvalErr.ifZeroBranch hCond' hZero (ihBranch hElseOmegaEq)
  | ifNonzeroBranch hCond hNonzero hBranch ihBranch =>
      cases hOmegaEq with
      | ite hCondOmegaEq hThenOmegaEq hElseOmegaEq =>
          rcases eval_omegaEq hCond hCondOmegaEq with ⟨vCond, hCond', hCondValue⟩
          cases hCondValue with
          | int n => exact EvalErr.ifNonzeroBranch hCond' hNonzero (ihBranch hThenOmegaEq)
  | letBody hBody ihBody =>
      cases hOmegaEq with
      | letE hDefOmegaEq hBodyOmegaEq =>
          exact EvalErr.letBody (ihBody (Term.OmegaEq.instantiate hBodyOmegaEq hDefOmegaEq))
  | fix hBody ihBody =>
      cases hOmegaEq with
      | contract => exact False.elim (fix_self_diverges.2 (EvalErr.fix hBody))
      | fix hBodyOmegaEq =>
          exact EvalErr.fix
            (ihBody (Term.OmegaEq.instantiate hBodyOmegaEq (Term.OmegaEq.fix hBodyOmegaEq)))

theorem omegaEq_evalErr_iff {e e' : Term} (h : Term.OmegaEq e e') :
    EvalErr e ↔ EvalErr e' := ⟨fun he => evalErr_omegaEq he h, fun he => evalErr_omegaEq he h.symm⟩

theorem omegaEq_diverges_iff {e e' : Term} (h : Term.OmegaEq e e') :
    Term.Diverges e ↔ Term.Diverges e' := by
  have forward : ∀ {a b : Term}, Term.OmegaEq a b → Term.Diverges a → Term.Diverges b := by
    intro a b hab hd
    constructor
    · rintro ⟨v, hv⟩
      rcases eval_omegaEq hv hab.symm with ⟨w, hw, _⟩
      exact hd.1 ⟨w, hw⟩
    · intro he
      exact hd.2 (evalErr_omegaEq he hab.symm)
  exact ⟨forward h, forward h.symm⟩

theorem omegaEq_infiniteSteps_iff {e e' : Term} {A : SimpleTy}
    (h : Term.OmegaEq e e') (ht : Term.HasType [] e A) :
    InfiniteSteps e ↔ InfiniteSteps e' := by
  rw [← diverges_iff_infiniteSteps ht, ← diverges_iff_infiniteSteps (h.hasType ht)]
  exact omegaEq_diverges_iff h

namespace Value

def expandOmega : Value → Value
  | .int n => .int n
  | .lam b => .lam b.expandOmega
  | .pair a b => .pair a.expandOmega b.expandOmega

end Value

theorem eval_expandOmega {e : Term} {v : Value} (h : Eval e v) :
    Eval e.expandOmega v.expandOmega := by
  induction h with
  | int => exact .int
  | lam => exact .lam
  | pair => exact .pair
  | app hf hb ihf ihb =>
    exact .app ihf (by simpa only [Term.expandOmega_instantiate] using ihb)
  | projLeft hp hc ihp ihc => exact .projLeft ihp ihc
  | projRight hp hc ihp ihc => exact .projRight ihp ihc
  | op o hl hr ihl ihr => exact .op o ihl ihr
  | ifZero hc hn hb ihc ihb => exact .ifZero ihc hn ihb
  | ifNonzero hc hn hb ihc ihb => exact .ifNonzero ihc hn ihb
  | letE hb ihb => exact .letE (by simpa only [Term.expandOmega_instantiate] using ihb)
  | fix hb ihb => exact .fix (by simpa only [Term.expandOmega_instantiate, Term.expandOmega] using ihb)

/-- The translated value is determined exactly, including all retained syntax. -/
theorem eval_expandOmega_iff {e : Term} {w : Value} :
    Eval e.expandOmega w ↔ ∃ v, Eval e v ∧ v.expandOmega = w := by
  constructor
  · intro h
    rcases eval_omegaEq h (Term.omegaEq_expandOmega e).symm with ⟨v, hv, _⟩
    exact ⟨v, hv, eval_deterministic (eval_expandOmega hv) h⟩
  · rintro ⟨v, hv, rfl⟩
    exact eval_expandOmega hv

theorem evalErr_expandOmega_iff (e : Term) : EvalErr e.expandOmega ↔ EvalErr e :=
  (omegaEq_evalErr_iff (Term.omegaEq_expandOmega e)).symm

theorem diverges_expandOmega_iff (e : Term) : Term.Diverges e.expandOmega ↔ Term.Diverges e :=
  (omegaEq_diverges_iff (Term.omegaEq_expandOmega e)).symm

theorem steps_value_expandOmega_iff {e : Term} {w : Value} :
    Steps e.expandOmega w.toTerm ↔ ∃ v : Value, Steps e v.toTerm ∧ v.expandOmega = w := by
  simp only [← eval_iff_steps_value]
  exact eval_expandOmega_iff

theorem steps_error_expandOmega_iff (e : Term) :
    (∃ E : EvalCtx, Steps e.expandOmega (E.plug .err)) ↔
    (∃ E : EvalCtx, Steps e (E.plug .err)) := by
  rw [← evalErr_iff_steps_error, ← evalErr_iff_steps_error]
  exact evalErr_expandOmega_iff e

theorem infiniteSteps_expandOmega_iff {e : Term} {A : SimpleTy} (ht : Term.HasType [] e A) :
    InfiniteSteps e.expandOmega ↔ InfiniteSteps e :=
  (omegaEq_infiniteSteps_iff (Term.omegaEq_expandOmega e) ht).symm

/-- The two isolated loop terms also agree in the existing exact-value equivalence. -/
theorem omega_rawEq_fix_self : RawEq .omega (.fix (.var 0)) := by
  constructor
  · intro v
    exact ⟨fun h => False.elim (Term.omega_diverges.1 ⟨v, h⟩),
      fun h => False.elim (fix_self_diverges.1 ⟨v, h⟩)⟩
  · exact omegaEq_evalErr_iff Term.OmegaEq.expand

theorem omega_semEq_fix_self (A : SimpleTy) : SemEq A .omega (.fix (.var 0)) :=
  ⟨omega_mem_allTerms A, fix_self_mem_allTerms A, omega_rawEq_fix_self⟩

end Strictness
