import Strictness.Semantics.ApproximationEvaluation

namespace Strictness

namespace Term

/-- Increasing the number of surrounding binders preserves well-scoping. -/
theorem closedAt_mono {d d' : Nat} {e : Term}
    (h : ClosedAt d e) (hle : d ≤ d') : ClosedAt d' e := by
  induction e generalizing d d' with
  | var i => exact Nat.lt_of_lt_of_le h hle
  | int n => trivial
  | lam body ih => exact ih h (Nat.succ_le_succ hle)
  | fix body ih => exact ih h (Nat.succ_le_succ hle)
  | app a b iha ihb => exact ⟨iha h.1 hle, ihb h.2 hle⟩
  | pair a b iha ihb => exact ⟨iha h.1 hle, ihb h.2 hle⟩
  | proj b e ih => exact ih h hle
  | op o a b iha ihb => exact ⟨iha h.1 hle, ihb h.2 hle⟩
  | ite c t f ihc iht ihf => exact ⟨ihc h.1 hle, iht h.2.1 hle, ihf h.2.2 hle⟩
  | letE a b iha ihb => exact ⟨iha h.1 hle, ihb h.2 (Nat.succ_le_succ hle)⟩
  | omega => trivial
  | err => trivial

end Term

/-- A family of terms obtained by replacing selected occurrences of a closed
fix term by finite unfoldings. Each selected occurrence may have a fixed
finite delay k: its n-th approximation is fixApprox body (n-k).
The delay is needed because observing a fix consumes one unfolding. -/
inductive UnfoldFamily (body : Term) : (Nat → Term) → Term → Prop where
  | hole (k : Nat) :
      UnfoldFamily body (fun n => Term.fixApprox body (n - k)) (.fix body)
  | var (i : Nat) : UnfoldFamily body (fun _ => .var i) (.var i)
  | int (n : Int) : UnfoldFamily body (fun _ => .int n) (.int n)
  | omega : UnfoldFamily body (fun _ => .omega) .omega
  | err : UnfoldFamily body (fun _ => .err) .err
  | lam {f : Nat → Term} {e : Term} :
      UnfoldFamily body f e → UnfoldFamily body (fun n => .lam (f n)) (.lam e)
  | fix {f : Nat → Term} {e : Term} :
      UnfoldFamily body f e → UnfoldFamily body (fun n => .fix (f n)) (.fix e)
  | app {f g : Nat → Term} {e a : Term} :
      UnfoldFamily body f e → UnfoldFamily body g a →
      UnfoldFamily body (fun n => .app (f n) (g n)) (.app e a)
  | pair {f g : Nat → Term} {e a : Term} :
      UnfoldFamily body f e → UnfoldFamily body g a →
      UnfoldFamily body (fun n => .pair (f n) (g n)) (.pair e a)
  | proj {b : Bool} {f : Nat → Term} {e : Term} :
      UnfoldFamily body f e → UnfoldFamily body (fun n => .proj b (f n)) (.proj b e)
  | op (o : PrimOp) {f g : Nat → Term} {e a : Term} :
      UnfoldFamily body f e → UnfoldFamily body g a →
      UnfoldFamily body (fun n => .op o (f n) (g n)) (.op o e a)
  | ite {f g h : Nat → Term} {c t e : Term} :
      UnfoldFamily body f c → UnfoldFamily body g t → UnfoldFamily body h e →
      UnfoldFamily body (fun n => .ite (f n) (g n) (h n)) (.ite c t e)
  | letE {f g : Nat → Term} {e a : Term} :
      UnfoldFamily body f e → UnfoldFamily body g a →
      UnfoldFamily body (fun n => .letE (f n) (g n)) (.letE e a)

namespace UnfoldFamily

/-- Unselected syntax is constant throughout the family. -/
theorem const (body e : Term) : UnfoldFamily body (fun _ => e) e := by
  induction e with
  | var i => exact .var i
  | int n => exact .int n
  | lam e ih => exact .lam ih
  | fix e ih => exact .fix ih
  | app e a ihe iha => exact .app ihe iha
  | pair e a ihe iha => exact .pair ihe iha
  | proj b e ih => exact .proj ih
  | op o e a ihe iha => exact .op o ihe iha
  | ite c t e ihc iht ihe => exact .ite ihc iht ihe
  | letE e a ihe iha => exact .letE ihe iha
  | omega => exact .omega
  | err => exact .err

/-- Closed selected fix terms are unaffected by shifts under binders. -/
theorem shift {A : SimpleTy} {body : Term} {f : Nat → Term} {e : Term}
    (hFix : AllTerms A (.fix body)) (h : UnfoldFamily body f e)
    (amount cutoff : Nat) :
    UnfoldFamily body (fun n => Term.shift amount cutoff (f n))
      (Term.shift amount cutoff e) := by
  induction h generalizing cutoff with
  | hole k =>
      have hf : (fun n => Term.shift amount cutoff (Term.fixApprox body (n - k))) =
          (fun n => Term.fixApprox body (n - k)) := by
        funext n
        exact Term.shift_eq_of_closedAt
          (Term.closedAt_mono (fixApprox_mem_allTerms hFix (n - k)).1 (Nat.zero_le cutoff))
      have he : Term.shift amount cutoff (.fix body) = .fix body :=
        Term.shift_eq_of_closedAt (Term.closedAt_mono hFix.1 (Nat.zero_le cutoff))
      rw [hf, he]
      exact .hole k
  | var i =>
      by_cases hi : cutoff ≤ i
      · simpa only [Term.shift, if_pos hi] using (UnfoldFamily.var (body := body) (i + amount))
      · simpa only [Term.shift, if_neg hi] using (UnfoldFamily.var (body := body) i)
  | int n => exact .int n
  | omega => exact .omega
  | err => exact .err
  | lam h ih => exact .lam (ih (cutoff + 1))
  | fix h ih => exact .fix (ih (cutoff + 1))
  | app h₁ h₂ ih₁ ih₂ => exact .app (ih₁ cutoff) (ih₂ cutoff)
  | pair h₁ h₂ ih₁ ih₂ => exact .pair (ih₁ cutoff) (ih₂ cutoff)
  | proj h ih => exact .proj (ih cutoff)
  | op o h₁ h₂ ih₁ ih₂ => exact .op o (ih₁ cutoff) (ih₂ cutoff)
  | ite h₀ h₁ h₂ ih₀ ih₁ ih₂ => exact .ite (ih₀ cutoff) (ih₁ cutoff) (ih₂ cutoff)
  | letE h₁ h₂ ih₁ ih₂ => exact .letE (ih₁ cutoff) (ih₂ (cutoff + 1))

/-- Substitution acts pointwise on unfolding families. -/
theorem subst {A : SimpleTy} {body : Term} {f g : Nat → Term} {e a : Term}
    (hFix : AllTerms A (.fix body))
    (h : UnfoldFamily body f e) (hArg : UnfoldFamily body g a) (j : Nat) :
    UnfoldFamily body (fun n => Term.subst j (g n) (f n)) (Term.subst j a e) := by
  induction h generalizing g a j with
  | hole k =>
      have hf : (fun n => Term.subst j (g n) (Term.fixApprox body (n - k))) =
          (fun n => Term.fixApprox body (n - k)) := by
        funext n
        exact Term.subst_eq_of_closedAt
          (fixApprox_mem_allTerms hFix (n - k)).1 (Nat.zero_le j)
      have he : Term.subst j a (.fix body) = .fix body :=
        Term.subst_eq_of_closedAt hFix.1 (Nat.zero_le j)
      rw [hf, he]
      exact .hole k
  | var i =>
      by_cases hEq : i = j
      · simpa only [Term.subst, if_pos hEq] using hArg
      · by_cases hLt : j < i
        · simpa only [Term.subst, if_neg hEq, if_pos hLt] using
            (UnfoldFamily.var (body := body) (i - 1))
        · simpa only [Term.subst, if_neg hEq, if_neg hLt] using
            (UnfoldFamily.var (body := body) i)
  | int n => exact .int n
  | omega => exact .omega
  | err => exact .err
  | lam h ih =>
      exact .lam (ih (j := j + 1)
        (g := fun n => Term.shift 1 0 (g n)) (a := Term.shift 1 0 a)
        (UnfoldFamily.shift hFix hArg 1 0))
  | fix h ih =>
      exact .fix (ih (j := j + 1)
        (g := fun n => Term.shift 1 0 (g n)) (a := Term.shift 1 0 a)
        (UnfoldFamily.shift hFix hArg 1 0))
  | app h₁ h₂ ih₁ ih₂ => exact .app (ih₁ (j := j) hArg) (ih₂ (j := j) hArg)
  | pair h₁ h₂ ih₁ ih₂ => exact .pair (ih₁ (j := j) hArg) (ih₂ (j := j) hArg)
  | proj h ih => exact .proj (ih (j := j) hArg)
  | op o h₁ h₂ ih₁ ih₂ => exact .op o (ih₁ (j := j) hArg) (ih₂ (j := j) hArg)
  | ite h₀ h₁ h₂ ih₀ ih₁ ih₂ =>
      exact .ite (ih₀ (j := j) hArg) (ih₁ (j := j) hArg) (ih₂ (j := j) hArg)
  | letE h₁ h₂ ih₁ ih₂ =>
      exact .letE (ih₁ (j := j) hArg)
        (ih₂ (j := j + 1)
          (g := fun n => Term.shift 1 0 (g n)) (a := Term.shift 1 0 a)
          (UnfoldFamily.shift hFix hArg 1 0))

theorem instantiate {A : SimpleTy} {body : Term}
    {f g : Nat → Term} {e a : Term}
    (hFix : AllTerms A (.fix body))
    (h : UnfoldFamily body f e) (hArg : UnfoldFamily body g a) :
    UnfoldFamily body (fun n => Term.instantiate (f n) (g n))
      (Term.instantiate e a) := by
  exact UnfoldFamily.subst hFix h hArg 0

end UnfoldFamily

/-- The retained syntax in value results is itself an unfolding family. -/
def UnfoldValueFamily (body : Term) (f : Nat → Value) : Value → Prop
  | .int n => ∀ k, f k = .int n
  | .lam e => ∃ g, UnfoldFamily body g e ∧ ∀ k, f k = .lam (g k)
  | .pair e a => ∃ g h, UnfoldFamily body g e ∧ UnfoldFamily body h a ∧
      ∀ k, f k = .pair (g k) (h k)

/-- Every finite value observation of the limit is reproduced by all
sufficiently deep unfoldings, with retained components tracked as families. -/
theorem unfoldFamily_eval
    {A : SimpleTy} {body : Term} {f : Nat → Term} {e : Term} {v : Value}
    (hFix : AllTerms A (.fix body)) (hEval : Eval e v)
    (hFamily : UnfoldFamily body f e) :
    ∃ N g, UnfoldValueFamily body g v ∧ ∀ n, N ≤ n → Eval (f n) (g n) := by
  induction hEval generalizing f with
  | int =>
      cases hFamily
      rename_i value
      refine ⟨0, fun _ => .int value, ?_, ?_⟩
      · intro n; rfl
      · intro n hn; exact Eval.int
  | lam =>
      cases hFamily with
      | @lam fb b hB =>
          refine ⟨0, fun n => .lam (fb n), ?_, ?_⟩
          · exact ⟨fb, hB, fun _ => rfl⟩
          · intro n hn; exact Eval.lam
  | pair =>
      cases hFamily with
      | @pair fa fb a b hA hB =>
          refine ⟨0, fun n => .pair (fa n) (fb n), ?_, ?_⟩
          · exact ⟨fa, fb, hA, hB, fun _ => rfl⟩
          · intro n hn; exact Eval.pair
  | app hFun hBody ihFun ihBody =>
      cases hFamily with
      | @app ff fa ef ea hF hA =>
          rcases ihFun hF with ⟨NF, fv, hValue, hEF⟩
          rcases hValue with ⟨fb, hB, hEq⟩
          rcases ihBody (UnfoldFamily.instantiate hFix hB hA) with ⟨NB, g, hG, hEB⟩
          refine ⟨max NF NB, g, hG, ?_⟩
          intro n hn
          have hFunN := hEF n (Nat.le_trans (Nat.le_max_left _ _) hn)
          rw [hEq n] at hFunN
          exact Eval.app hFunN (hEB n (Nat.le_trans (Nat.le_max_right _ _) hn))
  | projLeft hScrut hComp ihScrut ihComp =>
      cases hFamily with
      | proj hP =>
          rcases ihScrut hP with ⟨NP, fv, hValue, hEP⟩
          rcases hValue with ⟨fa, fb, hA, hB, hEq⟩
          rcases ihComp hA with ⟨NC, g, hG, hEC⟩
          refine ⟨max NP NC, g, hG, ?_⟩
          intro n hn
          have hPairN := hEP n (Nat.le_trans (Nat.le_max_left _ _) hn)
          rw [hEq n] at hPairN
          exact Eval.projLeft hPairN (hEC n (Nat.le_trans (Nat.le_max_right _ _) hn))
  | projRight hScrut hComp ihScrut ihComp =>
      cases hFamily with
      | proj hP =>
          rcases ihScrut hP with ⟨NP, fv, hValue, hEP⟩
          rcases hValue with ⟨fa, fb, hA, hB, hEq⟩
          rcases ihComp hB with ⟨NC, g, hG, hEC⟩
          refine ⟨max NP NC, g, hG, ?_⟩
          intro n hn
          have hPairN := hEP n (Nat.le_trans (Nat.le_max_left _ _) hn)
          rw [hEq n] at hPairN
          exact Eval.projRight hPairN (hEC n (Nat.le_trans (Nat.le_max_right _ _) hn))
  | op o hLeft hRight ihLeft ihRight =>
      cases hFamily with
      | op o hL hR =>
          rcases ihLeft hL with ⟨NL, fl, hVL, hEL⟩
          rcases ihRight hR with ⟨NR, fr, hVR, hER⟩
          let g : Nat → Value := fun n =>
            match fl n, fr n with
            | .int left, .int right => .int (o.eval left right)
            | _, _ => .int 0
          refine ⟨max NL NR, g, ?_, ?_⟩
          · intro n
            simp only [g, hVL n, hVR n]
          · intro n hn
            have hLN := hEL n (Nat.le_trans (Nat.le_max_left _ _) hn)
            have hRN := hER n (Nat.le_trans (Nat.le_max_right _ _) hn)
            rw [hVL n] at hLN
            rw [hVR n] at hRN
            simpa only [g, hVL n, hVR n] using Eval.op o hLN hRN
  | ifZero hCond hZero hBranch ihCond ihBranch =>
      cases hFamily with
      | ite hC hT hE =>
          rcases ihCond hC with ⟨NC, fc, hVC, hEC⟩
          rcases ihBranch hE with ⟨NB, g, hG, hEB⟩
          refine ⟨max NC NB, g, hG, ?_⟩
          intro n hn
          have hCN := hEC n (Nat.le_trans (Nat.le_max_left _ _) hn)
          rw [hVC n] at hCN
          exact Eval.ifZero hCN hZero (hEB n (Nat.le_trans (Nat.le_max_right _ _) hn))
  | ifNonzero hCond hNonzero hBranch ihCond ihBranch =>
      cases hFamily with
      | ite hC hT hE =>
          rcases ihCond hC with ⟨NC, fc, hVC, hEC⟩
          rcases ihBranch hT with ⟨NB, g, hG, hEB⟩
          refine ⟨max NC NB, g, hG, ?_⟩
          intro n hn
          have hCN := hEC n (Nat.le_trans (Nat.le_max_left _ _) hn)
          rw [hVC n] at hCN
          exact Eval.ifNonzero hCN hNonzero (hEB n (Nat.le_trans (Nat.le_max_right _ _) hn))
  | letE hBody ihBody =>
      cases hFamily with
      | letE hA hB =>
          rcases ihBody (UnfoldFamily.instantiate hFix hB hA) with ⟨N, g, hG, hE⟩
          exact ⟨N, g, hG, fun n hn => Eval.letE (hE n hn)⟩
  | fix hBody ihBody =>
      cases hFamily with
      | hole k =>
          have hUnfold : UnfoldFamily body
              (fun n => Term.instantiate body (Term.fixApprox body (n - (k + 1))))
              (Term.instantiate body (.fix body)) :=
            UnfoldFamily.instantiate hFix (UnfoldFamily.const body body) (UnfoldFamily.hole (k + 1))
          rcases ihBody hUnfold with ⟨N, g, hG, hE⟩
          refine ⟨max N (k + 1), g, hG, ?_⟩
          intro n hn
          have hNk : k + 1 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
          change Eval (Term.fixApprox body (n - k)) (g n)
          rw [show n - k = (n - (k + 1)) + 1 by omega]
          exact hE n (Nat.le_trans (Nat.le_max_left _ _) hn)
      | fix hB =>
          rcases ihBody (UnfoldFamily.instantiate hFix hB (UnfoldFamily.fix hB)) with
            ⟨N, g, hG, hE⟩
          exact ⟨N, g, hG, fun n hn => Eval.fix (hE n hn)⟩

/-- Every finite error observation of the limit is reproduced by all
sufficiently deep unfoldings. -/
theorem unfoldFamily_evalErr
    {A : SimpleTy} {body : Term} {f : Nat → Term} {e : Term}
    (hFix : AllTerms A (.fix body)) (hErr : EvalErr e)
    (hFamily : UnfoldFamily body f e) :
    ∃ N, ∀ n, N ≤ n → EvalErr (f n) := by
  induction hErr generalizing f with
  | err =>
      cases hFamily
      exact ⟨0, fun n hn => EvalErr.err⟩
  | appFun hFun ihFun =>
      cases hFamily with
      | app hF hA =>
          rcases ihFun hF with ⟨N, hE⟩
          exact ⟨N, fun n hn => EvalErr.appFun (hE n hn)⟩
  | appBody hFun hBody ihBody =>
      cases hFamily with
      | app hF hA =>
          rcases unfoldFamily_eval hFix hFun hF with ⟨NF, fv, hValue, hEF⟩
          rcases hValue with ⟨fb, hB, hEq⟩
          rcases ihBody (UnfoldFamily.instantiate hFix hB hA) with ⟨NB, hEB⟩
          refine ⟨max NF NB, ?_⟩
          intro n hn
          have hFN := hEF n (Nat.le_trans (Nat.le_max_left _ _) hn)
          rw [hEq n] at hFN
          exact EvalErr.appBody hFN (hEB n (Nat.le_trans (Nat.le_max_right _ _) hn))
  | projScrutinee hScrut ihScrut =>
      cases hFamily with
      | proj hP =>
          rcases ihScrut hP with ⟨N, hE⟩
          exact ⟨N, fun n hn => EvalErr.projScrutinee (hE n hn)⟩
  | projLeftComponent hScrut hComp ihComp =>
      cases hFamily with
      | proj hP =>
          rcases unfoldFamily_eval hFix hScrut hP with ⟨NP, fv, hValue, hEP⟩
          rcases hValue with ⟨fa, fb, hA, hB, hEq⟩
          rcases ihComp hA with ⟨NC, hEC⟩
          refine ⟨max NP NC, ?_⟩
          intro n hn
          have hPN := hEP n (Nat.le_trans (Nat.le_max_left _ _) hn)
          rw [hEq n] at hPN
          exact EvalErr.projLeftComponent hPN (hEC n (Nat.le_trans (Nat.le_max_right _ _) hn))
  | projRightComponent hScrut hComp ihComp =>
      cases hFamily with
      | proj hP =>
          rcases unfoldFamily_eval hFix hScrut hP with ⟨NP, fv, hValue, hEP⟩
          rcases hValue with ⟨fa, fb, hA, hB, hEq⟩
          rcases ihComp hB with ⟨NC, hEC⟩
          refine ⟨max NP NC, ?_⟩
          intro n hn
          have hPN := hEP n (Nat.le_trans (Nat.le_max_left _ _) hn)
          rw [hEq n] at hPN
          exact EvalErr.projRightComponent hPN (hEC n (Nat.le_trans (Nat.le_max_right _ _) hn))
  | opLeft o hLeft ihLeft =>
      cases hFamily with
      | op o hL hR =>
          rcases ihLeft hL with ⟨N, hE⟩
          exact ⟨N, fun n hn => EvalErr.opLeft o (hE n hn)⟩
  | opRight o hLeft hRight ihRight =>
      cases hFamily with
      | op o hL hR =>
          rcases unfoldFamily_eval hFix hLeft hL with ⟨NL, fl, hVL, hEL⟩
          rcases ihRight hR with ⟨NR, hER⟩
          refine ⟨max NL NR, ?_⟩
          intro n hn
          have hLN := hEL n (Nat.le_trans (Nat.le_max_left _ _) hn)
          rw [hVL n] at hLN
          exact EvalErr.opRight o hLN (hER n (Nat.le_trans (Nat.le_max_right _ _) hn))
  | ifCond hCond ihCond =>
      cases hFamily with
      | ite hC hT hE =>
          rcases ihCond hC with ⟨N, hErr⟩
          exact ⟨N, fun n hn => EvalErr.ifCond (hErr n hn)⟩
  | ifZeroBranch hCond hZero hBranch ihBranch =>
      cases hFamily with
      | ite hC hT hE =>
          rcases unfoldFamily_eval hFix hCond hC with ⟨NC, fc, hVC, hEC⟩
          rcases ihBranch hE with ⟨NB, hEB⟩
          refine ⟨max NC NB, ?_⟩
          intro n hn
          have hCN := hEC n (Nat.le_trans (Nat.le_max_left _ _) hn)
          rw [hVC n] at hCN
          exact EvalErr.ifZeroBranch hCN hZero (hEB n (Nat.le_trans (Nat.le_max_right _ _) hn))
  | ifNonzeroBranch hCond hNonzero hBranch ihBranch =>
      cases hFamily with
      | ite hC hT hE =>
          rcases unfoldFamily_eval hFix hCond hC with ⟨NC, fc, hVC, hEC⟩
          rcases ihBranch hT with ⟨NB, hEB⟩
          refine ⟨max NC NB, ?_⟩
          intro n hn
          have hCN := hEC n (Nat.le_trans (Nat.le_max_left _ _) hn)
          rw [hVC n] at hCN
          exact EvalErr.ifNonzeroBranch hCN hNonzero (hEB n (Nat.le_trans (Nat.le_max_right _ _) hn))
  | letBody hBody ihBody =>
      cases hFamily with
      | letE hA hB =>
          rcases ihBody (UnfoldFamily.instantiate hFix hB hA) with ⟨N, hE⟩
          exact ⟨N, fun n hn => EvalErr.letBody (hE n hn)⟩
  | fix hBody ihBody =>
      cases hFamily with
      | hole k =>
          have hUnfold : UnfoldFamily body
              (fun n => Term.instantiate body (Term.fixApprox body (n - (k + 1))))
              (Term.instantiate body (.fix body)) :=
            UnfoldFamily.instantiate hFix (UnfoldFamily.const body body) (UnfoldFamily.hole (k + 1))
          rcases ihBody hUnfold with ⟨N, hE⟩
          refine ⟨max N (k + 1), ?_⟩
          intro n hn
          have hNk : k + 1 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
          change EvalErr (Term.fixApprox body (n - k))
          rw [show n - k = (n - (k + 1)) + 1 by omega]
          exact hE n (Nat.le_trans (Nat.le_max_left _ _) hn)
      | fix hB =>
          rcases ihBody (UnfoldFamily.instantiate hFix hB (UnfoldFamily.fix hB)) with ⟨N, hE⟩
          exact ⟨N, fun n hn => EvalErr.fix (hE n hn)⟩

/-- Integer observations are reproduced with exactly the same integer. -/
theorem unfoldFamily_eval_int
    {A : SimpleTy} {body : Term} {f : Nat → Term} {e : Term} {value : Int}
    (hFix : AllTerms A (.fix body)) (hEval : Eval e (.int value))
    (hFamily : UnfoldFamily body f e) :
    ∃ N, ∀ n, N ≤ n → Eval (f n) (.int value) := by
  rcases unfoldFamily_eval hFix hEval hFamily with ⟨N, g, hValue, hE⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hEN := hE n hn
  rw [hValue n] at hEN
  exact hEN

/-- Specialization to the original zero-delay finite-unfolding sequence. -/
theorem fixApprox_eval_eventually
    {A : SimpleTy} {body : Term} {v : Value}
    (hFix : AllTerms A (.fix body)) (hEval : Eval (.fix body) v) :
    ∃ N g, UnfoldValueFamily body g v ∧
      ∀ n, N ≤ n → Eval (Term.fixApprox body n) (g n) := by
  simpa only [Nat.sub_zero] using
    unfoldFamily_eval hFix hEval (UnfoldFamily.hole (body := body) 0)

theorem fixApprox_evalErr_eventually
    {A : SimpleTy} {body : Term}
    (hFix : AllTerms A (.fix body)) (hErr : EvalErr (.fix body)) :
    ∃ N, ∀ n, N ≤ n → EvalErr (Term.fixApprox body n) := by
  simpa only [Nat.sub_zero] using
    unfoldFamily_evalErr hFix hErr (UnfoldFamily.hole (body := body) 0)

end Strictness
