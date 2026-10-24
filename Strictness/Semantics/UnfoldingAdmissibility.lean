import Strictness.Semantics.FiniteUnfolding
import Strictness.Semantics.SemanticApplication

namespace Strictness

open Term
open scoped Classical

/-- Membership occurs at arbitrarily large indices. -/
def Cofinal (P : Nat → Prop) : Prop := ∀ N, ∃ n, N ≤ n ∧ P n

namespace Cofinal

theorem map {P Q : Nat → Prop} (h : Cofinal P)
    (hPQ : ∀ n, P n → Q n) : Cofinal Q := by
  intro N
  rcases h N with ⟨n, hn, hP⟩
  exact ⟨n, hn, hPQ n hP⟩

theorem after {P : Nat → Prop} (h : Cofinal P) (K : Nat) :
    Cofinal (fun n => K ≤ n ∧ P n) := by
  intro N
  rcases h (max N K) with ⟨n, hn, hP⟩
  exact ⟨n, Nat.le_trans (Nat.le_max_left _ _) hn,
    Nat.le_trans (Nat.le_max_right _ _) hn, hP⟩

/-- A finite union is cofinal only if one of its summands is cofinal.
No intersection closure of cofinal predicates is assumed. -/
theorem or_split {P Q : Nat → Prop} (h : Cofinal (fun n => P n ∨ Q n)) :
    Cofinal P ∨ Cofinal Q := by
  by_cases hP : Cofinal P
  · exact Or.inl hP
  · right
    have hBound : ∃ K, ∀ n, K ≤ n → ¬ P n := by
      apply Classical.byContradiction
      intro hNoBound
      apply hP
      intro K
      apply Classical.byContradiction
      intro hNoWitness
      apply hNoBound
      refine ⟨K, ?_⟩
      intro n hn hPn
      exact hNoWitness ⟨n, hn, hPn⟩
    rcases hBound with ⟨K, hK⟩
    intro N
    rcases h (max N K) with ⟨n, hn, hPQ⟩
    refine ⟨n, Nat.le_trans (Nat.le_max_left _ _) hn, ?_⟩
    exact hPQ.resolve_left (hK n (Nat.le_trans (Nat.le_max_right _ _) hn))

end Cofinal

/-- Big-step evaluation preserves simple typing, including retained syntax. -/
theorem eval_hasType_open {Γ : Term.Ctx} {e : Term} {v : Value} {A : SimpleTy}
    (hEval : Eval e v) (hType : HasType Γ e A) :
    HasType Γ v.toTerm A := by
  induction hEval generalizing A with
  | int => exact hType
  | lam => exact hType
  | pair => exact hType
  | app hFun hBody ihFun ihBody =>
      cases hType with
      | app hF hA =>
          have hLam := ihFun hF
          cases hLam with
          | lam hB => exact ihBody (hasType_instantiate_open hB hA)
  | projLeft hPair hComp ihPair ihComp =>
      cases hType with
      | projLeft hP =>
          have hValue := ihPair hP
          cases hValue with
          | pair hL hR => exact ihComp hL
  | projRight hPair hComp ihPair ihComp =>
      cases hType with
      | projRight hP =>
          have hValue := ihPair hP
          cases hValue with
          | pair hL hR => exact ihComp hR
  | op o hLeft hRight ihLeft ihRight =>
      cases hType
      exact HasType.int
  | ifZero hCond hZero hBranch ihCond ihBranch =>
      cases hType with
      | ite hC hT hE => exact ihBranch hE
  | ifNonzero hCond hNonzero hBranch ihCond ihBranch =>
      cases hType with
      | ite hC hT hE => exact ihBranch hT
  | letE hBody ihBody =>
      cases hType with
      | letE hA hB => exact ihBody (hasType_instantiate_open hB hA)
  | fix hBody ihBody =>
      cases hType with
      | fix hB => exact ihBody (hasType_instantiate_open hB (HasType.fix hB))

/-- Closure under limits of the delayed unfolding families. The limit is
required to have the given erased type; cofinal membership is enough. -/
def UnfoldAdmissible (A : SimpleTy) (X : TermSet Term) : Prop :=
  ∀ {B : SimpleTy} {body : Term} {f : Nat → Term} {e : Term},
    AllTerms B (.fix body) → UnfoldFamily body f e → AllTerms A e →
    Cofinal (fun n => X (f n)) → X e

namespace UnfoldAdmissible

theorem allTerms (A : SimpleTy) : UnfoldAdmissible A (AllTerms A) := by
  intro B body f e hFix hFamily hAll hMem
  exact hAll

theorem empty (A : SimpleTy) : UnfoldAdmissible A TermSet.empty := by
  intro B body f e hFix hFamily hAll hMem
  rcases hMem 0 with ⟨n, hn, hFalse⟩
  exact False.elim hFalse

theorem union {A : SimpleTy} {X Y : TermSet Term}
    (hX : UnfoldAdmissible A X) (hY : UnfoldAdmissible A Y) :
    UnfoldAdmissible A (TermSet.union X Y) := by
  intro B body f e hFix hFamily hAll hMem
  rcases Cofinal.or_split hMem with hLeft | hRight
  · exact Or.inl (hX hFix hFamily hAll hLeft)
  · exact Or.inr (hY hFix hFamily hAll hRight)

/-- Distributing the common divergence branch over a finite union. -/
theorem safe_union {A : SimpleTy} {O X Y : TermSet Term}
    (hX : UnfoldAdmissible A (TermSet.union O X))
    (hY : UnfoldAdmissible A (TermSet.union O Y)) :
    UnfoldAdmissible A (TermSet.union O (TermSet.union X Y)) := by
  intro B body f e hFix hFamily hAll hMem
  have hSplit : Cofinal (fun n =>
      TermSet.union O X (f n) ∨ TermSet.union O Y (f n)) := by
    apply hMem.map
    intro n hn
    rcases hn with hO | hXn | hYn
    · exact Or.inl (Or.inl hO)
    · exact Or.inl (Or.inr hXn)
    · exact Or.inr (Or.inr hYn)
  rcases Cofinal.or_split hSplit with hLeft | hRight
  · rcases hX hFix hFamily hAll hLeft with hO | hXe
    · exact Or.inl hO
    · exact Or.inr (Or.inl hXe)
  · rcases hY hFix hFamily hAll hRight with hO | hYe
    · exact Or.inl hO
    · exact Or.inr (Or.inr hYe)

/-- To establish admissibility it suffices to handle convergent limits,
provided divergence is included and finite errors are excluded. -/
theorem of_convergent {A : SimpleTy} {X : TermSet Term}
    (hDiv : TermSet.Subset (DivergentTerms A) X)
    (hNoError : ∀ {e}, X e → ¬ EvalErr e)
    (hConv : ∀ {B : SimpleTy} {body : Term} {f : Nat → Term}
      {e : Term} {v : Value}, AllTerms B (.fix body) →
      UnfoldFamily body f e → AllTerms A e → Eval e v →
      Cofinal (fun n => X (f n)) → X e) :
    UnfoldAdmissible A X := by
  intro B body f e hFix hFamily hAll hMem
  have hNoErrorLimit : ¬ EvalErr e := by
    intro hErr
    rcases unfoldFamily_evalErr hFix hErr hFamily with ⟨N, hEventually⟩
    rcases hMem N with ⟨n, hn, hX⟩
    exact hNoError hX (hEventually n hn)
  by_cases hEval : ∃ v, Eval e v
  · rcases hEval with ⟨v, hv⟩
    exact hConv hFix hFamily hAll hv hMem
  · exact hDiv ⟨hAll, hEval, hNoErrorLimit⟩

theorem divergentTerms (A : SimpleTy) :
    UnfoldAdmissible A (DivergentTerms A) := by
  refine of_convergent (A := A) (X := DivergentTerms A)
    (fun {_} h => h) (fun {_} h => h.2.2) ?_
  intro B body f e v hFix hFamily hAll hEval hMem
  rcases unfoldFamily_eval hFix hEval hFamily with ⟨N, g, hG, hEventually⟩
  rcases hMem N with ⟨n, hn, hDiv⟩
  exact False.elim (hDiv.2.1 ⟨g n, hEventually n hn⟩)

/-- The integer V-clause (divergence or an integer observation). -/
theorem safe_numeral :
    UnfoldAdmissible .int (TermSet.union (DivergentTerms .int) NumeralTerms) := by
  refine of_convergent (A := .int)
    (X := TermSet.union (DivergentTerms .int) NumeralTerms)
    (fun {_} h => Or.inl h) ?_ ?_
  · intro e he
    rcases he with hDiv | hNum
    · exact hDiv.2.2
    · rcases hNum.2.2 with ⟨n, hEval⟩
      exact eval_not_evalErr hEval
  · intro B body f e v hFix hFamily hAll hEval hMem
    have hType := eval_hasType_open hEval hAll.2
    cases v with
    | int n => exact Or.inr ⟨hAll.1, hAll.2, n, hEval⟩
    | pair a b => cases hType
    | lam b => cases hType

/-- A divergent term or a pair with admissible retained components. -/
theorem safe_pair {A B : SimpleTy} {X Y : TermSet Term}
    (hX : UnfoldAdmissible A X) (hY : UnfoldAdmissible B Y) :
    UnfoldAdmissible (.prod A B)
      (TermSet.union (DivergentTerms (.prod A B)) (PairTerms A B X Y)) := by
  refine of_convergent (A := .prod A B)
    (X := TermSet.union (DivergentTerms (.prod A B)) (PairTerms A B X Y))
    (fun {_} h => Or.inl h) ?_ ?_
  · intro e he
    rcases he with hDiv | hPair
    · exact hDiv.2.2
    · rcases hPair.2 with ⟨a, b, hEval, ha, hb⟩
      exact eval_not_evalErr hEval
  · intro C body f e v hFix hFamily hAll hEval hMem
    have hType := eval_hasType_open hEval hAll.2
    cases v with
    | int n => cases hType
    | lam b => cases hType
    | pair a b =>
        cases hType with
        | pair hA hB =>
            rcases unfoldFamily_eval hFix hEval hFamily with ⟨N, g, hG, hEventually⟩
            rcases hG with ⟨fa, fb, hFA, hFB, hEq⟩
            have hComponents : Cofinal (fun n => X (fa n) ∧ Y (fb n)) := by
              apply (hMem.after N).map
              intro n hn
              have hEN := hEventually n hn.1
              rw [hEq n] at hEN
              rcases hn.2 with hDiv | hPair
              · exact False.elim (hDiv.2.1 ⟨_, hEN⟩)
              · rcases hPair.2 with ⟨x, y, hP, hx, hy⟩
                have hValues := Value.pair.inj (eval_deterministic hP hEN)
                rw [hValues.1] at hx
                rw [hValues.2] at hy
                exact ⟨hx, hy⟩
            have hXA : X a := hX hFix hFA ⟨hasType_nil_closed hA, hA⟩
              (hComponents.map (fun n hn => hn.1))
            have hYB : Y b := hY hFix hFB ⟨hasType_nil_closed hB, hB⟩
              (hComponents.map (fun n hn => hn.2))
            exact Or.inr ⟨hAll, a, b, hEval, hXA, hYB⟩

/-- Function V-obligations are transferred by applying the family to a
constant argument. Only the result sets need admissibility. -/
theorem safe_function {A B : SimpleTy} {VX DX VY DY : TermSet Term}
    (hVX : TermSet.Subset VX (AllTerms A))
    (hDX : TermSet.Subset DX (AllTerms A))
    (hVY : UnfoldAdmissible B VY) (hDY : UnfoldAdmissible B DY) :
    UnfoldAdmissible (.arrow A B)
      (TermSet.union (DivergentTerms (.arrow A B))
        (FunctionTerms A B VX DX VY DY)) := by
  refine of_convergent (A := .arrow A B)
    (X := TermSet.union (DivergentTerms (.arrow A B))
      (FunctionTerms A B VX DX VY DY))
    (fun {_} h => Or.inl h) ?_ ?_
  · intro e he
    rcases he with hDiv | hFun
    · exact hDiv.2.2
    · rcases hFun.2 with ⟨b, hEval, hV, hD⟩
      exact eval_not_evalErr hEval
  · intro C body f e v hFix hFamily hAll hEval hMem
    have hType := eval_hasType_open hEval hAll.2
    cases v with
    | int n => cases hType
    | pair a b => cases hType
    | lam b =>
        rcases unfoldFamily_eval hFix hEval hFamily with ⟨N, g, hG, hEventually⟩
        have hFunctions : Cofinal (fun n => FunctionTerms A B VX DX VY DY (f n)) := by
          apply (hMem.after N).map
          intro n hn
          rcases hn.2 with hDiv | hFun
          · exact False.elim (hDiv.2.1 ⟨g n, hEventually n hn.1⟩)
          · exact hFun
        refine Or.inr ⟨hAll, b, hEval, ?_, ?_⟩
        · intro a ha
          apply hVY hFix (UnfoldFamily.app hFamily (UnfoldFamily.const body a))
            (allTerms_app hAll (hVX ha))
          apply hFunctions.map
          intro n hn
          rcases hn.2 with ⟨b', hEval', hV, hD⟩
          exact hV a ha
        · intro a ha
          apply hDY hFix (UnfoldFamily.app hFamily (UnfoldFamily.const body a))
            (allTerms_app hAll (hDX ha))
          apply hFunctions.map
          intro n hn
          rcases hn.2 with ⟨b', hEval', hV, hD⟩
          exact hD a ha

/-- The additional V→D obligation of a strict arrow. The V-set of that
same arrow has already been shown admissible before using this lemma. -/
theorem safe_strict_function {A B : SimpleTy} {VA VX DY : TermSet Term}
    (hVA : UnfoldAdmissible (.arrow A B) VA)
    (hDivVA : TermSet.Subset (DivergentTerms (.arrow A B)) VA)
    (hVX : TermSet.Subset VX (AllTerms A))
    (hDY : UnfoldAdmissible B DY) :
    UnfoldAdmissible (.arrow A B)
      (TermSet.union (DivergentTerms (.arrow A B))
        (StrictFunctionTerms A B VA VX DY)) := by
  refine of_convergent (A := .arrow A B)
    (X := TermSet.union (DivergentTerms (.arrow A B))
      (StrictFunctionTerms A B VA VX DY))
    (fun {_} h => Or.inl h) ?_ ?_
  · intro e he
    rcases he with hDiv | hFun
    · exact hDiv.2.2
    · rcases hFun.2 with ⟨b, hEval, hStrict⟩
      exact eval_not_evalErr hEval
  · intro C body f e v hFix hFamily hAll hEval hMem
    have hType := eval_hasType_open hEval hAll.2
    cases v with
    | int n => cases hType
    | pair a b => cases hType
    | lam b =>
        have hValue : VA e := by
          apply hVA hFix hFamily hAll
          apply hMem.map
          intro n hn
          rcases hn with hDiv | hFun
          · exact hDivVA hDiv
          · exact hFun.1
        rcases unfoldFamily_eval hFix hEval hFamily with ⟨N, g, hG, hEventually⟩
        have hFunctions : Cofinal (fun n => StrictFunctionTerms A B VA VX DY (f n)) := by
          apply (hMem.after N).map
          intro n hn
          rcases hn.2 with hDiv | hFun
          · exact False.elim (hDiv.2.1 ⟨g n, hEventually n hn.1⟩)
          · exact hFun
        refine Or.inr ⟨hValue, b, hEval, ?_⟩
        intro a ha
        apply hDY hFix (UnfoldFamily.app hFamily (UnfoldFamily.const body a))
          (allTerms_app hAll (hVX ha))
        apply hFunctions.map
        intro n hn
        rcases hn.2 with ⟨b', hEval', hStrict⟩
        exact hStrict a ha

end UnfoldAdmissible

end Strictness
