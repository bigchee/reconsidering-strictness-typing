import Strictness.Semantics.SemanticBasic
import Strictness.Language.SimpleSubstitution
import Strictness.Operational.OperationalLemmas

namespace Strictness

open Term

/-- Two terms have the same CBN observations when they have exactly the same
values and either both or neither reach the semantic error marker. -/
def RawEq (e e' : Term) : Prop :=
  (∀ v, Eval e v ↔ Eval e' v) ∧
  (EvalErr e ↔ EvalErr e')

/-- Typed observational equivalence.  The common erased type is explicit so
that equivalence can be transported through the logical relation. -/
def SemEq (τ : SimpleTy) (e e' : Term) : Prop :=
  AllTerms τ e ∧ AllTerms τ e' ∧ RawEq e e'

@[simp] theorem rawEq_refl (e : Term) : RawEq e e := by
  exact ⟨fun _ => Iff.rfl, Iff.rfl⟩

theorem rawEq_symm {e e' : Term} : RawEq e e' → RawEq e' e := by
  intro h
  exact ⟨fun v => (h.1 v).symm, h.2.symm⟩

theorem rawEq_trans {e₁ e₂ e₃ : Term} :
    RawEq e₁ e₂ → RawEq e₂ e₃ → RawEq e₁ e₃ := by
  intro h12 h23
  exact ⟨fun v => (h12.1 v).trans (h23.1 v), h12.2.trans h23.2⟩

theorem rawEq_diverges {e e' : Term} (h : RawEq e e') :
    Term.Diverges e ↔ Term.Diverges e' := by
  constructor
  · intro hd
    refine ⟨?_, ?_⟩
    · intro hEval
      rcases hEval with ⟨v, hv⟩
      exact hd.1 ⟨v, (h.1 v).mpr hv⟩
    · intro hErr
      exact hd.2 ((h.2).mpr hErr)
  · intro hd
    refine ⟨?_, ?_⟩
    · intro hEval
      rcases hEval with ⟨v, hv⟩
      exact hd.1 ⟨v, (h.1 v).mp hv⟩
    · intro hErr
      exact hd.2 ((h.2).mp hErr)

/-- Application preserves raw observational equivalence. -/
theorem rawEq_app {f f' a : Term} :
    RawEq f f' → RawEq (.app f a) (.app f' a) := by
  intro hf
  constructor
  · intro v
    constructor
    · intro h
      cases h with
      | app hFun hBody =>
          rcases (hf.1 (.lam _)).mp hFun with hFun'
          exact Eval.app hFun' hBody
    · intro h
      cases h with
      | app hFun hBody =>
          rcases (hf.1 (.lam _)).mpr hFun with hFun'
          exact Eval.app hFun' hBody
  · constructor
    · intro h
      cases h with
      | appFun hErr => exact EvalErr.appFun ((hf.2).mp hErr)
      | appBody hFun hErr => exact EvalErr.appBody ((hf.1 _).mp hFun) hErr
    · intro h
      cases h with
      | appFun hErr => exact EvalErr.appFun ((hf.2).mpr hErr)
      | appBody hFun hErr => exact EvalErr.appBody ((hf.1 _).mpr hFun) hErr

/-- Application preserves typed semantic equivalence. -/
theorem semEq_app {σ τ : SimpleTy} {f f' a : Term}
    (hf : SemEq (.arrow σ τ) f f')
    (ha : AllTerms σ a) :
    SemEq τ (.app f a) (.app f' a) := by
  rcases hf with ⟨hfType, hf'Type, hRaw⟩
  rcases hfType with ⟨hfClosed, hfSimple⟩
  rcases hf'Type with ⟨hf'Closed, hf'Simple⟩
  rcases ha with ⟨haClosed, haSimple⟩
  refine ⟨?_, ?_, rawEq_app hRaw⟩
  · exact ⟨⟨hfClosed, haClosed⟩, Term.HasType.app hfSimple haSimple⟩
  · exact ⟨⟨hf'Closed, haClosed⟩, Term.HasType.app hf'Simple haSimple⟩

/-- A beta-redex and its CBN contractum have the same observations. -/
theorem semEq_beta {σ τ : SimpleTy} {body a : Term}
    (hLam : AllTerms (.arrow σ τ) (.lam body))
    (ha : AllTerms σ a)
    (hBody : AllTerms τ (Term.instantiate body a)) :
    SemEq τ (.app (.lam body) a) (Term.instantiate body a) := by
  refine ⟨?_, hBody, ?_⟩
  · rcases hLam with ⟨hClosed, hSimple⟩
    rcases ha with ⟨haClosed, haSimple⟩
    exact ⟨⟨hClosed, haClosed⟩, Term.HasType.app hSimple haSimple⟩
  · constructor
    · intro v
      constructor
      · intro h
        cases h with
        | app hFun hBodyEval =>
            cases hFun
            exact hBodyEval
      · intro h
        exact Eval.app Eval.lam h
    · constructor
      · intro h
        cases h with
        | appFun hErr => cases hErr
        | appBody hFun hErr =>
            cases hFun
            exact hErr
      · intro h
        exact EvalErr.appBody Eval.lam h

/-- A call-by-name let expression has the same observations as its contractum. -/
theorem semEq_let {τ : SimpleTy} {e₁ e₂ : Term}
    (hLet : AllTerms τ (.letE e₁ e₂))
    (hBody : AllTerms τ (Term.instantiate e₂ e₁)) :
    SemEq τ (.letE e₁ e₂) (Term.instantiate e₂ e₁) := by
  refine ⟨hLet, hBody, ?_⟩
  constructor
  · intro v
    constructor
    · intro h
      cases h with
      | letE hBodyEval => exact hBodyEval
    · intro h
      exact Eval.letE h
  · constructor
    · intro h
      cases h with
      | letBody hBodyErr => exact hBodyErr
    · intro h
      exact EvalErr.letBody h

/-- Semantic interpretations are invariant under typed observational
equivalence.  This is the analogue of the beta-equivalence closure used by
 Smetsers--van Eekelen.  The proof follows the structure of the annotated type.
 The pair cases use the fact that a successful pair evaluation preserves its
 component terms exactly; the function cases additionally use application
 congruence and the induction hypothesis for the result type. -/
theorem semantic_equiv_VD : ∀ {τ : Ty} {e e' : Term},
    SemEq τ.erase e e' →
      (V τ e ↔ V τ e') ∧ (D τ e ↔ D τ e')
  | .int u, e, e', hEq => by
      by_cases hOuter : Usage.lazy ≤ u
      · constructor
        · unfold V LogicalModel.acceptable operationalModel
          simp only [hOuter, if_pos]
          exact ⟨fun _ => hEq.2.1, fun _ => hEq.1⟩
        · unfold D LogicalModel.divergentSide operationalModel
          by_cases hLazy : Ty.IsLazy (.int u)
          · simp only [hLazy, if_pos]
            exact ⟨fun h => False.elim h, fun h => False.elim h⟩
          · simp only [hLazy, hOuter, if_pos]
            exact ⟨fun _ => hEq.2.1, fun _ => hEq.1⟩
      · constructor
        · unfold V LogicalModel.acceptable operationalModel
          simp only [hOuter]
          constructor
          · intro h
            rcases h with hDiv | hNum
            · exact Or.inl ⟨hEq.2.1, rawEq_diverges hEq.2.2 |>.mp hDiv.2⟩
            · exact Or.inr ⟨hEq.2.1.1, hEq.2.1.2,
                by
                  rcases hNum.2.2 with ⟨n, hn⟩
                  exact ⟨n, (hEq.2.2.1 (.int n)).mp hn⟩⟩
          · intro h
            rcases h with hDiv | hNum
            · exact Or.inl ⟨hEq.1, rawEq_diverges hEq.2.2 |>.mpr hDiv.2⟩
            · exact Or.inr ⟨hEq.1.1, hEq.1.2,
                by
                  rcases hNum.2.2 with ⟨n, hn⟩
                  exact ⟨n, (hEq.2.2.1 (.int n)).mpr hn⟩⟩
        · constructor
          · intro h
            unfold D LogicalModel.divergentSide operationalModel at h
            unfold D LogicalModel.divergentSide operationalModel
            by_cases hLazy : Ty.IsLazy (.int u)
            · simp only [hLazy, if_pos] at h
              simp only [hLazy, if_pos]
              exact False.elim h
            · simp only [hLazy] at h
              simp only [hLazy]
              by_cases hOuter' : Usage.lazy ≤ u
              · simp [hOuter'] at h ⊢
                exact hEq.2.1
              · simp only [hOuter'] at h ⊢
                cases u with
                | strict =>
                    exact ⟨hEq.2.1, rawEq_diverges hEq.2.2 |>.mp h.2⟩
                | unknown => simp [TermSet.empty] at h ⊢
                | lazy => simp [TermSet.empty] at h ⊢
                | top => simp [TermSet.empty] at h ⊢
          · intro h
            unfold D LogicalModel.divergentSide operationalModel at h
            unfold D LogicalModel.divergentSide operationalModel
            by_cases hLazy : Ty.IsLazy (.int u)
            · simp only [hLazy, if_pos] at h
              simp only [hLazy, if_pos]
              exact False.elim h
            · simp only [hLazy] at h
              simp only [hLazy]
              by_cases hOuter' : Usage.lazy ≤ u
              · simp [hOuter'] at h ⊢
                exact hEq.1
              · simp only [hOuter'] at h ⊢
                cases u with
                | strict =>
                    exact ⟨hEq.1, rawEq_diverges hEq.2.2 |>.mpr h.2⟩
                | unknown => simp [TermSet.empty] at h ⊢
                | lazy => simp [TermSet.empty] at h ⊢
                | top => simp [TermSet.empty] at h ⊢
  | .prod σ τ u, e, e', hEq => by
      by_cases hOuter : Usage.lazy ≤ u
      · constructor
        · unfold V LogicalModel.acceptable operationalModel
          simp only [hOuter, if_pos]
          exact ⟨fun _ => hEq.2.1, fun _ => hEq.1⟩
        · unfold D LogicalModel.divergentSide operationalModel
          by_cases hLazy : Ty.IsLazy (.prod σ τ u)
          · simp only [hLazy, if_pos]
            exact ⟨fun h => False.elim h, fun h => False.elim h⟩
          · simp only [hLazy, hOuter, if_pos]
            exact ⟨fun _ => hEq.2.1, fun _ => hEq.1⟩
      · constructor
        · unfold V LogicalModel.acceptable operationalModel
          simp only [hOuter]
          constructor
          · intro h
            rcases h with hDiv | hPair
            · exact Or.inl ⟨hEq.2.1, rawEq_diverges hEq.2.2 |>.mp hDiv.2⟩
            · rcases hPair with ⟨_, e₁, e₂, hev, h₁, h₂⟩
              exact Or.inr ⟨hEq.2.1, e₁, e₂,
                (hEq.2.2.1 (.pair e₁ e₂)).mp hev, h₁, h₂⟩
          · intro h
            rcases h with hDiv | hPair
            · exact Or.inl ⟨hEq.1, rawEq_diverges hEq.2.2 |>.mpr hDiv.2⟩
            · rcases hPair with ⟨_, e₁, e₂, hev, h₁, h₂⟩
              exact Or.inr ⟨hEq.1, e₁, e₂,
                (hEq.2.2.1 (.pair e₁ e₂)).mpr hev, h₁, h₂⟩
        · constructor
          · intro h
            unfold D LogicalModel.divergentSide operationalModel at h
            unfold D LogicalModel.divergentSide operationalModel
            by_cases hLazy : Ty.IsLazy (.prod σ τ u)
            · simp only [hLazy, if_pos] at h
              simp only [hLazy, if_pos]
              exact False.elim h
            · simp only [hLazy] at h
              simp only [hLazy]
              by_cases hOuter' : Usage.lazy ≤ u
              · simp only [hOuter', if_pos] at h ⊢
                exact hEq.2.1
              · simp only [hOuter'] at h ⊢
                cases u with
                | strict =>
                    simp only [if_false, TermSet.union] at h ⊢
                    rcases h with hDiv | hPair
                    · exact Or.inl ⟨hEq.2.1,
                        rawEq_diverges hEq.2.2 |>.mp hDiv.2⟩
                    · rcases hPair with hPair | hPair
                      · rcases hPair with ⟨_, e₁, e₂, hev, h₁, h₂⟩
                        exact Or.inr (Or.inl ⟨hEq.2.1, e₁, e₂,
                          (hEq.2.2.1 (.pair e₁ e₂)).mp hev, h₁, h₂⟩)
                      · rcases hPair with ⟨_, e₁, e₂, hev, h₁, h₂⟩
                        exact Or.inr (Or.inr ⟨hEq.2.1, e₁, e₂,
                          (hEq.2.2.1 (.pair e₁ e₂)).mp hev, h₁, h₂⟩)
                | unknown =>
                    simp only [if_false, TermSet.union] at h ⊢
                    rcases h with hDiv | hPair
                    · exact Or.inl ⟨hEq.2.1,
                        rawEq_diverges hEq.2.2 |>.mp hDiv.2⟩
                    · rcases hPair with hPair | hPair
                      · rcases hPair with ⟨_, e₁, e₂, hev, h₁, h₂⟩
                        exact Or.inr (Or.inl ⟨hEq.2.1, e₁, e₂,
                          (hEq.2.2.1 (.pair e₁ e₂)).mp hev, h₁, h₂⟩)
                      · rcases hPair with ⟨_, e₁, e₂, hev, h₁, h₂⟩
                        exact Or.inr (Or.inr ⟨hEq.2.1, e₁, e₂,
                          (hEq.2.2.1 (.pair e₁ e₂)).mp hev, h₁, h₂⟩)
                | lazy => simp [TermSet.empty] at h ⊢
                | top => simp [TermSet.empty] at h ⊢
          · intro h
            unfold D LogicalModel.divergentSide operationalModel at h
            unfold D LogicalModel.divergentSide operationalModel
            by_cases hLazy : Ty.IsLazy (.prod σ τ u)
            · simp only [hLazy, if_pos] at h
              simp only [hLazy, if_pos]
              exact False.elim h
            · simp only [hLazy] at h
              simp only [hLazy]
              by_cases hOuter' : Usage.lazy ≤ u
              · simp only [hOuter', if_pos] at h ⊢
                exact hEq.1
              · simp only [hOuter'] at h ⊢
                cases u with
                | strict =>
                    simp only [if_false, TermSet.union] at h ⊢
                    rcases h with hDiv | hPair
                    · exact Or.inl ⟨hEq.1,
                        rawEq_diverges hEq.2.2 |>.mpr hDiv.2⟩
                    · rcases hPair with hPair | hPair
                      · rcases hPair with ⟨_, e₁, e₂, hev, h₁, h₂⟩
                        exact Or.inr (Or.inl ⟨hEq.1, e₁, e₂,
                          (hEq.2.2.1 (.pair e₁ e₂)).mpr hev, h₁, h₂⟩)
                      · rcases hPair with ⟨_, e₁, e₂, hev, h₁, h₂⟩
                        exact Or.inr (Or.inr ⟨hEq.1, e₁, e₂,
                          (hEq.2.2.1 (.pair e₁ e₂)).mpr hev, h₁, h₂⟩)
                | unknown =>
                    simp only [if_false, TermSet.union] at h ⊢
                    rcases h with hDiv | hPair
                    · exact Or.inl ⟨hEq.1,
                        rawEq_diverges hEq.2.2 |>.mpr hDiv.2⟩
                    · rcases hPair with hPair | hPair
                      · rcases hPair with ⟨_, e₁, e₂, hev, h₁, h₂⟩
                        exact Or.inr (Or.inl ⟨hEq.1, e₁, e₂,
                          (hEq.2.2.1 (.pair e₁ e₂)).mpr hev, h₁, h₂⟩)
                      · rcases hPair with ⟨_, e₁, e₂, hev, h₁, h₂⟩
                        exact Or.inr (Or.inr ⟨hEq.1, e₁, e₂,
                          (hEq.2.2.1 (.pair e₁ e₂)).mpr hev, h₁, h₂⟩)
                | lazy => simp [TermSet.empty] at h ⊢
                | top => simp [TermSet.empty] at h ⊢
  | .arrow σ τ u, e, e', hEq => by
      by_cases hOuter : Usage.lazy ≤ u
      · constructor
        · unfold V LogicalModel.acceptable operationalModel
          simp only [hOuter, if_pos]
          exact ⟨fun _ => hEq.2.1, fun _ => hEq.1⟩
        · unfold D LogicalModel.divergentSide operationalModel
          by_cases hLazy : Ty.IsLazy (.arrow σ τ u)
          · simp only [hLazy, if_pos]
            exact ⟨fun h => False.elim h, fun h => False.elim h⟩
          · simp only [hLazy, hOuter, if_pos]
            exact ⟨fun _ => hEq.2.1, fun _ => hEq.1⟩
      · constructor
        · unfold V LogicalModel.acceptable operationalModel
          simp only [hOuter]
          constructor
          · intro h
            rcases h with hDiv | hFun
            · exact Or.inl ⟨hEq.2.1, rawEq_diverges hEq.2.2 |>.mp hDiv.2⟩
            · rcases hFun with ⟨hTyped, body, hev, hV, hD⟩
              apply Or.inr
              refine ⟨hEq.2.1, body,
                (hEq.2.2.1 (.lam body)).mp hev, ?_, ?_⟩
              · intro a ha
                have haAll : AllTerms σ.erase a := V_subset_allTerms σ ha
                have happEq := semEq_app hEq haAll
                exact (semantic_equiv_VD happEq).1.mp (hV a ha)
              · intro a ha
                have haAll : AllTerms σ.erase a := D_subset_allTerms σ ha
                have happEq := semEq_app hEq haAll
                exact (semantic_equiv_VD happEq).2.1 (hD a ha)
          · intro h
            rcases h with hDiv | hFun
            · exact Or.inl ⟨hEq.1, rawEq_diverges hEq.2.2 |>.mpr hDiv.2⟩
            · rcases hFun with ⟨hTyped, body, hev, hV, hD⟩
              apply Or.inr
              refine ⟨hEq.1, body,
                (hEq.2.2.1 (.lam body)).mpr hev, ?_, ?_⟩
              · intro a ha
                have haAll : AllTerms σ.erase a := V_subset_allTerms σ ha
                have happEq := semEq_app hEq haAll
                exact (semantic_equiv_VD happEq).1.mpr (hV a ha)
              · intro a ha
                have haAll : AllTerms σ.erase a := D_subset_allTerms σ ha
                have happEq := semEq_app hEq haAll
                exact (semantic_equiv_VD happEq).2.mpr (hD a ha)
        · constructor
          · intro h
            unfold D LogicalModel.divergentSide operationalModel at h
            unfold D LogicalModel.divergentSide operationalModel
            by_cases hLazy : Ty.IsLazy (.arrow σ τ u)
            · simp only [hLazy, if_pos] at h
              simp only [hLazy, if_pos]
              exact False.elim h
            · simp only [hLazy] at h
              simp only [hLazy]
              by_cases hOuter' : Usage.lazy ≤ u
              · simp only [hOuter', if_pos] at h ⊢
                exact hEq.2.1
              · simp only [hOuter'] at h ⊢
                cases u with
                | strict =>
                    rcases h with hDiv | hFun
                    · exact Or.inl ⟨hEq.2.1,
                        rawEq_diverges hEq.2.2 |>.mp hDiv.2⟩
                    · rcases hFun with ⟨hTyped, body, hev, hStrict⟩
                      apply Or.inr
                      refine ⟨?_, body,
                        (hEq.2.2.1 (.lam body)).mp hev, ?_⟩
                      · simp only [LogicalModel.acceptable,
                          Usage.not_lazy_le_strict]
                        exact Or.inr ⟨hEq.2.1, body,
                          (hEq.2.2.1 (.lam body)).mp hev,
                          (fun (a : Term) (ha : V σ a) =>
                            D_subset_V τ ((semantic_equiv_VD
                              (semEq_app hEq (V_subset_allTerms σ ha))).2.mp
                              (hStrict a ha))),
                          (fun (a : Term) (ha : D σ a) =>
                            (semantic_equiv_VD
                              (semEq_app hEq (D_subset_allTerms σ ha))).2.mp
                              (hStrict a (D_subset_V σ ha)))⟩
                      · intro a ha
                        exact (semantic_equiv_VD
                          (semEq_app hEq (V_subset_allTerms σ ha))).2.mp
                          (hStrict a ha)
                | unknown => exact False.elim h
                | lazy => exact False.elim h
                | top => exact False.elim h
          · intro h
            unfold D LogicalModel.divergentSide operationalModel at h
            unfold D LogicalModel.divergentSide operationalModel
            by_cases hLazy : Ty.IsLazy (.arrow σ τ u)
            · simp only [hLazy, if_pos] at h
              simp only [hLazy, if_pos]
              exact False.elim h
            · simp only [hLazy] at h
              simp only [hLazy]
              by_cases hOuter' : Usage.lazy ≤ u
              · simp only [hOuter', if_pos] at h ⊢
                exact hEq.1
              · simp only [hOuter'] at h ⊢
                cases u with
                | strict =>
                    rcases h with hDiv | hFun
                    · exact Or.inl ⟨hEq.1,
                        rawEq_diverges hEq.2.2 |>.mpr hDiv.2⟩
                    · rcases hFun with ⟨hTyped, body, hev, hStrict⟩
                      apply Or.inr
                      refine ⟨?_, body,
                        (hEq.2.2.1 (.lam body)).mpr hev, ?_⟩
                      · simp only [LogicalModel.acceptable,
                          Usage.not_lazy_le_strict]
                        exact Or.inr ⟨hEq.1, body,
                          (hEq.2.2.1 (.lam body)).mpr hev,
                          (fun (a : Term) (ha : V σ a) =>
                            D_subset_V τ ((semantic_equiv_VD
                              (semEq_app hEq (V_subset_allTerms σ ha))).2.mpr
                              (hStrict a ha))),
                          (fun (a : Term) (ha : D σ a) =>
                            (semantic_equiv_VD
                              (semEq_app hEq (D_subset_allTerms σ ha))).2.mpr
                              (hStrict a (D_subset_V σ ha)))⟩
                      · intro a ha
                        exact (semantic_equiv_VD
                          (semEq_app hEq (V_subset_allTerms σ ha))).2.mpr
                          (hStrict a ha)
                | unknown => exact False.elim h
                | lazy => exact False.elim h
                | top => exact False.elim h

end Strictness

namespace Strictness

open Term

/-- A projection of a known pair is observationally equivalent to its selected
component.  Determinism is used only to identify the pair components when the
scrutinee is evaluated in the projection derivation. -/
theorem semEq_proj_left {σ τ : SimpleTy} {e e₁ e₂ : Term}
    (hE : AllTerms (.prod σ τ) e)
    (h₁ : AllTerms σ e₁)
    (_ : AllTerms τ e₂)
    (hev : Eval e (.pair e₁ e₂)) :
    SemEq σ (.proj true e) e₁ := by
  refine ⟨?_, h₁, ?_⟩
  · · rcases hE with ⟨hClosed, hTyped⟩
      exact ⟨hClosed, Term.HasType.projLeft hTyped⟩
  constructor
  · intro v
    constructor
    · intro h
      cases h with
      | projLeft hScrut hComp =>
          have hEq : Value.pair _ _ = Value.pair e₁ e₂ := eval_deterministic hScrut hev
          cases hEq
          exact hComp
    · intro h
      exact Eval.projLeft hev h
  · constructor
    · intro h
      cases h with
      | projScrutinee hErr =>
          exact False.elim (eval_not_evalErr hev hErr)
      | projLeftComponent hScrut hErrComp =>
          have hEq : Value.pair _ _ = Value.pair e₁ e₂ := eval_deterministic hScrut hev
          cases hEq
          exact hErrComp
    · intro h
      exact EvalErr.projLeftComponent hev h

/-- Right-projection version of `semEq_proj_left`. -/
theorem semEq_proj_right {σ τ : SimpleTy} {e e₁ e₂ : Term}
    (hE : AllTerms (.prod σ τ) e)
    (_ : AllTerms σ e₁)
    (h₂ : AllTerms τ e₂)
    (hev : Eval e (.pair e₁ e₂)) :
    SemEq τ (.proj false e) e₂ := by
  refine ⟨?_, h₂, ?_⟩
  · rcases hE with ⟨hClosed, hTyped⟩
    exact ⟨hClosed, Term.HasType.projRight hTyped⟩
  constructor
  · intro v
    constructor
    · intro h
      cases h with
      | projRight hScrut hComp =>
          have hEq := eval_deterministic hScrut hev
          cases hEq
          exact hComp
    · intro h
      exact Eval.projRight hev h
  · constructor
    · intro h
      cases h with
      | projScrutinee hErr =>
          exact False.elim (eval_not_evalErr hev hErr)
      | projRightComponent hScrut hErrComp =>
          have hEq := eval_deterministic hScrut hev
          cases hEq
          exact hErrComp
    · intro h
      exact EvalErr.projRightComponent hev h

end Strictness

namespace Strictness

open Term

/-- If the condition evaluates to zero, a conditional is observationally
 equivalent to its second branch.  The all-term hypotheses are supplied so the
 equivalence is at the simple type required by the logical relation. -/
theorem semEq_if_zero {σ : SimpleTy} {e₀ e₁ e₂ : Term}
    (hCond : Eval e₀ (.int 0))
    (hBranch : AllTerms σ e₂)
    (hIf : AllTerms σ (.ite e₀ e₁ e₂)) :
    SemEq σ (.ite e₀ e₁ e₂) e₂ := by
  refine ⟨hIf, hBranch, ?_⟩
  constructor
  · intro v
    constructor
    · intro hEval
      cases hEval with
      | ifZero hCond' hz hBranch' =>
          have hN := eval_deterministic hCond hCond'
          cases hN
          exact hBranch'
      | ifNonzero hCond' hnz _ =>
          have hN := eval_deterministic hCond hCond'
          cases hN
          exact False.elim (hnz rfl)
    · intro hEval
      exact Eval.ifZero hCond rfl hEval
  · constructor
    · intro hErr
      cases hErr with
      | ifCond hCondErr =>
        exfalso
        exact (eval_not_evalErr hCond) hCondErr
      | ifZeroBranch _ _ hBranchErr => exact hBranchErr
      | ifNonzeroBranch hCond' hnz _ =>
          have hN := eval_deterministic hCond hCond'
          cases hN
          exact False.elim (hnz rfl)
    · intro hBranchErr
      exact EvalErr.ifZeroBranch hCond rfl hBranchErr

/-- If the condition evaluates to a nonzero integer, a conditional is
 observationally equivalent to its first branch. -/
theorem semEq_if_nonzero {σ : SimpleTy} {e₀ e₁ e₂ : Term} {n : Int}
    (hCond : Eval e₀ (.int n))
    (hn : n ≠ 0)
    (hBranch : AllTerms σ e₁)
    (hIf : AllTerms σ (.ite e₀ e₁ e₂)) :
    SemEq σ (.ite e₀ e₁ e₂) e₁ := by
  refine ⟨hIf, hBranch, ?_⟩
  constructor
  · intro v
    constructor
    · intro hEval
      cases hEval with
      | ifZero hCond' hz _ =>
          have hN := eval_deterministic hCond hCond'
          cases hN
          exact False.elim (hn hz)
      | ifNonzero hCond' hnz hBranch' =>
          have hN := eval_deterministic hCond hCond'
          cases hN
          exact hBranch'
    · intro hEval
      exact Eval.ifNonzero hCond hn hEval
  · constructor
    · intro hErr
      cases hErr with
      | ifCond hCondErr =>
        exfalso
        exact (eval_not_evalErr hCond) hCondErr
      | ifZeroBranch hCond' hz _ =>
          have hN := eval_deterministic hCond hCond'
          cases hN
          exact False.elim (hn hz)
      | ifNonzeroBranch _ _ hBranchErr => exact hBranchErr
    · intro hBranchErr
      exact EvalErr.ifNonzeroBranch hCond hn hBranchErr

end Strictness
