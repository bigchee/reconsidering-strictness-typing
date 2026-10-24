import Strictness.Compatibility.Omega.Observation
import Strictness.Compatibility.Semantics

/-!
Both type interpretations are stable under selected loop replacements.

The function case compares applications to the same arbitrary argument,
using reflexivity of the partial replacement relation on that argument.
The complete-expansion results follow as a special case. Small-step
interpretations are connected through semantic correspondence.
-/

namespace Strictness

/-- A semantic set is stable under selected changes of loop representation. -/
def OmegaStable (X : TermSet Term) : Prop :=
  ∀ {e e'}, Term.OmegaEq e e' → X e → X e'

private theorem omegaStable_all (A : SimpleTy) : OmegaStable (AllTerms A) := by
  intro e e' h he
  exact ⟨(h.closedAt 0).mp he.1, h.hasType he.2⟩

private theorem omegaStable_divergent (A : SimpleTy) : OmegaStable (DivergentTerms A) := by
  intro e e' h he
  exact ⟨omegaStable_all A h he.1, (omegaEq_diverges_iff h).mp he.2⟩

private theorem omegaStable_numeral : OmegaStable NumeralTerms := by
  intro e e' h he
  rcases he with ⟨hc, ht, n, hn⟩
  rcases eval_omegaEq hn h with ⟨v, hv, hr⟩
  cases hr with
  | int n => exact ⟨(h.closedAt 0).mp hc, h.hasType ht, n, hv⟩

private theorem omegaStable_empty : OmegaStable TermSet.empty := by
  intro e e' h he
  exact False.elim he

private theorem omegaStable_union {X Y : TermSet Term}
    (hx : OmegaStable X) (hy : OmegaStable Y) : OmegaStable (TermSet.union X Y) := by
  intro e e' h he
  exact he.elim (fun he => Or.inl (hx h he)) (fun he => Or.inr (hy h he))

private theorem omegaStable_pair (A B : SimpleTy) {X Y : TermSet Term}
    (hx : OmegaStable X) (hy : OmegaStable Y) : OmegaStable (PairTerms A B X Y) := by
  intro e e' h he
  rcases he with ⟨ha, a, b, hev, hax, hby⟩
  rcases eval_omegaEq hev h with ⟨v, hv, hr⟩
  cases hr with
  | pair hab hbb => exact ⟨omegaStable_all _ h ha, _, _, hv, hx hab hax, hy hbb hby⟩

private theorem omegaStable_function (A B : SimpleTy) (VX DX : TermSet Term)
    {VY DY : TermSet Term} (hy : OmegaStable VY) (hdy : OmegaStable DY) :
    OmegaStable (FunctionTerms A B VX DX VY DY) := by
  intro e e' h he
  rcases he with ⟨ha, body, hev, hV, hD⟩
  rcases eval_omegaEq hev h with ⟨v, hv, hr⟩
  cases hr with
  | lam hb =>
    exact ⟨omegaStable_all _ h ha, _, hv,
      fun a ha => hy (.app h (.refl a)) (hV a ha),
      fun a ha => hdy (.app h (.refl a)) (hD a ha)⟩

private theorem omegaStable_strict (A B : SimpleTy) (VX : TermSet Term)
    {VA DY : TermSet Term} (hva : OmegaStable VA) (hdy : OmegaStable DY) :
    OmegaStable (StrictFunctionTerms A B VA VX DY) := by
  intro e e' h he
  rcases he with ⟨ha, body, hev, hD⟩
  rcases eval_omegaEq hev h with ⟨v, hv, hr⟩
  cases hr with
  | lam hb => exact ⟨hva h ha, _, hv, fun a ha => hdy (.app h (.refl a)) (hD a ha)⟩

/-- Both interpretations are invariant under partial replacement, including
under retained constructors and in functions applied to arbitrary arguments. -/
theorem omegaStable_VD (τ : Ty) : OmegaStable (V τ) ∧ OmegaStable (D τ) := by
  induction τ with
  | int u =>
    constructor
    · change OmegaStable (LogicalModel.acceptable operationalModel (.int u))
      rw [LogicalModel.acceptable]
      split
      · exact omegaStable_all _
      · exact omegaStable_union (omegaStable_divergent _) omegaStable_numeral
    · change OmegaStable (LogicalModel.divergentSide operationalModel (.int u))
      rw [LogicalModel.divergentSide.eq_def]
      dsimp only
      split
      · exact omegaStable_empty
      · split
        · exact omegaStable_all _
        · cases u <;> first | exact omegaStable_divergent _ | exact omegaStable_empty
  | prod σ τ u ihσ ihτ =>
    constructor
    · change OmegaStable (LogicalModel.acceptable operationalModel (.prod σ τ u))
      rw [LogicalModel.acceptable]
      split
      · exact omegaStable_all _
      · exact omegaStable_union (omegaStable_divergent _) (omegaStable_pair _ _ ihσ.1 ihτ.1)
    · change OmegaStable (LogicalModel.divergentSide operationalModel (.prod σ τ u))
      rw [LogicalModel.divergentSide.eq_def]
      dsimp only
      split
      · exact omegaStable_empty
      · split
        · exact omegaStable_all _
        · cases u <;> first
            | exact omegaStable_empty
            | exact omegaStable_union (omegaStable_divergent _)
                (omegaStable_union (omegaStable_pair _ _ ihσ.2 ihτ.1)
                  (omegaStable_pair _ _ ihσ.1 ihτ.2))
  | arrow σ τ u ihσ ihτ =>
    have hv : OmegaStable (V (.arrow σ τ u)) := by
      change OmegaStable (LogicalModel.acceptable operationalModel (.arrow σ τ u))
      rw [LogicalModel.acceptable]
      split
      · exact omegaStable_all _
      · exact omegaStable_union (omegaStable_divergent _)
          (omegaStable_function _ _ _ _ ihτ.1 ihτ.2)
    refine ⟨hv, ?_⟩
    change OmegaStable (LogicalModel.divergentSide operationalModel (.arrow σ τ u))
    rw [LogicalModel.divergentSide.eq_def]
    dsimp only
    split
    · exact omegaStable_empty
    · split
      · exact omegaStable_all _
      · cases u with
        | unknown | lazy | top => exact omegaStable_empty
        | strict =>
            exact omegaStable_union (omegaStable_divergent _)
              (omegaStable_strict σ.erase τ.erase (V σ) hv ihτ.2)

theorem omegaEq_semantic_VD {e e' : Term} (h : Term.OmegaEq e e') (τ : Ty) :
    (V τ e ↔ V τ e') ∧ (D τ e ↔ D τ e') := by
  have hs := omegaStable_VD τ
  exact ⟨⟨hs.1 h, hs.1 h.symm⟩, ⟨hs.2 h, hs.2 h.symm⟩⟩

theorem expandOmega_semantic_VD (e : Term) (τ : Ty) :
    (V τ e ↔ V τ e.expandOmega) ∧ (D τ e ↔ D τ e.expandOmega) :=
  omegaEq_semantic_VD (Term.omegaEq_expandOmega e) τ

theorem expandOmega_smallStep_VD (e : Term) (τ : Ty) :
    (SmallStep.V τ e ↔ SmallStep.V τ e.expandOmega) ∧
    (SmallStep.D τ e ↔ SmallStep.D τ e.expandOmega) := by
  rw [SmallStep.V_eq, SmallStep.D_eq]
  exact expandOmega_semantic_VD e τ

end Strictness
