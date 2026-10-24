import Strictness.Semantics.Interpretation
import Strictness.Operational.OperationalFacts

namespace Strictness

open Usage
open Term

/-- Pointwise inclusion of term predicates. -/
def TermSet.Subset (X Y : TermSet Term) : Prop :=
  ∀ ⦃e : Term⦄, X e → Y e

/-- Every term in a semantic set is closed. This exposes the `U_τ` part of
the semantic-set definitions, and is used when a De Bruijn substitution crosses a binder. -/
theorem V_closed : ∀ {τ : Ty} {e : Term}, V τ e → Term.Closed e
  | .int u, e, h => by
      unfold V LogicalModel.acceptable operationalModel at h
      by_cases hu : Usage.lazy ≤ u
      · simp only [hu, if_pos] at h
        exact h.1
      · simp only [hu] at h
        rcases h with hdiv | hnum
        · exact hdiv.1.1
        · exact hnum.1
  | .prod σ τ u, e, h => by
      unfold V LogicalModel.acceptable operationalModel at h
      by_cases hu : Usage.lazy ≤ u
      · simp only [hu, if_pos] at h
        exact h.1
      · simp only [hu] at h
        rcases h with hdiv | hpair
        · exact hdiv.1.1
        · exact hpair.1.1
  | .arrow σ τ u, e, h => by
      unfold V LogicalModel.acceptable operationalModel at h
      by_cases hu : Usage.lazy ≤ u
      · simp only [hu, if_pos] at h
        exact h.1
      · simp only [hu] at h
        rcases h with hdiv | hfun
        · exact hdiv.1.1
        · exact hfun.1.1

/-- Every term in a divergent-side semantic set is closed. -/
theorem D_closed : ∀ {τ : Ty} {e : Term}, D τ e → Term.Closed e
  | .int u, e, h => by
      unfold D LogicalModel.divergentSide operationalModel at h
      by_cases hLazy : Ty.IsLazy (.int u)
      · simp only [hLazy, if_pos] at h
        exact False.elim h
      · simp only [hLazy] at h
        by_cases hOuter : Usage.lazy ≤ u
        · simp only [hOuter, if_pos] at h
          exact h.1
        · simp only [hOuter] at h
          cases u with
          | strict => exact h.1.1
          | unknown => exact False.elim h
          | lazy => exact False.elim h
          | top => exact False.elim h
  | .prod σ τ u, e, h => by
      unfold D LogicalModel.divergentSide operationalModel at h
      by_cases hLazy : Ty.IsLazy (.prod σ τ u)
      · simp only [hLazy, if_pos] at h
        exact False.elim h
      · simp only [hLazy] at h
        by_cases hOuter : Usage.lazy ≤ u
        · simp only [hOuter, if_pos] at h
          exact h.1
        · simp only [hOuter] at h
          cases u with
          | unknown | strict =>
              rcases h with hdiv | hpair
              · exact hdiv.1.1
              · rcases hpair with hpair | hpair
                · exact hpair.1.1
                · exact hpair.1.1
          | lazy => exact False.elim h
          | top => exact False.elim h
  | .arrow σ τ u, e, h => by
      unfold D LogicalModel.divergentSide operationalModel at h
      by_cases hLazy : Ty.IsLazy (.arrow σ τ u)
      · simp only [hLazy, if_pos] at h
        exact False.elim h
      · simp only [hLazy] at h
        by_cases hOuter : Usage.lazy ≤ u
        · simp only [hOuter, if_pos] at h
          exact h.1
        · simp only [hOuter] at h
          cases u with
          | strict =>
              rcases h with hdiv | hfun
              · exact hdiv.1.1
              · exact V_closed hfun.1
          | unknown => exact False.elim h
          | lazy => exact False.elim h
          | top => exact False.elim h


/-- The semantic error marker is a closed, simply typed term of every simple type. -/
theorem err_mem_allTerms (τ : SimpleTy) : AllTerms τ .err := by
  constructor
  · trivial
  · exact Term.HasType.err

/-- Ω is a closed, simply typed term of every simple type. -/
theorem omega_mem_allTerms (τ : SimpleTy) : AllTerms τ .omega := by
  constructor
  · trivial
  · exact Term.HasType.omega

/-- A strict outer usage makes a type non-Lazy. -/
theorem not_lazy_of_outer_strict {τ : Ty}
    (hOuter : τ.outer = strict) : ¬ Ty.IsLazy τ := by
  cases τ with
  | int u =>
      change u = strict at hOuter
      subst u
      exact Usage.not_lazy_le_strict
  | prod σ τ u =>
      change u = strict at hOuter
      subst u
      intro h
      exact Usage.not_lazy_le_strict h.1
  | arrow σ τ u =>
      change u = strict at hOuter
      subst u
      exact Usage.not_lazy_le_strict

/-- A top outer usage makes a type non-Lazy. -/
theorem not_lazy_of_outer_top {τ : Ty}
    (hOuter : τ.outer = top) : ¬ Ty.IsLazy τ := by
  cases τ with
  | int u =>
      change u = top at hOuter
      subst u
      exact fun h => h
  | prod σ τ u =>
      change u = top at hOuter
      subst u
      intro h
      exact (fun h => h) h.1
  | arrow σ τ u =>
      change u = top at hOuter
      subst u
      exact fun h => h

/-- Ω belongs to D(Int^S). -/
theorem omega_mem_D_int_strict : D (Ty.int strict) .omega := by
  unfold D LogicalModel.divergentSide operationalModel
  simp only [not_lazy_of_outer_strict (τ := .int strict) rfl,
    Usage.not_lazy_le_strict, if_false]
  change AllTerms .int .omega ∧ Term.Diverges .omega
  exact ⟨omega_mem_allTerms .int, Term.omega_diverges⟩

/-- Ω belongs to D((σ × τ)^S), independently of the component annotations. -/
theorem omega_mem_D_prod_strict (σ τ : Ty) :
    D (Ty.prod σ τ strict) .omega := by
  unfold D LogicalModel.divergentSide operationalModel
  simp only [not_lazy_of_outer_strict (τ := .prod σ τ strict) rfl,
    Usage.not_lazy_le_strict, if_false]
  change DivergentTerms (.prod σ.erase τ.erase) .omega ∨ _
  left
  exact ⟨omega_mem_allTerms (.prod σ.erase τ.erase), Term.omega_diverges⟩

/-- Ω belongs to D((σ → τ)^S), independently of the component annotations. -/
theorem omega_mem_D_arrow_strict (σ τ : Ty) :
    D (Ty.arrow σ τ strict) .omega := by
  unfold D LogicalModel.divergentSide operationalModel
  simp only [not_lazy_of_outer_strict (τ := .arrow σ τ strict) rfl,
    Usage.not_lazy_le_strict, if_false]
  change DivergentTerms (.arrow σ.erase τ.erase) .omega ∨ _
  left
  exact ⟨omega_mem_allTerms (.arrow σ.erase τ.erase), Term.omega_diverges⟩

theorem D_eq_allTerms_of_outer_top {τ : Ty}
    (hOuter : τ.outer = top) : D τ = AllTerms τ.erase := by
  rw [D_def]
  apply LogicalModel.divergentSide_eq_allTerms_of_not_lazy operationalModel
    (not_lazy_of_outer_top hOuter)
  simpa [hOuter] using Usage.lazy_le_top

theorem D_eq_allTerms_of_not_lazy {τ : Ty}
    (hNotLazy : ¬ Ty.IsLazy τ) (hOuter : lazy ≤ τ.outer) :
    D τ = AllTerms τ.erase := by
  rw [D_def]
  exact LogicalModel.divergentSide_eq_allTerms_of_not_lazy operationalModel
    hNotLazy hOuter

/-- Ω belongs to D(τ) whenever the outer usage of τ is strict.

This is exactly the semantic membership needed in the strict observation case;
it makes no stronger claim about arbitrary non-lazy types.
-/
theorem omega_mem_D_of_outer_strict {τ : Ty}
    (hOuter : τ.outer = strict) : D τ .omega := by
  cases τ with
  | int u =>
      change u = strict at hOuter
      subst u
      exact omega_mem_D_int_strict
  | prod σ τ u =>
      change u = strict at hOuter
      subst u
      exact omega_mem_D_prod_strict σ τ
  | arrow σ τ u =>
      change u = strict at hOuter
      subst u
      exact omega_mem_D_arrow_strict σ τ

/-- Ω belongs to D for every non-Lazy type.  This is the key fact for
the converse direction of the empty-set characterization: the D-set contains either
the divergence set or the whole erased type in every non-Lazy outer case. -/
theorem omega_mem_D_of_not_lazy {τ : Ty}
    (hNotLazy : ¬ Ty.IsLazy τ) : D τ .omega := by
  cases τ with
  | int u =>
      cases u with
      | unknown => exact False.elim (hNotLazy (by simp [Ty.IsLazy, Usage.Le]))
      | strict => exact omega_mem_D_int_strict
      | lazy => exact False.elim (hNotLazy (by simp [Ty.IsLazy, Usage.Le]))
      | top =>
          rw [D_eq_allTerms_of_outer_top rfl]
          exact omega_mem_allTerms .int
  | prod σ τ u =>
      cases u with
      | unknown =>
          by_cases hLazy : Ty.IsLazy (.prod σ τ unknown)
          · exact False.elim (hNotLazy hLazy)
          · unfold D LogicalModel.divergentSide operationalModel
            simp only [hLazy, Usage.not_lazy_le_unknown,
              if_false, TermSet.union]
            exact Or.inl (And.intro (omega_mem_allTerms (.prod σ.erase τ.erase))
              omega_diverges)
      | strict =>
          by_cases hLazy : Ty.IsLazy (.prod σ τ strict)
          · exact False.elim (hNotLazy hLazy)
          · unfold D LogicalModel.divergentSide operationalModel
            simp only [hLazy, Usage.not_lazy_le_strict,
              if_false, TermSet.union]
            exact Or.inl (And.intro (omega_mem_allTerms (.prod σ.erase τ.erase))
              omega_diverges)
      | lazy =>
          by_cases hOuter : Ty.IsLazy (.prod σ τ lazy)
          · exact False.elim (hNotLazy hOuter)
          · rw [D_eq_allTerms_of_not_lazy hNotLazy Usage.lazy_le_lazy]
            exact omega_mem_allTerms (.prod σ.erase τ.erase)
      | top =>
          rw [D_eq_allTerms_of_outer_top rfl]
          exact omega_mem_allTerms (.prod σ.erase τ.erase)
  | arrow σ τ u =>
      cases u with
      | unknown => exact False.elim (hNotLazy (by simp [Ty.IsLazy, Usage.Le]))
      | strict => exact omega_mem_D_arrow_strict σ τ
      | lazy => exact False.elim (hNotLazy (by simp [Ty.IsLazy, Usage.Le]))
      | top =>
          rw [D_eq_allTerms_of_outer_top rfl]
          exact omega_mem_allTerms (.arrow σ.erase τ.erase)

/-- Non-Lazy types have all divergent closed terms on the D-side. -/
theorem divergentTerms_subset_D_of_not_lazy {τ : Ty}
    (hNotLazy : ¬ Ty.IsLazy τ) :
    TermSet.Subset (DivergentTerms τ.erase) (D τ) := by
  cases τ with
  | int u =>
      cases u with
      | unknown => exact False.elim (hNotLazy (by simp [Ty.IsLazy, Usage.Le]))
      | strict => exact (by
          intro e he
          unfold D LogicalModel.divergentSide operationalModel
          simp only [not_lazy_of_outer_strict (τ := .int strict) rfl,
            Usage.not_lazy_le_strict,  if_false]
          exact he)
      | lazy => exact False.elim (hNotLazy (by simp [Ty.IsLazy, Usage.Le]))
      | top => exact (by
          intro e he
          rw [D_eq_allTerms_of_outer_top rfl]
          exact he.1)
  | prod σ τ u =>
      cases u with
      | unknown => exact (by
          intro e he
          unfold D LogicalModel.divergentSide operationalModel
          simp only [hNotLazy, Usage.not_lazy_le_unknown,
            if_false, TermSet.union]
          exact Or.inl he)
      | strict => exact (by
          intro e he
          unfold D LogicalModel.divergentSide operationalModel
          simp only [hNotLazy, Usage.not_lazy_le_strict,
            if_false, TermSet.union]
          exact Or.inl he)
      | lazy => exact (by
          intro e he
          rw [D_eq_allTerms_of_not_lazy hNotLazy Usage.lazy_le_lazy]
          exact he.1)
      | top => exact (by
          intro e he
          rw [D_eq_allTerms_of_outer_top rfl]
          exact he.1)
  | arrow σ τ u =>
      cases u with
      | unknown => exact False.elim (hNotLazy (by simp [Ty.IsLazy, Usage.Le]))
      | strict => exact (by
          intro e he
          unfold D LogicalModel.divergentSide operationalModel
          simp only [not_lazy_of_outer_strict (τ := .arrow σ τ strict) rfl,
            Usage.not_lazy_le_strict,  if_false,
            TermSet.union]
          exact Or.inl he)
      | lazy => exact False.elim (hNotLazy (by simp [Ty.IsLazy, Usage.Le]))
      | top => exact (by
          intro e he
          rw [D_eq_allTerms_of_outer_top rfl]
          exact he.1)

/-- Laziness implies an empty D-set. -/
theorem lazy_implies_D_empty {τ : Ty} (h : Ty.IsLazy τ) :
    D τ = TermSet.empty :=
  LogicalModel.divergentSide_eq_empty_of_lazy operationalModel h

/-- A D-set is empty exactly when its type is Lazy. -/
theorem D_empty_iff_lazy {τ : Ty} :
    D τ = TermSet.empty ↔ Ty.IsLazy τ := by
  constructor
  · intro hEmpty
    by_cases hLazy : Ty.IsLazy τ
    · exact hLazy
    · have hOmega : D τ .omega := omega_mem_D_of_not_lazy hLazy
      rw [hEmpty] at hOmega
      exact False.elim hOmega
  · exact lazy_implies_D_empty

/-- For a lazy outer usage, V is the whole erased simple type. -/
theorem V_eq_allTerms_of_outer_lazy {τ : Ty}
    (hOuter : τ.outer = lazy) : V τ = AllTerms τ.erase := by
  rw [V_def]
  apply LogicalModel.acceptable_eq_allTerms_of_outer_lazy operationalModel
  simpa [hOuter] using Usage.lazy_le_lazy

/-- For a top outer usage, V is the whole erased simple type. -/
theorem V_eq_allTerms_of_outer_top {τ : Ty}
    (hOuter : τ.outer = top) : V τ = AllTerms τ.erase := by
  rw [V_def]
  apply LogicalModel.acceptable_eq_allTerms_of_outer_lazy
  simpa [hOuter] using Usage.lazy_le_top

/-- In particular, `err` can be used for the lazy substitution test. -/
theorem err_mem_V_of_outer_lazy {τ : Ty}
    (hOuter : τ.outer = lazy) : V τ .err := by
  rw [V_eq_allTerms_of_outer_lazy hOuter]
  exact err_mem_allTerms τ.erase

/-- In particular, `err` can be used for the top substitution test in V. -/
theorem err_mem_V_of_outer_top {τ : Ty}
    (hOuter : τ.outer = top) : V τ .err := by
  rw [V_eq_allTerms_of_outer_top hOuter]
  exact err_mem_allTerms τ.erase

/-- In particular, `err` is in the D-set at top outer annotation. -/
theorem err_mem_D_of_outer_top {τ : Ty}
    (hOuter : τ.outer = top) : D τ .err := by
  rw [D_eq_allTerms_of_outer_top hOuter]
  exact err_mem_allTerms τ.erase

/-- `D(Int^?)` is empty because `? ≤ L`, so `Int^?` is Lazy. -/
theorem D_int_unknown_eq_empty :
    D (Ty.int unknown) = TermSet.empty := by
  simp [D_def, LogicalModel.divergentSide, Ty.IsLazy, Usage.Le]

/-- `Int^?` is Lazy in the four-element usage order. -/
theorem lazy_int_unknown : Ty.IsLazy (Ty.int unknown) := by
  exact trivial

/-- The strict-test membership fact using `σ^S` notation. -/
theorem omega_mem_D_reannotate_strict (τ : Ty) :
    D (τ.reannotate strict) .omega := by
  apply omega_mem_D_of_outer_strict
  exact Ty.outer_reannotate strict τ

/-- The lazy-test characterization. -/
theorem V_reannotate_lazy_eq_allTerms (τ : Ty) :
    V (τ.reannotate lazy) = AllTerms τ.erase := by
  simpa using V_eq_allTerms_of_outer_lazy (τ := τ.reannotate lazy)
    (Ty.outer_reannotate lazy τ)

/-- The top-test characterization for V. -/
theorem V_reannotate_top_eq_allTerms (τ : Ty) :
    V (τ.reannotate top) = AllTerms τ.erase := by
  simpa using V_eq_allTerms_of_outer_top (τ := τ.reannotate top)
    (Ty.outer_reannotate top τ)

/-- The top-test characterization for D. -/
theorem D_reannotate_top_eq_allTerms (τ : Ty) :
    D (τ.reannotate top) = AllTerms τ.erase := by
  simpa using D_eq_allTerms_of_outer_top (τ := τ.reannotate top)
    (Ty.outer_reannotate top τ)

/-- Ω is not an error. -/
theorem omega_not_evalErr : ¬ EvalErr .omega := by
  intro h
  cases h

/-- `err` does not evaluate to an ordinary value. -/
theorem err_not_eval : ¬ ∃ v, Eval .err v := by
  rintro ⟨v, h⟩
  cases h

/-- `err` is an error. -/
theorem err_evalErr : EvalErr .err := EvalErr.err

/-- Pair membership is monotone in both component predicates. -/
theorem pairTerms_mono {σ τ : SimpleTy} {X X' Y Y' : TermSet Term}
    (hX : TermSet.Subset X X') (hY : TermSet.Subset Y Y') :
    TermSet.Subset (PairTerms σ τ X Y) (PairTerms σ τ X' Y') := by
  intro e h
  rcases h with ⟨hTyped, e₁, e₂, hev, hx, hy⟩
  exact ⟨hTyped, e₁, e₂, hev, hX hx, hY hy⟩

/-- Function-value membership is monotone in all four logical arguments. -/
theorem functionTerms_mono {σ τ : SimpleTy}
    {VX VX' DX DX' VY VY' DY DY' : TermSet Term}
    (hVX : TermSet.Subset VX' VX)
    (hDX : TermSet.Subset DX' DX)
    (hVY : TermSet.Subset VY VY')
    (hDY : TermSet.Subset DY DY') :
    TermSet.Subset
      (FunctionTerms σ τ VX DX VY DY)
      (FunctionTerms σ τ VX' DX' VY' DY') := by
  intro e h
  rcases h with ⟨hTyped, body, hev, hV, hD⟩
  refine ⟨hTyped, body, hev, ?_, ?_⟩
  · intro a ha
    exact hVY (hV a (hVX ha))
  · intro a ha
    exact hDY (hD a (hDX ha))

/-- Strict-function membership is monotone when the underlying V-arrow set,
the V-domain set, and the D-codomain set grow. -/
theorem strictFunctionTerms_mono {σ τ : SimpleTy}
    {VA VA' VX VX' DY DY' : TermSet Term}
    (hVA : TermSet.Subset VA VA')
    (hVX : TermSet.Subset VX' VX)
    (hDY : TermSet.Subset DY DY') :
    TermSet.Subset
      (StrictFunctionTerms σ τ VA VX DY)
      (StrictFunctionTerms σ τ VA' VX' DY') := by
  intro e h
  rcases h with ⟨hVAe, body, hev, hStrict⟩
  refine ⟨hVA hVAe, body, hev, ?_⟩
  intro a ha
  exact hDY (hStrict a (hVX ha))

end Strictness
