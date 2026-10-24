import Strictness.Semantics.SemanticEnvironment
import Strictness.Semantics.SemanticBasic
import Strictness.Semantics.SemanticSubtype
import Strictness.Semantics.SemanticSubstitution

namespace Strictness

open Usage
open Term

/-- The T-Const V-case: an integer literal belongs to every `V(Int^u)`. -/
theorem fundamental_const_V {Γ : Env} {n : Int} {u : Usage}
    {ρ : Substitution} (hValid : Valid (Env.scale u Γ) ρ) :
    V (.int u) (Substitution.apply ρ (.int n)) := by
  simp only [Substitution.apply_int]
  unfold V LogicalModel.acceptable operationalModel
  cases u with
  | unknown =>
      simp only [Usage.not_lazy_le_unknown]
      change DivergentTerms .int (.int n) ∨ NumeralTerms (.int n)
      exact Or.inr ⟨by trivial, Term.HasType.int, n, Eval.int⟩
  | strict =>
      simp only [Usage.not_lazy_le_strict]
      change DivergentTerms .int (.int n) ∨ NumeralTerms (.int n)
      exact Or.inr ⟨by trivial, Term.HasType.int, n, Eval.int⟩
  | lazy =>
      simp only [Usage.lazy_le_lazy, if_pos]
      change AllTerms .int (.int n)
      exact ⟨by trivial, Term.HasType.int⟩
  | top =>
      simp only [Usage.lazy_le_top, if_pos]
      change AllTerms .int (.int n)
      exact ⟨by trivial, Term.HasType.int⟩

/-- The T-Const D-case: D-satisfaction of the (Lazy) unused environment is
impossible, so the D-clause is obtained by contradiction. -/
theorem fundamental_const_D {Γ : Env} {n : Int} {u : Usage}
    (hLazy : Env.IsLazy Γ)
    {ρ : Substitution} (hValid : Valid (Env.scale u Γ) ρ)
    (hD : SatisfiesD (Env.scale u Γ) ρ) :
    D (.int u) (Substitution.apply ρ (.int n)) := by
  cases u with
  | unknown =>
      exfalso
      exact not_satisfiesD_of_lazy (Env.isLazy_unknown_scale Γ) hD
  | strict =>
      exfalso
      rw [Env.strict_scale] at hD
      exact not_satisfiesD_of_lazy hLazy hD
  | lazy =>
      exfalso
      exact not_satisfiesD_of_lazy (Env.isLazy_lazy_scale Γ) hD
  | top =>
      simp only [Substitution.apply_int]
      rw [D_eq_allTerms_of_outer_top rfl]
      exact ⟨by trivial, Term.HasType.int⟩

/-- T-Var, V-case: the referenced variable is directly selected by the
head of the semantic substitution. -/
theorem fundamental_var_V {τ : Ty} {Γ : Env} {ρ : Substitution}
    (hValid : Valid (τ :: Env.scale τ.outer Γ) ρ) :
    V τ (Substitution.apply ρ (.var 0)) := by
  simp only [Substitution.apply_var]
  exact hValid.2 0 τ rfl

/-- T-Var, D-case with the complete environment.  The proof separates the
outer annotation of the referenced type.  For `?` and `S`, any D-witness in
the tail is impossible because the unused tail is Lazy; for `L`, a head
witness directly proves the conclusion (the whole L-outer type need not be
Lazy because products can retain inner demand); `⊤` has an all-term D-set. -/
theorem fundamental_var_D {τ : Ty} {Γ : Env} {ρ : Substitution}
    (hLazy : Env.IsLazy Γ)
    (hValid : Valid (τ :: Env.scale τ.outer Γ) ρ)
    (hD : SatisfiesD (τ :: Env.scale τ.outer Γ) ρ) :
    D τ (Substitution.apply ρ (.var 0)) := by
  simp only [Substitution.apply_var]
  cases hOuter : τ.outer with
  | unknown =>
      have hTailLazy : Env.IsLazy (Env.scale unknown Γ) :=
        Env.isLazy_scale_of_isLazy (by trivial) hLazy
      rcases satisfiesD_cons_iff.mp hD with hHead | hTail
      · exact hHead
      · exact False.elim
          (not_satisfiesD_of_lazy hTailLazy (by simpa only [hOuter] using hTail))
  | lazy =>
      have hTailLazy : Env.IsLazy (Env.scale lazy Γ) :=
        Env.isLazy_scale_of_isLazy (by trivial) hLazy
      rcases satisfiesD_cons_iff.mp hD with hHead | hTail
      · exact hHead
      · exact False.elim
          (not_satisfiesD_of_lazy hTailLazy (by simpa only [hOuter] using hTail))
  | strict =>
      rcases satisfiesD_cons_iff.mp hD with hHead | hTail
      · exact hHead
      · have hTailLazy : Env.IsLazy (Env.scale strict Γ) :=
          Env.isLazy_scale_of_isLazy (by trivial) hLazy
        exact False.elim
          (not_satisfiesD_of_lazy hTailLazy (by simpa only [hOuter] using hTail))
  | top =>
      have hHeadV : V τ (ρ 0) := hValid.2 0 τ rfl
      have hAll : AllTerms τ.erase (ρ 0) := V_subset_allTerms τ hHeadV
      rw [D_eq_allTerms_of_outer_top hOuter]
      exact hAll

/-- The semantic `T-Var` cases lift through an unused De Bruijn binding.
This is the representation-level counterpart of selecting an arbitrary named
variable from the paper's context. -/
theorem fundamental_varSkip_V {Γ : Env} {τ σ : Ty} {i : Nat}
    {ρ : Substitution}
    (ihV : ∀ {ρ : Substitution}, Valid Γ ρ →
      V τ (Substitution.apply ρ (.var i)))
    (hValid : Valid (Ty.scale τ.outer σ :: Γ) ρ) :
    V τ (Substitution.apply ρ (.var (i + 1))) := by
  have hTail := (valid_cons_iff.mp hValid).2.2
  have hV := ihV hTail
  have hV' : V τ (Term.shift 1 0 (ρ (i + 1))) := by
    simpa only [Substitution.apply_var] using hV
  rw [Term.shift_eq_of_closed (hValid.1 (i + 1))] at hV'
  simpa only [Substitution.apply_var] using hV'

theorem fundamental_varSkip_D {Γ : Env} {τ σ : Ty} {i : Nat}
    {ρ : Substitution}
    (hLazy : Ty.IsLazy σ)
    (ihV : ∀ {ρ : Substitution}, Valid Γ ρ →
      V τ (Substitution.apply ρ (.var i)))
    (ihD : ∀ {ρ : Substitution}, Valid Γ ρ → SatisfiesD Γ ρ →
      D τ (Substitution.apply ρ (.var i)))
    (hValid : Valid (Ty.scale τ.outer σ :: Γ) ρ)
  (hD : SatisfiesD (Ty.scale τ.outer σ :: Γ) ρ) :
    D τ (Substitution.apply ρ (.var (i + 1))) := by
  have hTailValid := (valid_cons_iff.mp hValid).2.2
  cases hOuter : τ.outer with
  | unknown =>
      rcases satisfiesD_cons_iff.mp hD with hHead | hTail
      · have hHeadLazy : Ty.IsLazy (Ty.scale unknown σ) := Ty.unknown_scale_lazy σ
        have hBad : D (Ty.scale unknown σ) (ρ 0) := by
          simpa [hOuter] using hHead
        rw [lazy_implies_D_empty hHeadLazy] at hBad
        exact False.elim hBad
      · have hDShift := ihD hTailValid hTail
        have hDShift' : D τ (Term.shift 1 0 (ρ (i + 1))) := by
          simpa only [Substitution.apply_var] using hDShift
        rw [Term.shift_eq_of_closed (hValid.1 (i + 1))] at hDShift'
        simpa only [Substitution.apply_var] using hDShift'
  | strict =>
      rcases satisfiesD_cons_iff.mp hD with hHead | hTail
      · have hHeadLazy : Ty.IsLazy (Ty.scale strict σ) := by
          simpa only [Ty.strict_scale] using hLazy
        have hBad : D (Ty.scale strict σ) (ρ 0) := by
          simpa [hOuter] using hHead
        rw [lazy_implies_D_empty hHeadLazy] at hBad
        exact False.elim hBad
      · have hDShift := ihD hTailValid hTail
        have hDShift' : D τ (Term.shift 1 0 (ρ (i + 1))) := by
          simpa only [Substitution.apply_var] using hDShift
        rw [Term.shift_eq_of_closed (hValid.1 (i + 1))] at hDShift'
        simpa only [Substitution.apply_var] using hDShift'
  | lazy =>
      rcases satisfiesD_cons_iff.mp hD with hHead | hTail
      · have hHeadLazy : Ty.IsLazy (Ty.scale lazy σ) := Ty.lazy_scale_lazy σ
        have hBad : D (Ty.scale lazy σ) (ρ 0) := by
          simpa [hOuter] using hHead
        rw [lazy_implies_D_empty hHeadLazy] at hBad
        exact False.elim hBad
      · have hDShift := ihD hTailValid hTail
        have hDShift' : D τ (Term.shift 1 0 (ρ (i + 1))) := by
          simpa only [Substitution.apply_var] using hDShift
        rw [Term.shift_eq_of_closed (hValid.1 (i + 1))] at hDShift'
        simpa only [Substitution.apply_var] using hDShift'
  | top =>
      have hVShift := ihV hTailValid
      have hVShift' : V τ (Term.shift 1 0 (ρ (i + 1))) := by
        simpa only [Substitution.apply_var] using hVShift
      have hV : V τ (ρ (i + 1)) := by
        rw [Term.shift_eq_of_closed (hValid.1 (i + 1))] at hVShift'
        exact hVShift'
      have hAll : AllTerms τ.erase (ρ (i + 1)) := V_subset_allTerms τ hV
      rw [D_eq_allTerms_of_outer_top hOuter]
      simpa only [Substitution.apply_var] using hAll

end Strictness
