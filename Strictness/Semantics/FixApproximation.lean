import Strictness.Semantics.FixSemantics

namespace Strictness

namespace Term

/-- Finite unfolding of a fix body. Index zero in body is the recursive
variable; all other free variables remain open. The zero approximation is
the semantic divergence marker. -/
def fixApprox (body : Term) : Nat → Term
  | 0 => .omega
  | n + 1 => instantiate body (fixApprox body n)

/-- Every finite unfolding retains the simple type of the fix term,
including in an open context. -/
theorem fixApprox_hasType
    {Γ : Ctx} {A : SimpleTy} {body : Term}
    (hBody : HasType (A :: Γ) body A) (n : Nat) :
    HasType Γ (fixApprox body n) A := by
  induction n with
  | zero =>
      exact HasType.omega
  | succ n ih =>
      exact hasType_instantiate_open hBody ih

end Term

/-- Finite unfoldings of a closed simply typed fix term are closed and
simply typed at the same type. -/
theorem fixApprox_mem_allTerms
    {A : SimpleTy} {body : Term}
    (hFix : AllTerms A (.fix body)) (n : Nat) :
    AllTerms A (Term.fixApprox body n) := by
  have hTyped : Term.HasType [] (Term.fixApprox body n) A := by
    cases hFix.2 with
    | fix hBody =>
        exact Term.fixApprox_hasType hBody n
  exact ⟨Term.hasType_nil_closed hTyped, hTyped⟩

namespace Substitution

/-- Closing the outer variables commutes with finite unfolding. The
recursive variable remains bound in the closed body on the right. -/
theorem apply_fixApprox_of_closed_images
    (ρ : Substitution) (body : Term)
    (hρ : ∀ i, Term.Closed (ρ i)) (n : Nat) :
    apply ρ (Term.fixApprox body n) =
      Term.fixApprox (applyAt ρ 1 body) n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [Term.fixApprox]
      rw [apply_instantiate_of_closed_images
        ρ body (Term.fixApprox body n) hρ]
      rw [ih]

end Substitution

end Strictness
