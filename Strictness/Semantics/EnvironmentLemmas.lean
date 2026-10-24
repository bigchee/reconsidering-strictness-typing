import Strictness.Language.Environment
import Strictness.Language.SimpleTyping
import Strictness.Semantics.SemanticEnvironment
import Strictness.Semantics.SemanticSubtype

namespace Strictness

open Usage

namespace Env

/-- A successful pointwise `+` on nonempty environments decomposes into a
head type composition and a successful tail composition. -/
theorem plus_cons_iff {σ τ : Ty} {Γ Δ Θ : Env} :
    plus (σ :: Γ) (τ :: Δ) = some Θ ↔
      ∃ ρ Ξ, Ty.plus σ τ = some ρ ∧ plus Γ Δ = some Ξ ∧ Θ = ρ :: Ξ := by
    cases hσ : Ty.combine Usage.add σ τ <;>
        cases hΓ : Env.combine Usage.add Γ Δ <;>
        simp [plus, combine, Ty.plus, hσ, hΓ];
        constructor <;> intro h <;> exact h.symm


/-- The corresponding decomposition for pointwise `⊓`. -/
theorem cap_cons_iff {σ τ : Ty} {Γ Δ Θ : Env} :
    cap (σ :: Γ) (τ :: Δ) = some Θ ↔
      ∃ ρ Ξ, Ty.cap σ τ = some ρ ∧ cap Γ Δ = some Ξ ∧ Θ = ρ :: Ξ := by
    cases hσ : Ty.combine Usage.meet σ τ <;>
        cases hΓ : Env.combine Usage.meet Γ Δ <;>
        simp [cap, combine, Ty.cap, hσ, hΓ];
        constructor <;> intro h <;> exact h.symm

/-- At every position of a successful environment `+`, the result type is
exactly the pointwise composition of the two input types. -/
theorem plus_lookup_iff {Γ Δ Θ : Env} (h : plus Γ Δ = some Θ) :
    ∀ {i ρ}, lookup Θ i = some ρ ↔
      ∃ σ τ, lookup Γ i = some σ ∧ lookup Δ i = some τ ∧ Ty.plus σ τ = some ρ := by
  induction Γ generalizing Δ Θ with
  | nil =>
      cases Δ with
      | nil =>
          have h0: Θ = [] := by simpa [plus, combine] using h
          subst Θ
          intro i ρ
          cases i <;> simp [lookup]
      | cons τ Δ =>
          simp [plus, combine] at h
  | cons σ Γ ih =>
      cases Δ with
      | nil =>
          simp [plus, combine] at h
      | cons τ Δ =>
          intro i ρ
          cases i with
          | zero =>
              rw [plus_cons_iff] at h
              rcases h with ⟨ρ0, Ξ, hρ0, htail, rfl⟩
              simp only [lookup]
              constructor
              · intro h
                cases h
                exact ⟨σ, τ, rfl, rfl, hρ0⟩
              · rintro ⟨σ', τ', hs', ht', hplus'⟩
                cases hs'
                cases ht'
                have hEq : ρ0 = ρ := Option.some.inj (hρ0.symm.trans hplus')
                simp [hEq]
          | succ i =>
              rw [plus_cons_iff] at h
              rcases h with ⟨ρ0, Ξ, hρ0, htail, rfl⟩
              simp only [lookup]
              exact ih htail

/-- The analogous pointwise lookup characterization for `⊓`. -/
theorem cap_lookup_iff {Γ Δ Θ : Env} (h : cap Γ Δ = some Θ) :
    ∀ {i ρ}, lookup Θ i = some ρ ↔
      ∃ σ τ, lookup Γ i = some σ ∧ lookup Δ i = some τ ∧ Ty.cap σ τ = some ρ := by
  induction Γ generalizing Δ Θ with
  | nil =>
      cases Δ with
      | nil =>
          have h0: Θ = [] := by simpa [cap, combine] using h
          subst Θ
          intro i ρ
          cases i <;> simp [lookup]
      | cons τ Δ =>
          simp [cap, combine] at h
  | cons σ Γ ih =>
      cases Δ with
      | nil =>
          simp [cap, combine] at h
      | cons τ Δ =>
          intro i ρ
          cases i with
          | zero =>
              rw [cap_cons_iff] at h
              rcases h with ⟨ρ0, Ξ, hρ0, htail, rfl⟩
              simp only [lookup]
              constructor
              · intro h
                cases h
                exact ⟨σ, τ, rfl, rfl, hρ0⟩
              · rintro ⟨σ', τ', hs', ht', hcap'⟩
                cases hs'
                cases ht'
                have hEq : ρ0 = ρ := Option.some.inj (hρ0.symm.trans hcap')
                simp [hEq]
          | succ i =>
              rw [cap_cons_iff] at h
              rcases h with ⟨ρ0, Ξ, hρ0, htail, rfl⟩
              simp only [lookup]
              exact ih htail


/-- Given successful `+` and lookups of both input environments, the
corresponding result lookup exists and its type is their pointwise sum. -/
theorem plus_lookup_of_inputs {Γ Δ Θ : Env} (h : plus Γ Δ = some Θ) :
    ∀ {i σ τ}, lookup Γ i = some σ → lookup Δ i = some τ →
      ∃ ρ, lookup Θ i = some ρ ∧ Ty.plus σ τ = some ρ := by
  induction Γ generalizing Δ Θ with
  | nil =>
      cases Δ <;> simp [lookup, plus, combine] at *
  | cons σ₀ Γ ih =>
      cases Δ with
      | nil => simp [plus, combine] at h
      | cons τ₀ Δ =>
          intro i σ τ hσ hτ
          cases i with
          | zero =>
              rw [plus_cons_iff] at h
              rcases h with ⟨ρ, Ξ, hρ, htail, rfl⟩
              simp only [lookup] at hσ hτ ⊢
              cases hσ
              cases hτ
              exact ⟨ρ, rfl, hρ⟩
          | succ i =>
              rw [plus_cons_iff] at h
              rcases h with ⟨ρ, Ξ, hρ, htail, rfl⟩
              simp only [lookup] at hσ hτ ⊢
              exact ih htail hσ hτ

/-- The corresponding input-to-result lookup theorem for `⊓`. -/
theorem cap_lookup_of_inputs {Γ Δ Θ : Env} (h : cap Γ Δ = some Θ) :
    ∀ {i σ τ}, lookup Γ i = some σ → lookup Δ i = some τ →
      ∃ ρ, lookup Θ i = some ρ ∧ Ty.cap σ τ = some ρ := by
  induction Γ generalizing Δ Θ with
  | nil =>
      cases Δ <;> simp [lookup, cap, combine] at *
  | cons σ₀ Γ ih =>
      cases Δ with
      | nil => simp [cap, combine] at h
      | cons τ₀ Δ =>
          intro i σ τ hσ hτ
          cases i with
          | zero =>
              rw [cap_cons_iff] at h
              rcases h with ⟨ρ, Ξ, hρ, htail, rfl⟩
              simp only [lookup] at hσ hτ ⊢
              cases hσ
              cases hτ
              exact ⟨ρ, rfl, hρ⟩
          | succ i =>
              rw [cap_cons_iff] at h
              rcases h with ⟨ρ, Ξ, hρ, htail, rfl⟩
              simp only [lookup] at hσ hτ ⊢
              exact ih htail hσ hτ


/-- A successful lookup identifies a position inside the environment. -/
theorem lookup_some_lt_length {Γ : Env} {i : Nat} {τ : Ty}
    (h : lookup Γ i = some τ) : i < Γ.length := by
  induction Γ generalizing i τ with
  | nil => simp [lookup] at h
  | cons σ Γ ih =>
      cases i with
      | zero => simp
      | succ i =>
          simp only [lookup] at h
          have hi := ih h
          simp only [List.length_cons]
          exact Nat.succ_lt_succ hi

/-- Every position below the environment length has a corresponding lookup. -/
theorem lookup_exists_of_lt_length {Γ : Env} {i : Nat}
    (hi : i < Γ.length) : ∃ τ, lookup Γ i = some τ := by
  induction Γ generalizing i with
  | nil => simp at hi
  | cons σ Γ ih =>
      cases i with
      | zero => exact ⟨σ, rfl⟩
      | succ i =>
          simp only [List.length_cons] at hi
          exact ih (Nat.lt_of_succ_lt_succ hi)

/-- Environments of the same length have a lookup at the same positions. -/
theorem lookup_exists_of_same_length {Γ Δ : Env}
    (hlen : Γ.length = Δ.length) {i : Nat} {τ : Ty}
    (h : lookup Γ i = some τ) : ∃ σ, lookup Δ i = some σ := by
  apply lookup_exists_of_lt_length
  rw [← hlen]
  exact lookup_some_lt_length h

end Env

end Strictness


namespace Strictness

open Term

/-- A lookup in the lower environment of an environment subtyping pair can
be promoted to a lookup in the upper environment, with a type-level subtype. -/
theorem lookup_supertype_of_subtype {Γ Δ : Env} (hSub : Env.Subtype Γ Δ)
    {i : Nat} {τ : Ty} (hLookup : Env.lookup Γ i = some τ) :
    ∃ τ', Env.lookup Δ i = some τ' ∧ Ty.Subtype τ τ' := by
  induction Γ generalizing Δ i τ with
  | nil =>
      cases Δ with
      | nil =>
          simp [Env.lookup] at hLookup
      | cons σ Δ =>
          simp [Env.Subtype] at hSub
  | cons τ₁ Γ ih =>
      cases Δ with
      | nil =>
          simp [Env.Subtype] at hSub
      | cons σ Δ =>
          simp only [Env.Subtype] at hSub
          rcases hSub with ⟨hτ, hΓ⟩
          cases i with
          | zero =>
              simp only [Env.lookup] at hLookup
              cases hLookup
              exact ⟨σ, rfl, hτ⟩
          | succ i =>
              simp only [Env.lookup] at hLookup
              obtain ⟨τ', hτ', hSubτ'⟩ := ih hΓ hLookup
              exact ⟨τ', by simpa [Env.lookup] using hτ', hSubτ'⟩

/-- A lookup in the upper environment of an environment subtyping pair can be
pulled back to the lower environment, with a type-level subtype. -/
theorem lookup_subtype_of_subtype {Γ Δ : Env} (hSub : Env.Subtype Γ Δ)
    {i : Nat} {τ : Ty} (hLookup : Env.lookup Δ i = some τ) :
    ∃ σ, Env.lookup Γ i = some σ ∧ Ty.Subtype σ τ := by
  induction Γ generalizing Δ i τ with
  | nil =>
      cases Δ with
      | nil =>
          simp [Env.lookup] at hLookup
      | cons σ Δ =>
          simp [Env.Subtype] at hSub
  | cons τ₁ Γ ih =>
      cases Δ with
      | nil =>
          simp [Env.Subtype] at hSub
      | cons σ Δ =>
          simp only [Env.Subtype] at hSub
          rcases hSub with ⟨hτ, hΓ⟩
          cases i with
          | zero =>
              simp only [Env.lookup] at hLookup
              cases hLookup
              exact ⟨τ₁, rfl, hτ⟩
          | succ i =>
              simp only [Env.lookup] at hLookup
              obtain ⟨σ', hσ', hSubσ'⟩ := ih hΓ hLookup
              exact ⟨σ', by simpa [Env.lookup] using hσ', hSubσ'⟩


/-- Validity is monotone with respect to environment subtyping: a substitution
valid for a smaller-demand environment is valid for the larger environment. -/
theorem valid_of_env_subtype {Γ Δ : Env} {ρ : Substitution}
    (hSub : Env.Subtype Γ Δ) (hValid : Valid Γ ρ) :
    Valid Δ ρ := by
  refine ⟨hValid.1, ?_⟩
  intro i τ' hLookup
  obtain ⟨τ, hLookup', hTy⟩ := lookup_subtype_of_subtype hSub hLookup
  exact (semantic_subtype hTy).1 (hValid.2 i τ hLookup')

/-- D-satisfaction is monotone with respect to environment subtyping. -/
theorem satisfiesD_of_env_subtype {Γ Δ : Env} {ρ : Substitution}
    (hSub : Env.Subtype Γ Δ) (hD : SatisfiesD Γ ρ) :
    SatisfiesD Δ ρ := by
  rcases hD with ⟨i, τ, hLookup, hDτ⟩
  obtain ⟨τ', hLookup', hTy⟩ := lookup_supertype_of_subtype hSub hLookup
  exact ⟨i, τ', hLookup', (semantic_subtype hTy).2 hDτ⟩


end Strictness
