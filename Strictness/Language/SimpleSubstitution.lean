import Strictness.Language.Erasure
import Strictness.Language.Substitution

namespace Strictness

open Term

namespace Term

/-- A successful lookup on the left of an appended context is preserved. -/
theorem lookup_append_left {Γ Δ : Ctx} {i : Nat} {τ : SimpleTy}
    (h : lookup Γ i = some τ) : lookup (Γ ++ Δ) i = some τ := by
  induction Γ generalizing i with
  | nil => simp [lookup] at h
  | cons σ Γ ih =>
      cases i with
      | zero => simpa [lookup] using h
      | succ i =>
          simp only [lookup] at h ⊢
          exact ih h

/-- A lookup beyond a bound prefix reaches the appended outer context. -/
theorem lookup_append_right {B Γ : Ctx} {i : Nat} {τ : SimpleTy}
    (h : lookup (B ++ Γ) (B.length + i) = some τ) :
    lookup Γ i = some τ := by
  induction B with
  | nil => simpa using h
    | cons σ B ih =>
            exact ih (by
                simpa [lookup, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)

/-- A lookup within the bound prefix is recovered from an appended context. -/
theorem lookup_append_bound {B Γ : Ctx} {i : Nat} {τ : SimpleTy}
    (h : lookup (B ++ Γ) i = some τ) (hi : i < B.length) :
    lookup B i = some τ := by
  induction B generalizing i with
  | nil => simp at hi
  | cons σ B ih =>
      cases i with
      | zero => simpa [lookup] using h
      | succ i =>
          simp only [lookup, List.length_cons] at h hi ⊢
          exact ih h (Nat.lt_of_succ_lt_succ hi)

/-- A term typed in the empty context is closed. -/
theorem hasType_nil_closed {e : Term} {τ : SimpleTy}
    (h : HasType [] e τ) : Closed e := by
  have lookup_lt : ∀ {Γ : Ctx} {i : Nat} {τ : SimpleTy},
      lookup Γ i = some τ → i < Γ.length := by
    intro Γ i τ h
    induction Γ generalizing i τ with
    | nil => simp [lookup] at h
    | cons σ Γ ih =>
        cases i with
        | zero => simp
        | succ i =>
            simp only [lookup, List.length_cons] at h ⊢
            exact Nat.succ_lt_succ (ih h)
  have go : ∀ {Γ : Ctx} {e : Term} {τ : SimpleTy},
      HasType Γ e τ → ClosedAt Γ.length e := by
    intro Γ e τ h
    induction h with
    | var h => exact lookup_lt h
    | int => trivial
    | lam h ih =>
        simpa [ClosedAt, List.length_cons, Nat.add_comm] using ih
    | fix h ih =>
        simpa [ClosedAt, List.length_cons, Nat.add_comm] using ih
    | app h₁ h₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
    | pair h₁ h₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
    | projLeft h ih => exact ih
    | projRight h ih => exact ih
    | op o h₁ h₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
    | ite h₀ h₁ h₂ ih₀ ih₁ ih₂ => exact ⟨ih₀, ih₁, ih₂⟩
    | letE h₁ h₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
    | omega => trivial
    | err => trivial
  simpa [Closed] using go h

/-- Simple typing admits weakening by appending an outer context.
De Bruijn indices are unchanged because the new bindings are farther out. -/
theorem weaken_right : ∀ {Γ Δ : Ctx} {e : Term} {τ : SimpleTy},
    HasType Γ e τ → HasType (Γ ++ Δ) e τ
  | Γ, Δ, _, _, HasType.var h =>
      HasType.var (lookup_append_left h)
  | _, _, _, _, HasType.int => HasType.int
  | Γ, Δ, _, _, HasType.lam h => by
      simpa [List.cons_append] using HasType.lam (weaken_right h)
  | Γ, Δ, _, _, HasType.fix h => by
      simpa [List.cons_append] using HasType.fix (weaken_right h)
  | _, _, _, _, HasType.app h₁ h₂ =>
      HasType.app (weaken_right h₁) (weaken_right h₂)
  | _, _, _, _, HasType.pair h₁ h₂ =>
      HasType.pair (weaken_right h₁) (weaken_right h₂)
  | _, _, _, _, HasType.projLeft h =>
      HasType.projLeft (weaken_right h)
  | _, _, _, _, HasType.projRight h =>
      HasType.projRight (weaken_right h)
  | _, _, _, _, HasType.op o h₁ h₂ =>
      HasType.op o (weaken_right h₁) (weaken_right h₂)
  | _, _, _, _, HasType.ite h₀ h₁ h₂ =>
      HasType.ite (weaken_right h₀) (weaken_right h₁) (weaken_right h₂)
  | _, _, _, _, HasType.letE h₁ h₂ => by
      simpa [List.cons_append] using
        HasType.letE (weaken_right h₁) (weaken_right h₂)
  | _, _, _, _, HasType.omega => HasType.omega
  | _, _, _, _, HasType.err => HasType.err

/-- Applying a substitution to a simply typed term preserves its type.
The theorem is generalized by a bound prefix so that lambda and let bodies
can cross De Bruijn binders. -/
theorem hasType_applyAt {B Γ : Ctx} {e : Term} {τ : SimpleTy}
    {ρ : Substitution}
    (h : HasType (B ++ Γ) e τ)
    (hρ : ∀ i σ, lookup Γ i = some σ → HasType [] (ρ i) σ) :
    HasType B (Substitution.applyAt ρ B.length e) τ := by
  induction e generalizing B Γ τ with
  | var i =>
      cases h with
      | var hlookup =>
          by_cases hbound : i < B.length
          · have hb := lookup_append_bound hlookup hbound
            simp [Substitution.applyAt, hbound]
            exact HasType.var hb
          · have hle : B.length ≤ i := Nat.le_of_not_gt hbound
            obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
            have hout := lookup_append_right hlookup
            have hs := hρ j _ hout
            have hc := hasType_nil_closed hs
            have hnot : ¬ B.length + j < B.length := by omega
            simp [Substitution.applyAt, hnot, Term.shift_eq_of_closed hc]
            simpa using (weaken_right (Γ := []) (Δ := B) hs)
  | int n =>
      cases h
      exact HasType.int
  | lam body ih =>
      cases h with
      | lam hbody =>
          simp [Substitution.applyAt]
          exact HasType.lam (ih (B := _ :: B) (Γ := Γ) hbody hρ)
  | fix body ih =>
      cases h with
      | fix hbody =>
          simp only [Substitution.applyAt]
          apply HasType.fix
          have hbody' := ih (B := τ :: B) (Γ := Γ) hbody hρ
          simpa only [List.length_cons] using hbody'
  | app e₁ e₂ ih₁ ih₂ =>
      cases h with
      | app h₁ h₂ =>
          simp [Substitution.applyAt]
          exact HasType.app (ih₁ h₁ hρ) (ih₂ h₂ hρ)
  | pair e₁ e₂ ih₁ ih₂ =>
      cases h with
      | pair h₁ h₂ =>
          simp [Substitution.applyAt]
          exact HasType.pair (ih₁ h₁ hρ) (ih₂ h₂ hρ)
  | proj b e ih =>
      cases h with
      | projLeft h' =>
          simp [Substitution.applyAt]
          exact HasType.projLeft (ih h' hρ)
      | projRight h' =>
          simp [Substitution.applyAt]
          exact HasType.projRight (ih h' hρ)
  | op o e₁ e₂ ih₁ ih₂ =>
      cases h with
      | op o h₁ h₂ =>
          simp [Substitution.applyAt]
          exact HasType.op o (ih₁ h₁ hρ) (ih₂ h₂ hρ)
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
      cases h with
      | ite h₀ h₁ h₂ =>
          simp [Substitution.applyAt]
          exact HasType.ite (ih₀ h₀ hρ) (ih₁ h₁ hρ) (ih₂ h₂ hρ)
  | letE e₁ e₂ ih₁ ih₂ =>
      cases h with
      | letE h₁ h₂ =>
          simp [Substitution.applyAt]
          exact HasType.letE (ih₁ h₁ hρ)
            (ih₂ (B := _ :: B) (Γ := Γ) h₂ hρ)
  | omega => exact HasType.omega
  | err => exact HasType.err

/-- Top-level semantic substitution preserves simple typing. -/
theorem hasType_apply {Γ : Ctx} {e : Term} {τ : SimpleTy} {ρ : Substitution}
    (h : HasType Γ e τ)
    (hρ : ∀ i σ, lookup Γ i = some σ → HasType [] (ρ i) σ) :
    HasType [] (Substitution.apply ρ e) τ := by
  simpa [Substitution.apply] using hasType_applyAt (B := []) h hρ

end Term

end Strictness
