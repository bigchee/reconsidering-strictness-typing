import Strictness.Language.Type

namespace Strictness

open Usage

/-- typing environments, represented as De Bruijn contexts.
The head is the nearest binding. -/
abbrev Env := List Ty

namespace Env

/-- Pointwise structural subtyping on contexts with the same bindings. -/
def Subtype : Env → Env → Prop
  | [], [] => True
  | τ :: Γ, σ :: Δ => Ty.Subtype τ σ ∧ Subtype Γ Δ
  | _, _ => False

/-- Every declaration in an environment is Lazy. -/
def IsLazy : Env → Prop
  | [] => True
  | τ :: Γ => Ty.IsLazy τ ∧ IsLazy Γ

/-- Pointwise scalar multiplication of an environment. -/
def scale (u : Usage) : Env → Env
  | [] => []
  | τ :: Γ => Ty.scale u τ :: scale u Γ

@[simp] theorem scale_nil (u : Usage) : scale u [] = [] := rfl

@[simp] theorem scale_cons (u : Usage) (τ : Ty) (Γ : Env) :
    scale u (τ :: Γ) = Ty.scale u τ :: scale u Γ := rfl

/-- Partial pointwise environment composition. -/
def combine (op : Usage → Usage → Usage) : Env → Env → Option Env
  | [], [] => some []
  | τ :: Γ, σ :: Δ => do
      let θ ← Ty.combine op τ σ
      let Ξ ← combine op Γ Δ
      pure (θ :: Ξ)
  | _, _ => none

def plus : Env → Env → Option Env := combine Usage.add
def cap : Env → Env → Option Env := combine Usage.meet

/-- De Bruijn lookup, nearest binding first. -/
def lookup : Env → Nat → Option Ty
  | [], _ => none
  | τ :: _, 0 => some τ
  | _ :: Γ, n + 1 => lookup Γ n

/-- Insert a declaration at a De Bruijn position.  The index is allowed to
point immediately after the final declaration; larger indices leave the
environment unchanged and are ruled out by the accompanying bound in
`Typing.var`. -/
def insertAt : Nat → Ty → Env → Env
  | 0, τ, Γ => τ :: Γ
  | _ + 1, _, [] => []
  | i + 1, τ, σ :: Γ => σ :: insertAt i τ Γ


@[simp] theorem strict_scale (Γ : Env) : scale strict Γ = Γ := by
  induction Γ <;> simp [scale, Ty.strict_scale, *]

/-- Scaling by `?` makes every environment entry Lazy, independently of the
original environment. -/
theorem isLazy_unknown_scale (Γ : Env) : IsLazy (scale unknown Γ) := by
  induction Γ with
  | nil => trivial
  | cons τ Γ ih =>
      exact ⟨Ty.unknown_scale_lazy τ, ih⟩

/-- Scaling by `L` makes every environment entry Lazy, independently of the
original environment. -/
theorem isLazy_lazy_scale (Γ : Env) : IsLazy (scale lazy Γ) := by
  induction Γ with
  | nil => trivial
  | cons τ Γ ih =>
      exact ⟨Ty.lazy_scale_lazy τ, ih⟩

/-- Scaling a Lazy environment by `?`, `S`, or `L` preserves Laziness. -/
theorem isLazy_scale_of_isLazy : ∀ {u : Usage} {Γ : Env},
    u ≠ top → IsLazy Γ → IsLazy (scale u Γ)
  | unknown, Γ, _, hΓ => by
      induction Γ with
      | nil => trivial
      | cons τ Γ ih =>
          exact ⟨Ty.unknown_scale_lazy τ, ih hΓ.2⟩
  | strict, Γ, _, hΓ => by
      simpa [Ty.strict_scale] using hΓ
  | lazy, Γ, _, hΓ => by
      induction Γ with
      | nil => trivial
      | cons τ Γ ih =>
          exact ⟨Ty.lazy_scale_lazy τ, ih hΓ.2⟩
  | top, Γ, h, hΓ => by
      contradiction


@[simp] theorem lookup_zero (τ : Ty) (Γ : Env) : lookup (τ :: Γ) 0 = some τ := rfl

@[simp] theorem lookup_succ (τ : Ty) (Γ : Env) (i : Nat) :
    lookup (τ :: Γ) (i + 1) = lookup Γ i := rfl

/-- The declaration inserted at a bounded position is found at exactly that
position. -/
theorem lookup_insertAt {Γ : Env} {i : Nat} {τ : Ty}
    (hi : i ≤ Γ.length) : lookup (insertAt i τ Γ) i = some τ := by
  induction Γ generalizing i with
  | nil =>
      have hzero : i = 0 := Nat.eq_zero_of_le_zero (by simpa using hi)
      subst i
      rfl
  | cons σ Γ ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simp only [List.length_cons] at hi
          exact ih (Nat.le_of_succ_le_succ hi)

/-- Lookup commutes with pointwise scaling. -/
theorem lookup_scale {u : Usage} {Γ : Env} {i : Nat} {τ : Ty}
    (hi : lookup Γ i = some τ) :
    lookup (scale u Γ) i = some (Ty.scale u τ) := by
  induction Γ generalizing i τ with
  | nil =>
      simp [lookup] at hi
  | cons σ Γ ih =>
      cases i with
      | zero =>
          simp only [lookup] at hi ⊢
          cases hi
          rfl
      | succ i =>
          exact ih hi

@[simp] theorem subtype_nil : Subtype [] [] := trivial

@[simp] theorem lazy_nil : IsLazy [] := trivial

@[simp] theorem lazy_cons_iff (τ : Ty) (Γ : Env) :
    IsLazy (τ :: Γ) ↔ Ty.IsLazy τ ∧ IsLazy Γ := Iff.rfl

@[simp] theorem scale_length (u : Usage) (Γ : Env) :
    (scale u Γ).length = Γ.length := by
  induction Γ <;> simp [scale, *]

/-- Pointwise composition preserves the context length when defined. -/
theorem plus_some_length {Γ Δ Θ : Env}
    (h : plus Γ Δ = some Θ) : Γ.length = Δ.length := by
  induction Γ generalizing Δ Θ with
  | nil =>
      cases Δ <;> simp [plus, combine] at h; simp
  | cons τ Γ ih =>
      cases Δ with
      | nil => simp [plus, combine] at h
      | cons σ Δ =>
            simp only [plus, combine] at h
            cases hτ : Ty.combine Usage.add τ σ with
            | none =>
                simp [hτ] at h
            | some θ =>
                cases hΓ : combine Usage.add Γ Δ with
                | none =>
                    simp [hτ, hΓ] at h
                | some Ξ =>
                    simp [hτ, hΓ] at h
                    have := ih hΓ
                    simp [this]

/-- The same length fact for meet-based composition. -/
theorem cap_some_length {Γ Δ Θ : Env}
    (h : cap Γ Δ = some Θ) : Γ.length = Δ.length := by
  induction Γ generalizing Δ Θ with
  | nil =>
      cases Δ <;> simp [cap, combine] at h; simp
  | cons τ Γ ih =>
      cases Δ with
      | nil => simp [cap, combine] at h
      | cons σ Δ =>
          simp only [cap, combine] at h
          cases hτ : Ty.combine Usage.meet τ σ with
            | none =>
                simp [hτ] at h
            | some θ =>
                cases hΓ : combine Usage.meet Γ Δ with
                | none =>
                    simp [hτ, hΓ] at h
                | some Ξ =>
                    simp [hτ, hΓ] at h
                    have := ih hΓ
                    simp [this]

/-- Pointwise subtyping implies equal context length. -/
theorem subtype_length : ∀ {Γ Δ : Env}, Subtype Γ Δ → Γ.length = Δ.length
  | [], [], _ => rfl
  | τ :: Γ, σ :: Δ, h => by
      simp only [List.length_cons]
      rw [subtype_length h.2]
  | _ :: _, [], h => False.elim h
  | [], _ :: _, h => False.elim h

end Env

end Strictness
