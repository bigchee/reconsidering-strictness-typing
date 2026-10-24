import Strictness.Language.Environment
import Strictness.Language.SimpleTyping

namespace Strictness

open Usage
open Term

namespace Ty

/-- subtyping never changes the erased simple type. -/
theorem subtype_erase {σ τ : Ty} (h : Ty.Subtype σ τ) :
    σ.erase = τ.erase := by
  induction h with
  | int huv =>
      rfl
  | prod hσ hτ huv ihσ ihτ =>
      simp only [Ty.erase]
      rw [ihσ, ihτ]
  | arrow hσ hτ huv ihσ ihτ =>
      simp only [Ty.erase]
      rw [ihσ, ihτ]

theorem congrArg₂ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ) {x x' : α} {y y' : β} (hx : x = x') (hy : y = y') : f x y = f x' y' := by simp_all

/-- Successful type composition preserves the erased simple type. -/
theorem combine_erase_of_some (op : Usage → Usage → Usage) :
    ∀ {σ τ ρ : Ty}, Ty.combine op σ τ = some ρ →
      σ.erase = τ.erase ∧ ρ.erase = σ.erase
  | .int u, .int v, .int w, h => by
      simp [Ty.combine] at h
      cases h
      exact ⟨rfl, rfl⟩
  | .prod σ₁ τ₁ u, .prod σ₂ τ₂ v, .prod ρ₁ ρ₂ w, h => by
      cases hσ : Ty.combine op σ₁ σ₂ with
      | none => simp [Ty.combine, hσ] at h
      | some σ' =>
          cases hτ : Ty.combine op τ₁ τ₂ with
          | none => simp [Ty.combine, hσ, hτ] at h
          | some τ' =>
            simp [Ty.combine, hσ, hτ] at h
            rcases h with ⟨hσρ, hτρ, _⟩

            have hσeq : σ₁.erase = σ₂.erase :=
              (combine_erase_of_some op hσ).1
            have hσ'eq : σ'.erase = σ₁.erase :=
              (combine_erase_of_some op hσ).2
            have hτeq : τ₁.erase = τ₂.erase :=
              (combine_erase_of_some op hτ).1
            have hτ'eq : τ'.erase = τ₁.erase :=
              (combine_erase_of_some op hτ).2

            change
              σ₁.erase.prod τ₁.erase = σ₂.erase.prod τ₂.erase ∧
              ρ₁.erase.prod ρ₂.erase = σ₁.erase.prod τ₁.erase

            constructor
            · exact congrArg₂ SimpleTy.prod hσeq hτeq
            · rw [← hσρ, ← hτρ, hσ'eq, hτ'eq]

  | .arrow σ₁ τ₁ u, .arrow σ₂ τ₂ v, .arrow ρ₁ ρ₂ w, h => by
    simp [Ty.combine] at h
    rcases h with ⟨hσ, hτ, hσρ, hτρ, _⟩
    subst σ₂
    subst τ₂
    subst ρ₁
    subst ρ₂
    exact ⟨rfl, rfl⟩
    | .int _, .prod _ _ _, _, h => by simp [Ty.combine] at h
    | .int _, .arrow _ _ _, _, h => by simp [Ty.combine] at h
    | .prod _ _ _, .int _, _, h => by simp [Ty.combine] at h
    | .prod _ _ _, .arrow _ _ _, _, h => by simp [Ty.combine] at h
    | .arrow _ _ _, .int _, _, h => by simp [Ty.combine] at h
    | .arrow _ _ _, .prod _ _ _, _, h => by simp [Ty.combine] at h
    | .int _, .int _, .prod _ _ _, h => by simp [Ty.combine] at h
    | .int _, .int _, .arrow _ _ _, h => by simp [Ty.combine] at h
    | .prod σ₁ τ₁ u, .prod σ₂ τ₂ v, .int _, h => by
            cases hσ : Ty.combine op σ₁ σ₂ <;>
                cases hτ : Ty.combine op τ₁ τ₂ <;>
                simp [Ty.combine, hσ, hτ] at h
    | .prod σ₁ τ₁ u, .prod σ₂ τ₂ v, .arrow _ _ _, h => by
            cases hσ : Ty.combine op σ₁ σ₂ <;>
                cases hτ : Ty.combine op τ₁ τ₂ <;>
                simp [Ty.combine, hσ, hτ] at h
    | .arrow _ _ _, .arrow _ _ _, .int _, h => by simp [Ty.combine] at h
    | .arrow _ _ _, .arrow _ _ _, .prod _ _ _, h => by simp [Ty.combine] at h


end Ty

namespace Env

/-- Erase all usage annotations in an environment. -/
def erase : Env → Term.Ctx
  | [] => []
  | τ :: Γ => τ.erase :: erase Γ

@[simp] theorem erase_nil : erase [] = [] := rfl
@[simp] theorem erase_cons (τ : Ty) (Γ : Env) :
    erase (τ :: Γ) = τ.erase :: erase Γ := rfl

@[simp] theorem erase_scale (u : Usage) (Γ : Env) :
    erase (scale u Γ) = erase Γ := by
  induction Γ <;> simp [scale, erase, *]

/-- Erasure commutes with De Bruijn lookup. -/
theorem erase_lookup_iff {Γ : Env} {i : Nat} {τ : SimpleTy} :
    Term.lookup (erase Γ) i = some τ ↔
      ∃ σ, Env.lookup Γ i = some σ ∧ σ.erase = τ := by
  induction Γ generalizing i τ with
  | nil =>
      cases i <;> simp [erase, Env.lookup, Term.lookup]
  | cons σ Γ ih =>
      cases i with
      | zero =>
          simp [erase, Env.lookup, Term.lookup]
      | succ i =>
          simpa [erase, Env.lookup, Term.lookup] using (ih (i := i) (τ := τ))

/-- Successful pointwise `+` preserves the erased simple context. -/
theorem plus_erase_of_some {Γ Δ Θ : Env} (h : Env.plus Γ Δ = some Θ) :
    erase Γ = erase Δ ∧ erase Θ = erase Γ := by
  induction Γ generalizing Δ Θ with
  | nil =>
      cases Δ with
      | nil =>
          cases Θ <;> simp [Env.plus, Env.combine, erase] at h ⊢
      | cons σ Δ => simp [Env.plus, Env.combine] at h
  | cons σ Γ ih =>
      cases Δ with
      | nil => simp [Env.plus, Env.combine] at h
      | cons τ Δ =>
                    change
                        (Ty.combine Usage.add σ τ >>= fun ρ =>
                            Env.combine Usage.add Γ Δ >>= fun Ξ => some (ρ :: Ξ)) = some Θ at h
                    cases hHead : Ty.combine Usage.add σ τ with
                    | none => simp [hHead] at h
                    | some ρ =>
                            cases hTail : Env.combine Usage.add Γ Δ with
                            | none => simp [hHead, hTail] at h
                            | some Ξ =>
                                    simp [hHead, hTail] at h
                                    cases h
                                    have hTy := Ty.combine_erase_of_some Usage.add hHead
                                    have hEnv := ih hTail
                                    simp only [erase]
                                    constructor
                                    · rw [hTy.1, hEnv.1]
                                    · rw [hTy.2, hEnv.2]

/-- Successful pointwise `⊓` preserves the erased simple context. -/
theorem cap_erase_of_some {Γ Δ Θ : Env} (h : Env.cap Γ Δ = some Θ) :
    erase Γ = erase Δ ∧ erase Θ = erase Γ := by
  induction Γ generalizing Δ Θ with
  | nil =>
      cases Δ with
      | nil =>
          cases Θ <;> simp [Env.cap, Env.combine, erase] at h ⊢
      | cons σ Δ => simp [Env.cap, Env.combine] at h
  | cons σ Γ ih =>
      cases Δ with
      | nil => simp [Env.cap, Env.combine] at h
      | cons τ Δ =>
          change
            (Ty.combine Usage.meet σ τ >>= fun ρ =>
              Env.combine Usage.meet Γ Δ >>= fun Ξ => some (ρ :: Ξ)) = some Θ at h
          cases hHead : Ty.combine Usage.meet σ τ with
          | none => simp [hHead] at h
          | some ρ =>
              cases hTail : Env.combine Usage.meet Γ Δ with
              | none => simp [hHead, hTail] at h
              | some Ξ =>
                  simp [hHead, hTail] at h
                  cases h
                  have hTy := Ty.combine_erase_of_some Usage.meet hHead
                  have hEnv := ih hTail
                  simp only [erase]
                  constructor
                  · rw [hTy.1, hEnv.1]
                  · rw [hTy.2, hEnv.2]

end Env

/-- Environment subtyping preserves the erased simple context. -/
theorem Env.subtype_erase :
    ∀ {Γ Δ : Env}, Env.Subtype Γ Δ → Env.erase Γ = Env.erase Δ
  | [], [], _ => rfl
  | σ :: Γ, τ :: Δ, h => by
      rcases h with ⟨hσ, hΓ⟩
      simp only [Env.erase]
      rw [Ty.subtype_erase hσ, Env.subtype_erase hΓ]
  | _ :: _, [], h => False.elim h
  | [], _ :: _, h => False.elim h

end Strictness
