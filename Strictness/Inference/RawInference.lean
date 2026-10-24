import Strictness.Language.Environment

namespace Strictness

/-!
Symbolic usage expressions, annotated types, and usage constraints.

This module supplies the shared constraint algebra, evaluation lemmas, and
variance-aware structural subtype expansion. The syntax-directed generator
is in Strictness/Inference/CoreBoundary.lean; its correspondence with declarative typing is in
Strictness/Inference/Correspondence.lean.
-/

namespace Raw

open Usage

/-- Variables in raw annotation expressions. -/
abbrev Var := Nat

/-- A valuation of raw annotation variables. -/
abbrev Valuation := Var → Usage

/-- Raw usage expressions.  Every constructor denotes a monotone operation
on the fixed usage lattice. -/
inductive Expr where
  | var : Var → Expr
  | lit : Usage → Expr
  | add : Expr → Expr → Expr
  | meet : Expr → Expr → Expr
  | join : Expr → Expr → Expr
  | scale : Expr → Expr → Expr
  deriving DecidableEq, Repr

namespace Expr

def eval (ν : Valuation) : Expr → Usage
  | var a => ν a
  | lit u => u
  | add p q => Usage.add (eval ν p) (eval ν q)
  | meet p q => Usage.meet (eval ν p) (eval ν q)
  | join p q => Usage.join (eval ν p) (eval ν q)
  | scale p q => Usage.scale (eval ν p) (eval ν q)

def IsAtom : Expr → Prop
  | var _ | lit _ => True
  | _ => False

def ValuationLE (ν₁ ν₂ : Valuation) : Prop := ∀ a, ν₁ a ≤ ν₂ a

def ValuationJoin (ν₁ ν₂ : Valuation) : Valuation :=
  fun a => ν₁ a ⊔ ν₂ a

theorem le_valuationJoin_left (ν₁ ν₂ : Valuation) :
    ValuationLE ν₁ (ValuationJoin ν₁ ν₂) := fun a =>
  Usage.le_join_left (ν₁ a) (ν₂ a)

theorem le_valuationJoin_right (ν₁ ν₂ : Valuation) :
    ValuationLE ν₂ (ValuationJoin ν₁ ν₂) := fun a =>
  Usage.le_join_right (ν₁ a) (ν₂ a)

def Monotone (p : Expr) : Prop :=
  ∀ {ν₁ ν₂}, ValuationLE ν₁ ν₂ → eval ν₁ p ≤ eval ν₂ p

private theorem add_monotone {u₁ u₂ v₁ v₂ : Usage}
    (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂) :
    Usage.add u₁ v₁ ≤ Usage.add u₂ v₂ := by
  cases u₁ <;> cases u₂ <;> cases v₁ <;> cases v₂ <;>
    simp [Usage.Le, Usage.add] at hu hv ⊢

private theorem meet_monotone {u₁ u₂ v₁ v₂ : Usage}
    (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂) :
    Usage.meet u₁ v₁ ≤ Usage.meet u₂ v₂ := by
  cases u₁ <;> cases u₂ <;> cases v₁ <;> cases v₂ <;>
    simp [Usage.Le, Usage.meet] at hu hv ⊢

private theorem join_monotone {u₁ u₂ v₁ v₂ : Usage}
    (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂) :
    Usage.join u₁ v₁ ≤ Usage.join u₂ v₂ := by
  cases u₁ <;> cases u₂ <;> cases v₁ <;> cases v₂ <;>
    simp [Usage.Le, Usage.join] at hu hv ⊢

/-- Every expression in the grammar is monotone.  This is the lattice fact
used by the dual Algorithm-D normalization theorem. -/
theorem monotone (p : Expr) : Monotone p := by
  induction p with
  | var a =>
      intro ν₁ ν₂ hν
      exact hν a
  | lit u =>
      intro ν₁ ν₂ _
      exact Usage.le_refl u
  | add p q ihp ihq =>
      intro ν₁ ν₂ hν
      exact add_monotone (ihp hν) (ihq hν)
  | meet p q ihp ihq =>
      intro ν₁ ν₂ hν
      exact meet_monotone (ihp hν) (ihq hν)
  | join p q ihp ihq =>
      intro ν₁ ν₂ hν
      exact join_monotone (ihp hν) (ihq hν)
  | scale p q ihp ihq =>
      intro ν₁ ν₂ hν
      exact Usage.le_trans (Usage.scale_monotone_right (ihq hν))
        (Usage.scale_monotone_left (ihp hν))

theorem eval_atom_join (p : Expr) (hp : p.IsAtom)
    (ν₁ ν₂ : Valuation) :
    p.eval (ValuationJoin ν₁ ν₂) = p.eval ν₁ ⊔ p.eval ν₂ := by
  cases p with
  | var _ => rfl
  | lit u =>
      simp only [eval]
      exact (Usage.join_idem u).symm
  | add _ _ | meet _ _ | join _ _ | scale _ _ => simp [IsAtom] at hp

end Expr

/-- A usage inequality retained by the generator. -/
structure UseConstraint where
  lhs : Expr
  rhs : Expr
  deriving DecidableEq, Repr

namespace UseConstraint

def Holds (ν : Valuation) (c : UseConstraint) : Prop :=
  c.lhs.eval ν ≤ c.rhs.eval ν

def IsDualDefinite (c : UseConstraint) : Prop :=
  c.lhs.IsAtom ∧ c.rhs.Monotone

theorem holds_valuationJoin {ν₁ ν₂ : Valuation} {c : UseConstraint}
    (hDef : c.IsDualDefinite) (h₁ : c.Holds ν₁) (h₂ : c.Holds ν₂) :
    c.Holds (Expr.ValuationJoin ν₁ ν₂) := by
  rcases hDef with ⟨hAtom, hMono⟩
  change c.lhs.eval (Expr.ValuationJoin ν₁ ν₂) ≤
    c.rhs.eval (Expr.ValuationJoin ν₁ ν₂)
  rw [Expr.eval_atom_join c.lhs hAtom]
  apply Usage.join_le
  · exact Usage.le_trans h₁ (hMono (Expr.le_valuationJoin_left ν₁ ν₂))
  · exact Usage.le_trans h₂ (hMono (Expr.le_valuationJoin_right ν₁ ν₂))

end UseConstraint

abbrev UseConstraints := List UseConstraint

namespace UseConstraints

def Satisfies (ν : Valuation) (C : UseConstraints) : Prop :=
  ∀ c, c ∈ C → c.Holds ν

def DualDefinite (C : UseConstraints) : Prop :=
  ∀ c, c ∈ C → c.IsDualDefinite

theorem satisfies_nil (ν : Valuation) : Satisfies ν [] := by
  intro c hc
  simp at hc

theorem satisfies_append {ν : Valuation} {C D : UseConstraints} :
    Satisfies ν (C ++ D) ↔ Satisfies ν C ∧ Satisfies ν D := by
  constructor
  · intro h
    constructor
    · intro c hc
      exact h c (List.mem_append_left _ hc)
    · intro c hc
      exact h c (List.mem_append_right _ hc)
  · rintro ⟨hC, hD⟩ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hC c hc
    · exact hD c hc

theorem satisfies_singleton {ν : Valuation} {c : UseConstraint} :
    Satisfies ν [c] ↔ c.Holds ν := by
  constructor
  · intro h
    exact h c (by simp)
  · intro h d hd
    rcases List.mem_singleton.mp hd with rfl
    exact h

theorem dualDefinite_append {C D : UseConstraints} :
    DualDefinite (C ++ D) ↔ DualDefinite C ∧ DualDefinite D := by
  constructor
  · intro h
    constructor
    · intro c hc
      exact h c (List.mem_append_left _ hc)
    · intro c hc
      exact h c (List.mem_append_right _ hc)
  · rintro ⟨hC, hD⟩ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hC c hc
    · exact hD c hc

theorem dualDefinite_singleton {c : UseConstraint} :
    DualDefinite [c] ↔ c.IsDualDefinite := by
  constructor
  · intro h
    exact h c (by simp)
  · intro h d hd
    rcases List.mem_singleton.mp hd with rfl
    exact h

theorem satisfies_valuationJoin {ν₁ ν₂ : Valuation} {C : UseConstraints}
    (hDef : C.DualDefinite) (h₁ : C.Satisfies ν₁) (h₂ : C.Satisfies ν₂) :
    C.Satisfies (Expr.ValuationJoin ν₁ ν₂) := by
  intro c hc
  exact UseConstraint.holds_valuationJoin (hDef c hc) (h₁ c hc) (h₂ c hc)

end UseConstraints

/-- Raw types: ordinary type constructors, with expressions rather than
concrete usages at every annotation position. -/
inductive Ty where
  | int : Expr → Ty
  | prod : Ty → Ty → Expr → Ty
  | arrow : Ty → Ty → Expr → Ty
  deriving DecidableEq, Repr

namespace Ty

def outer : Ty → Expr
  | int u | prod _ _ u | arrow _ _ u => u

def erase : Ty → SimpleTy
  | int _ => .int
  | prod σ τ _ => .prod σ.erase τ.erase
  | arrow σ τ _ => .arrow σ.erase τ.erase

def eval (ν : Valuation) : Ty → Strictness.Ty
  | int u => .int (u.eval ν)
  | prod σ τ u => .prod (eval ν σ) (eval ν τ) (u.eval ν)
  | arrow σ τ u => .arrow (eval ν σ) (eval ν τ) (u.eval ν)

/-- Raise only the outer annotation, leaving all type interiors unchanged. -/
def raiseStrict : Ty → Ty
  | .int u => .int (.join u (.lit .strict))
  | .prod A B u => .prod A B (.join u (.lit .strict))
  | .arrow A B u => .arrow A B (.join u (.lit .strict))

@[simp] theorem eval_raiseStrict (ν : Valuation) (A : Ty) :
    A.raiseStrict.eval ν = Strictness.Ty.raiseStrict (A.eval ν) := by
  cases A <;> rfl

/-- Every annotation is already an atom.  This is the boundary invariant for
raw derivation premises.  In particular it makes both orientations of a
structural subtyping constraint compatible with the Algorithm-D shape. -/
def AllAtoms : Ty → Prop
  | int u => u.IsAtom
  | prod σ τ u => σ.AllAtoms ∧ τ.AllAtoms ∧ u.IsAtom
  | arrow σ τ u => σ.AllAtoms ∧ τ.AllAtoms ∧ u.IsAtom

/-- Embed a concrete type at an atom-annotated raw boundary. -/
def quote : Strictness.Ty → Ty
  | .int u => .int (.lit u)
  | .prod σ τ u => .prod (quote σ) (quote τ) (.lit u)
  | .arrow σ τ u => .arrow (quote σ) (quote τ) (.lit u)

@[simp] theorem eval_quote (ν : Valuation) (τ : Strictness.Ty) :
    (quote τ).eval ν = τ := by
  induction τ <;> simp [quote, eval, Expr.eval, *]

theorem allAtoms_quote (τ : Strictness.Ty) : (quote τ).AllAtoms := by
  induction τ with
  | int _ => trivial
  | prod σ τ _ ihσ ihτ => exact ⟨ihσ, ihτ, trivial⟩
  | arrow σ τ _ ihσ ihτ => exact ⟨ihσ, ihτ, trivial⟩

@[simp] theorem eval_outer (ν : Valuation) (τ : Ty) :
    τ.outer.eval ν = (τ.eval ν).outer := by
  cases τ <;> rfl

/-- Raw structural scaling.  It descends through products but stops at
function arguments and results, exactly as scaling does. -/
def scale (p : Expr) : Ty → Ty
  | int u => int (.scale p u)
  | prod σ τ u => prod (scale p σ) (scale p τ) (.scale p u)
  | arrow σ τ u => arrow σ τ (.scale p u)

/-- Raw partial composition.  Function interiors must agree syntactically;
the constraint generator records any required agreement as a shape
constraint before using this operation. -/
def combine (op : Expr → Expr → Expr) : Ty → Ty → Option Ty
  | int u, int v => some (.int (op u v))
  | prod σ₁ τ₁ u, prod σ₂ τ₂ v => do
      let σ ← combine op σ₁ σ₂
      let τ ← combine op τ₁ τ₂
      pure (.prod σ τ (op u v))
  | arrow σ₁ τ₁ u, arrow σ₂ τ₂ v =>
      if σ₁ = σ₂ then
        if τ₁ = τ₂ then some (.arrow σ₁ τ₁ (op u v))
        else none
      else none
  | _, _ => none

def plus : Ty → Ty → Option Ty := combine Expr.add
def cap : Ty → Ty → Option Ty := combine Expr.meet

def lazyConstraints : Ty → UseConstraints
  | int u => [⟨u, .lit lazy⟩]
  | prod σ τ u => [⟨u, .lit lazy⟩] ++ lazyConstraints σ ++ lazyConstraints τ
  | arrow _ _ u => [⟨u, .lit lazy⟩]

/-- Variance-aware structural subtyping constraints, whose satisfaction
is equivalent to concrete type subtyping after valuation. -/
def subtypeConstraintsFuel : Nat → Ty → Ty → Option UseConstraints
  | 0, _, _ => none
  | _ + 1, int u, int v => some [⟨u, v⟩]
  | n + 1, prod σ₁ τ₁ u, prod σ₂ τ₂ v => do
      let Cσ ← subtypeConstraintsFuel n σ₁ σ₂
      let Cτ ← subtypeConstraintsFuel n τ₁ τ₂
      pure (Cσ ++ Cτ ++ [⟨u, v⟩])
  | n + 1, arrow σ₁ τ₁ u, arrow σ₂ τ₂ v => do
      let Cσ ← subtypeConstraintsFuel n σ₂ σ₁
      let Cτ ← subtypeConstraintsFuel n τ₁ τ₂
      pure (Cσ ++ Cτ ++ [⟨u, v⟩])
  | _ + 1, _, _ => none

noncomputable def subtypeConstraints (σ τ : Ty) : Option UseConstraints :=
  subtypeConstraintsFuel (sizeOf σ + sizeOf τ + 1) σ τ

theorem eval_scale (ν : Valuation) (p : Expr) (τ : Ty) :
    (scale p τ).eval ν = Strictness.Ty.scale (p.eval ν) (τ.eval ν) := by
  induction τ with
  | int u => rfl
  | prod σ τ u ihσ ihτ =>
      simp [scale, eval, Strictness.Ty.scale, ihσ, ihτ]
      rfl
  | arrow σ τ u => rfl

theorem eval_lazyConstraints (ν : Valuation) (τ : Ty) :
    UseConstraints.Satisfies ν τ.lazyConstraints ↔
      Strictness.Ty.IsLazy (τ.eval ν) := by
  induction τ with
  | int u =>
      rw [lazyConstraints, UseConstraints.satisfies_singleton]
      rfl
  | prod σ τ u ihσ ihτ =>
      rw [lazyConstraints, UseConstraints.satisfies_append,
        UseConstraints.satisfies_append, UseConstraints.satisfies_singleton,
        ihσ, ihτ]
      constructor
      · rintro ⟨⟨hu, hσ⟩, hτ⟩
        exact ⟨hu, hσ, hτ⟩
      · rintro ⟨hu, hσ, hτ⟩
        exact ⟨⟨hu, hσ⟩, hτ⟩
  | arrow σ τ u =>
      rw [lazyConstraints, UseConstraints.satisfies_singleton]
      rfl

private theorem eval_subtypeConstraintsFuel {ν : Valuation}
    {n : Nat} {σ τ : Ty} {C : UseConstraints}
    (hC : subtypeConstraintsFuel n σ τ = some C) :
    UseConstraints.Satisfies ν C ↔
      Strictness.Ty.Subtype (σ.eval ν) (τ.eval ν) := by
  induction n generalizing σ τ C with
  | zero =>
      simp [subtypeConstraintsFuel] at hC
  | succ n ih =>
      cases σ with
      | int u =>
          cases τ with
          | int v =>
              simp [subtypeConstraintsFuel] at hC
              subst C
              rw [UseConstraints.satisfies_singleton]
              constructor
              · exact Strictness.Ty.Subtype.int
              · intro h
                cases h with
                | int h => exact h
          | prod τ₁ τ₂ v => simp [subtypeConstraintsFuel] at hC
          | arrow τ₁ τ₂ v => simp [subtypeConstraintsFuel] at hC
      | prod σ₁ σ₂ u =>
          cases τ with
          | int v => simp [subtypeConstraintsFuel] at hC
          | prod τ₁ τ₂ v =>
              cases hσ : subtypeConstraintsFuel n σ₁ τ₁ with
              | none => simp [subtypeConstraintsFuel, hσ] at hC
              | some Cσ =>
                  cases hτ : subtypeConstraintsFuel n σ₂ τ₂ with
                  | none => simp [subtypeConstraintsFuel, hσ, hτ] at hC
                  | some Cτ =>
                      simp [subtypeConstraintsFuel, hσ, hτ] at hC
                      subst C
                      rw [UseConstraints.satisfies_append,
                        UseConstraints.satisfies_append,
                        UseConstraints.satisfies_singleton,
                        ih hσ, ih hτ]
                      change
                        (Strictness.Ty.Subtype (σ₁.eval ν) (τ₁.eval ν) ∧
                          Strictness.Ty.Subtype (σ₂.eval ν) (τ₂.eval ν) ∧
                          u.eval ν ≤ v.eval ν) ↔
                        Strictness.Ty.Subtype
                          (.prod (σ₁.eval ν) (σ₂.eval ν) (u.eval ν))
                          (.prod (τ₁.eval ν) (τ₂.eval ν) (v.eval ν))
                      constructor
                      · rintro ⟨hσ, hτ, hu⟩
                        exact .prod hσ hτ hu
                      · intro h
                        cases h with
                        | prod hσ hτ hu => exact ⟨hσ, hτ, hu⟩
          | arrow τ₁ τ₂ v => simp [subtypeConstraintsFuel] at hC
      | arrow σ₁ σ₂ u =>
          cases τ with
          | int v => simp [subtypeConstraintsFuel] at hC
          | prod τ₁ τ₂ v => simp [subtypeConstraintsFuel] at hC
          | arrow τ₁ τ₂ v =>
              cases hσ : subtypeConstraintsFuel n τ₁ σ₁ with
              | none => simp [subtypeConstraintsFuel, hσ] at hC
              | some Cσ =>
                  cases hτ : subtypeConstraintsFuel n σ₂ τ₂ with
                  | none => simp [subtypeConstraintsFuel, hσ, hτ] at hC
                  | some Cτ =>
                      simp [subtypeConstraintsFuel, hσ, hτ] at hC
                      subst C
                      rw [UseConstraints.satisfies_append,
                        UseConstraints.satisfies_append,
                        UseConstraints.satisfies_singleton,
                        ih hσ, ih hτ]
                      change
                        (Strictness.Ty.Subtype (τ₁.eval ν) (σ₁.eval ν) ∧
                          Strictness.Ty.Subtype (σ₂.eval ν) (τ₂.eval ν) ∧
                          u.eval ν ≤ v.eval ν) ↔
                        Strictness.Ty.Subtype
                          (.arrow (σ₁.eval ν) (σ₂.eval ν) (u.eval ν))
                          (.arrow (τ₁.eval ν) (τ₂.eval ν) (v.eval ν))
                      constructor
                      · rintro ⟨hσ, hτ, hu⟩
                        exact .arrow hσ hτ hu
                      · intro h
                        cases h with
                        | arrow hσ hτ hu => exact ⟨hσ, hτ, hu⟩

theorem eval_subtypeConstraints {ν : Valuation} {σ τ : Ty}
    {C : UseConstraints} (hC : subtypeConstraints σ τ = some C) :
    UseConstraints.Satisfies ν C ↔
      Strictness.Ty.Subtype (σ.eval ν) (τ.eval ν) := by
  exact eval_subtypeConstraintsFuel hC

private theorem subtypeConstraintsFuel_dualDefinite
    {n : Nat} {σ τ : Ty} {C : UseConstraints}
    (hσ : σ.AllAtoms) (hτ : τ.AllAtoms)
    (hC : subtypeConstraintsFuel n σ τ = some C) :
    C.DualDefinite := by
  induction n generalizing σ τ C with
  | zero => simp [subtypeConstraintsFuel] at hC
  | succ n ih =>
      cases σ with
      | int u =>
          cases τ with
          | int v =>
              simp [subtypeConstraintsFuel] at hC
              subst C
              rw [UseConstraints.dualDefinite_singleton]
              exact ⟨hσ, Expr.monotone _⟩
          | prod _ _ _ => simp [subtypeConstraintsFuel] at hC
          | arrow _ _ _ => simp [subtypeConstraintsFuel] at hC
      | prod σ₁ σ₂ u =>
          cases τ with
          | int _ => simp [subtypeConstraintsFuel] at hC
          | prod τ₁ τ₂ v =>
              cases hσ' : subtypeConstraintsFuel n σ₁ τ₁ with
              | none => simp [subtypeConstraintsFuel, hσ'] at hC
              | some Cσ =>
                  cases hτ' : subtypeConstraintsFuel n σ₂ τ₂ with
                  | none => simp [subtypeConstraintsFuel, hσ', hτ'] at hC
                  | some Cτ =>
                      simp [subtypeConstraintsFuel, hσ', hτ'] at hC
                      subst C
                      rw [UseConstraints.dualDefinite_append,
                        UseConstraints.dualDefinite_append,
                        UseConstraints.dualDefinite_singleton]
                      exact ⟨ih hσ.1 hτ.1 hσ', ih hσ.2.1 hτ.2.1 hτ',
                        ⟨hσ.2.2, Expr.monotone _⟩⟩
          | arrow _ _ _ => simp [subtypeConstraintsFuel] at hC
      | arrow σ₁ σ₂ u =>
          cases τ with
          | int _ => simp [subtypeConstraintsFuel] at hC
          | prod _ _ _ => simp [subtypeConstraintsFuel] at hC
          | arrow τ₁ τ₂ v =>
              cases hσ' : subtypeConstraintsFuel n τ₁ σ₁ with
              | none => simp [subtypeConstraintsFuel, hσ'] at hC
              | some Cσ =>
                  cases hτ' : subtypeConstraintsFuel n σ₂ τ₂ with
                  | none => simp [subtypeConstraintsFuel, hσ', hτ'] at hC
                  | some Cτ =>
                      simp [subtypeConstraintsFuel, hσ', hτ'] at hC
                      subst C
                      rw [UseConstraints.dualDefinite_append,
                        UseConstraints.dualDefinite_append,
                        UseConstraints.dualDefinite_singleton]
                      exact ⟨ih hτ.1 hσ.1 hσ', ih hσ.2.1 hτ.2.1 hτ',
                        ⟨hσ.2.2, Expr.monotone _⟩⟩

/-- Structural subtyping produces dual-definite usage constraints when both
types have been passed through an atomising boundary.  The two-sided
precondition is essential because arrow domains reverse variance. -/
theorem subtypeConstraints_dualDefinite {σ τ : Ty} {C : UseConstraints}
    (hσ : σ.AllAtoms) (hτ : τ.AllAtoms)
    (hC : subtypeConstraints σ τ = some C) :
    C.DualDefinite := by
  exact subtypeConstraintsFuel_dualDefinite hσ hτ hC

private theorem eval_combine
    {ν : Valuation} (op : Expr → Expr → Expr) (op' : Usage → Usage → Usage)
    (hOp : ∀ p q, (op p q).eval ν = op' (p.eval ν) (q.eval ν))
    {σ τ θ : Ty} (h : combine op σ τ = some θ) :
    Strictness.Ty.combine op' (σ.eval ν) (τ.eval ν) = some (θ.eval ν) := by
  induction σ generalizing τ θ with
  | int u =>
      cases τ with
      | int v =>
          simp [combine] at h
          subst θ
          simp [Strictness.Ty.combine, eval, hOp]
      | prod τ₁ τ₂ v => simp [combine] at h
      | arrow τ₁ τ₂ v => simp [combine] at h
  | prod σ₁ σ₂ u ih₁ ih₂ =>
      cases τ with
      | int v => simp [combine] at h
      | prod τ₁ τ₂ v =>
          cases h₁ : combine op σ₁ τ₁ with
          | none => simp [combine, h₁] at h
          | some θ₁ =>
              cases h₂ : combine op σ₂ τ₂ with
              | none => simp [combine, h₁, h₂] at h
              | some θ₂ =>
                  simp [combine, h₁, h₂] at h
                  subst θ
                  simp [Strictness.Ty.combine, eval, ih₁ h₁, ih₂ h₂, hOp]
      | arrow τ₁ τ₂ v => simp [combine] at h
  | arrow σ₁ σ₂ u =>
      cases τ with
      | int v => simp [combine] at h
      | prod τ₁ τ₂ v => simp [combine] at h
      | arrow τ₁ τ₂ v =>
          by_cases h₁ : σ₁ = τ₁
          · subst τ₁
            by_cases h₂ : σ₂ = τ₂
            · subst τ₂
              simp [combine] at h
              subst θ
              simp [Strictness.Ty.combine, eval, hOp]
            · simp [combine, h₂] at h
          · simp [combine, h₁] at h

theorem eval_plus {ν : Valuation} {σ τ θ : Ty}
    (h : plus σ τ = some θ) :
    Strictness.Ty.plus (σ.eval ν) (τ.eval ν) = some (θ.eval ν) := by
  exact eval_combine Expr.add Usage.add (fun _ _ => rfl) h

theorem eval_cap {ν : Valuation} {σ τ θ : Ty}
    (h : cap σ τ = some θ) :
    Strictness.Ty.cap (σ.eval ν) (τ.eval ν) = some (θ.eval ν) := by
  exact eval_combine Expr.meet Usage.meet (fun _ _ => rfl) h

end Ty

abbrev Env := List Ty

namespace Env

def eval (ν : Valuation) : Env → Strictness.Env
  | [] => []
  | τ :: Γ => τ.eval ν :: eval ν Γ

/-- Embed a concrete environment at an atom-annotated raw boundary. -/
def quote : Strictness.Env → Env
  | [] => []
  | τ :: Γ => Ty.quote τ :: quote Γ

@[simp] theorem eval_quote (ν : Valuation) (Γ : Strictness.Env) :
    eval ν (quote Γ) = Γ := by
  induction Γ with
  | nil => rfl
  | cons τ Γ ih => simp [quote, eval, ih]

def scale (p : Expr) : Env → Env
  | [] => []
  | τ :: Γ => Ty.scale p τ :: scale p Γ

def combine (op : Expr → Expr → Expr) : Env → Env → Option Env
  | [], [] => some []
  | τ :: Γ, σ :: Δ => do
      let θ ← Ty.combine op τ σ
      let Ξ ← combine op Γ Δ
      pure (θ :: Ξ)
  | _, _ => none

def plus : Env → Env → Option Env := combine Expr.add
def cap : Env → Env → Option Env := combine Expr.meet

/-- Constraint expansion of pointwise declarative environment subtyping.
Unlike raw context composition, this relation is variance aware inside every
entry because it delegates to `Ty.subtypeConstraints`. -/
noncomputable def subtypeConstraints : Env → Env → Option UseConstraints
  | [], [] => some []
  | τ :: Γ, σ :: Δ => do
      let Cτ ← Ty.subtypeConstraints τ σ
      let CΓ ← subtypeConstraints Γ Δ
      pure (Cτ ++ CΓ)
  | _, _ => none

def AllAtoms (Γ : Env) : Prop := ∀ τ, τ ∈ Γ → τ.AllAtoms

theorem allAtoms_quote (Γ : Strictness.Env) : (quote Γ).AllAtoms := by
  intro τ hτ
  induction Γ with
  | nil => simp [quote] at hτ
  | cons σ Γ ih =>
      simp only [quote, List.mem_cons] at hτ
      rcases hτ with rfl | hτ
      · exact Ty.allAtoms_quote σ
      · exact ih hτ

def lazyConstraints : Env → UseConstraints
  | [] => []
  | τ :: Γ => τ.lazyConstraints ++ lazyConstraints Γ

theorem eval_scale (ν : Valuation) (p : Expr) (Γ : Env) :
    (scale p Γ).eval ν = Strictness.Env.scale (p.eval ν) (Γ.eval ν) := by
  induction Γ with
  | nil => rfl
  | cons τ Γ ih =>
      simp [scale, eval, Ty.eval_scale, ih]

theorem eval_lazyConstraints (ν : Valuation) (Γ : Env) :
    UseConstraints.Satisfies ν Γ.lazyConstraints ↔
      Strictness.Env.IsLazy (Γ.eval ν) := by
  induction Γ with
  | nil =>
      constructor
      · intro _
        trivial
      · intro _
        exact UseConstraints.satisfies_nil ν
  | cons τ Γ ih =>
      rw [lazyConstraints, UseConstraints.satisfies_append,
        Ty.eval_lazyConstraints, ih]
      rfl

theorem eval_plus {ν : Valuation} {Γ Δ Θ : Env}
    (h : plus Γ Δ = some Θ) :
    Strictness.Env.plus (Γ.eval ν) (Δ.eval ν) = some (Θ.eval ν) := by
  change combine Expr.add Γ Δ = some Θ at h
  induction Γ generalizing Δ Θ with
  | nil =>
      cases Δ
      · simp [combine] at h
        subst Θ
        rfl
      · simp [combine] at h
  | cons τ Γ ih =>
      cases Δ with
      | nil => simp [combine] at h
      | cons σ Δ =>
          cases hτ : Ty.combine Expr.add τ σ with
          | none => simp [combine, hτ] at h
          | some θ =>
              cases hΓ : combine Expr.add Γ Δ with
              | none => simp [combine, hτ, hΓ] at h
              | some Ξ =>
                  simp [combine, hτ, hΓ] at h
                  subst Θ
                  change
                    (Strictness.Ty.combine Usage.add (τ.eval ν) (σ.eval ν)).bind
                      (fun θ' =>
                        (Strictness.Env.combine Usage.add (eval ν Γ) (eval ν Δ)).bind
                          (fun Ξ' => some (θ' :: Ξ'))) =
                      some (θ.eval ν :: Ξ.eval ν)
                  have hEvalTy :
                      Strictness.Ty.combine Usage.add (τ.eval ν) (σ.eval ν) =
                        some (θ.eval ν) := by
                    simpa [Strictness.Ty.plus] using Ty.eval_plus hτ
                  rw [hEvalTy]
                  have hEvalΓ :
                      Strictness.Env.combine Usage.add (eval ν Γ) (eval ν Δ) =
                        some (eval ν Ξ) := by
                    simpa [Strictness.Env.plus] using ih hΓ
                  rw [hEvalΓ]
                  rfl

theorem eval_cap {ν : Valuation} {Γ Δ Θ : Env}
    (h : cap Γ Δ = some Θ) :
    Strictness.Env.cap (Γ.eval ν) (Δ.eval ν) = some (Θ.eval ν) := by
  change combine Expr.meet Γ Δ = some Θ at h
  induction Γ generalizing Δ Θ with
  | nil =>
      cases Δ
      · simp [combine] at h
        subst Θ
        rfl
      · simp [combine] at h
  | cons τ Γ ih =>
      cases Δ with
      | nil => simp [combine] at h
      | cons σ Δ =>
          cases hτ : Ty.combine Expr.meet τ σ with
          | none => simp [combine, hτ] at h
          | some θ =>
              cases hΓ : combine Expr.meet Γ Δ with
              | none => simp [combine, hτ, hΓ] at h
              | some Ξ =>
                  simp [combine, hτ, hΓ] at h
                  subst Θ
                  change
                    (Strictness.Ty.combine Usage.meet (τ.eval ν) (σ.eval ν)).bind
                      (fun θ' =>
                        (Strictness.Env.combine Usage.meet (eval ν Γ) (eval ν Δ)).bind
                          (fun Ξ' => some (θ' :: Ξ'))) =
                      some (θ.eval ν :: Ξ.eval ν)
                  have hEvalTy :
                      Strictness.Ty.combine Usage.meet (τ.eval ν) (σ.eval ν) =
                        some (θ.eval ν) := by
                    simpa [Strictness.Ty.cap] using Ty.eval_cap hτ
                  rw [hEvalTy]
                  have hEvalΓ :
                      Strictness.Env.combine Usage.meet (eval ν Γ) (eval ν Δ) =
                        some (eval ν Ξ) := by
                    simpa [Strictness.Env.cap] using ih hΓ
                  rw [hEvalΓ]
                  rfl

theorem eval_subtypeConstraints {ν : Valuation} {Γ Δ : Env}
    {C : UseConstraints} (hC : subtypeConstraints Γ Δ = some C) :
    UseConstraints.Satisfies ν C ↔
      Strictness.Env.Subtype (Γ.eval ν) (Δ.eval ν) := by
  induction Γ generalizing Δ C with
  | nil =>
      cases Δ with
      | nil =>
          simp [subtypeConstraints] at hC
          subst C
          constructor
          · intro _
            trivial
          · intro _
            exact UseConstraints.satisfies_nil ν
      | cons _ _ => simp [subtypeConstraints] at hC
  | cons τ Γ ih =>
      cases Δ with
      | nil => simp [subtypeConstraints] at hC
      | cons σ Δ =>
          cases hτ : Ty.subtypeConstraints τ σ with
          | none => simp [subtypeConstraints, hτ] at hC
          | some Cτ =>
              cases hΓ : subtypeConstraints Γ Δ with
              | none => simp [subtypeConstraints, hτ, hΓ] at hC
              | some CΓ =>
                  simp [subtypeConstraints, hτ, hΓ] at hC
                  subst C
                  rw [UseConstraints.satisfies_append,
                    Ty.eval_subtypeConstraints hτ, ih hΓ]
                  rfl

theorem subtypeConstraints_dualDefinite {Γ Δ : Env} {C : UseConstraints}
    (hΓ : Γ.AllAtoms) (hΔ : Δ.AllAtoms)
    (hC : subtypeConstraints Γ Δ = some C) :
    C.DualDefinite := by
  induction Γ generalizing Δ C with
  | nil =>
      cases Δ with
      | nil =>
          simp [subtypeConstraints] at hC
          subst C
          intro c hc
          simp at hc
      | cons _ _ => simp [subtypeConstraints] at hC
  | cons τ Γ ih =>
      cases Δ with
      | nil => simp [subtypeConstraints] at hC
      | cons σ Δ =>
          cases hτ : Ty.subtypeConstraints τ σ with
          | none => simp [subtypeConstraints, hτ] at hC
          | some Cτ =>
              cases hΓ' : subtypeConstraints Γ Δ with
              | none => simp [subtypeConstraints, hτ, hΓ'] at hC
              | some CΓ =>
                  simp [subtypeConstraints, hτ, hΓ'] at hC
                  subst C
                  rw [UseConstraints.dualDefinite_append]
                  constructor
                  · exact Ty.subtypeConstraints_dualDefinite
                      (hΓ τ (by simp)) (hΔ σ (by simp)) hτ
                  · apply ih
                    · intro θ hθ
                      exact hΓ θ (List.mem_cons_of_mem _ hθ)
                    · intro θ hθ
                      exact hΔ θ (List.mem_cons_of_mem _ hθ)
                    · exact hΓ'

end Env

end Raw

end Strictness
