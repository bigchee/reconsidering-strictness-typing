import Strictness.Language.Usage

namespace Strictness

open Usage

/-- Annotated types.  An annotation occurs at every type constructor. -/
inductive Ty where
  | int : Usage → Ty
  | prod : Ty → Ty → Usage → Ty
  | arrow : Ty → Ty → Usage → Ty
  deriving DecidableEq, Repr

/-- The simple type obtained by erasing all usage annotations. -/
inductive SimpleTy where
  | int : SimpleTy
  | prod : SimpleTy → SimpleTy → SimpleTy
  | arrow : SimpleTy → SimpleTy → SimpleTy
  deriving DecidableEq, Repr

namespace Ty

def outer : Ty → Usage
  | int u | prod _ _ u | arrow _ _ u => u

def erase : Ty → SimpleTy
  | int _ => .int
  | prod σ τ _ => .prod σ.erase τ.erase
  | arrow σ τ _ => .arrow σ.erase τ.erase

/-- Replace only the outer usage annotation, preserving all inner annotations.
This represents the paper's outer reannotation notation `σ^u`. -/
def reannotate (u : Usage) : Ty → Ty
  | int _ => int u
  | prod σ τ _ => prod σ τ u
  | arrow σ τ _ => arrow σ τ u

@[simp] theorem outer_reannotate (u : Usage) (τ : Ty) :
    (τ.reannotate u).outer = u := by
  cases τ <;> rfl

@[simp] theorem erase_reannotate (u : Usage) (τ : Ty) :
    (τ.reannotate u).erase = τ.erase := by
  cases τ <;> rfl

/-- Join only the outer annotation with S; inner annotations are unchanged. -/
def raiseStrict (τ : Ty) : Ty :=
  τ.reannotate (Usage.join τ.outer Usage.strict)

@[simp] theorem outer_raiseStrict (τ : Ty) :
    (raiseStrict τ).outer = Usage.join τ.outer Usage.strict := by
  exact outer_reannotate (Usage.join τ.outer Usage.strict) τ

@[simp] theorem erase_raiseStrict (τ : Ty) :
    (raiseStrict τ).erase = τ.erase := by
  exact erase_reannotate (Usage.join τ.outer Usage.strict) τ

/-- Raising changes neither S nor top at the outer position. -/
theorem raiseStrict_eq_self_of_outer {τ : Ty}
    (hOuter : τ.outer = Usage.strict ∨ τ.outer = Usage.top) :
    raiseStrict τ = τ := by
  rcases hOuter with hOuter | hOuter
  · cases τ <;> simp_all [raiseStrict, outer, reannotate, Usage.join]
  · cases τ <;> simp_all [raiseStrict, outer, reannotate, Usage.join]

/-- scalar multiplication: it descends through products but not arrows. -/
def scale (u : Usage) : Ty → Ty
  | int v => int (u.scale v)
  | prod σ τ v => prod (scale u σ) (scale u τ) (u.scale v)
  | arrow σ τ v => arrow σ τ (u.scale v)

/--
Pointwise type composition.  Product components are composed
recursively; an arrow's argument and result types must agree exactly.
-/
def combine (op : Usage → Usage → Usage) : Ty → Ty → Option Ty
  | int u, int v => some (.int (op u v))
  | prod σ₁ τ₁ u, prod σ₂ τ₂ v => do
      let σ ← combine op σ₁ σ₂
      let τ ← combine op τ₁ τ₂
      pure (.prod σ τ (op u v))
  | arrow σ₁ τ₁ u, arrow σ₂ τ₂ v =>
      if _ : σ₁ = σ₂ then
        if _ : τ₁ = τ₂ then some (.arrow σ₁ τ₁ (op u v))
        else none
      else none
  | _, _ => none

def plus : Ty → Ty → Option Ty := combine Usage.add
def cap : Ty → Ty → Option Ty := combine Usage.meet

/-- The recursive `Lazy` predicate. -/
def IsLazy : Ty → Prop
  | int u => u ≤ lazy
  | prod σ τ u => u ≤ lazy ∧ IsLazy σ ∧ IsLazy τ
  | arrow _ _ u => u ≤ lazy

@[simp] theorem erase_scale (u : Usage) (τ : Ty) : (τ.scale u).erase = τ.erase := by
  induction τ generalizing u <;> simp [scale, erase, *]

@[simp] theorem strict_scale (τ : Ty) : τ.scale strict = τ := by
  induction τ <;> simp [scale, *]

@[simp] theorem outer_scale (u : Usage) (τ : Ty) : (τ.scale u).outer = u.scale τ.outer := by
  cases τ <;> rfl

theorem scale_assoc (u v : Usage) (τ : Ty) :
    (τ.scale v).scale u = τ.scale (u.scale v) := by
  induction τ generalizing u v with
  | int w => simp [scale, Usage.scale_assoc]
  | prod σ τ w ihσ ihτ =>
      simp [scale, ihσ, ihτ, Usage.scale_assoc]
  | arrow σ τ w => simp [scale, Usage.scale_assoc]

/-- Scaling by `?` makes every observable product component lazy. -/
theorem unknown_scale_lazy (τ : Ty) : IsLazy (τ.scale unknown) := by
  induction τ with
  | int u =>
      change Usage.Le (Usage.scale unknown u) lazy
      cases u <;> trivial
  | prod σ τ u ihσ ihτ =>
      refine ⟨?_, ihσ, ihτ⟩
      change Usage.Le (Usage.scale unknown u) lazy
      cases u <;> trivial
  | arrow σ τ u =>
      change Usage.Le (Usage.scale unknown u) lazy
      cases u <;> trivial

/-- Scaling by `L` makes every observable product component lazy. -/
theorem lazy_scale_lazy (τ : Ty) : IsLazy (τ.scale lazy) := by
  induction τ with
  | int u =>
      change Usage.Le (Usage.scale lazy u) lazy
      cases u <;> trivial
  | prod σ τ u ihσ ihτ =>
      refine ⟨?_, ihσ, ihτ⟩
      change Usage.Le (Usage.scale lazy u) lazy
      cases u <;> trivial
  | arrow σ τ u =>
      change Usage.Le (Usage.scale lazy u) lazy
      cases u <;> trivial

/-- Structural subtyping: products and codomains are covariant;
function domains are contravariant. -/
inductive Subtype : Ty → Ty → Prop where
  | int {u v} : u ≤ v → Subtype (.int u) (.int v)
  | prod {σ₁ τ₁ σ₂ τ₂ u v} :
      Subtype σ₁ σ₂ → Subtype τ₁ τ₂ → u ≤ v →
      Subtype (.prod σ₁ τ₁ u) (.prod σ₂ τ₂ v)
  | arrow {σ₁ τ₁ σ₂ τ₂ u v} :
      Subtype σ₂ σ₁ → Subtype τ₁ τ₂ → u ≤ v →
      Subtype (.arrow σ₁ τ₁ u) (.arrow σ₂ τ₂ v)

end Ty
end Strictness
