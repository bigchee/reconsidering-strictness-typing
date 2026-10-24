import Std

/-- The four usage annotations of the type system. -/
inductive Usage where
  | unknown
  | strict
  | lazy
  | top
  deriving DecidableEq, Repr

namespace Usage

/-- The order `? ≤ S ≤ ⊤` and `? ≤ L ≤ ⊤`. -/
protected def Le : Usage → Usage → Prop
  | unknown, _ => True
  | strict, strict | strict, top => True
  | lazy, lazy | lazy, top => True
  | top, top => True
  | _, _ => False

instance : LE Usage := ⟨Usage.Le⟩

@[simp] theorem le_def {u v : Usage} :
    u ≤ v ↔ Usage.Le u v := Iff.rfl

theorem le_refl (u : Usage) : u ≤ u := by
  cases u <;> trivial

theorem le_trans {u v w : Usage} (huv : u ≤ v) (hvw : v ≤ w) : u ≤ w := by
  simp_all;
  cases u <;> cases v <;> cases w <;> simp_all only [Usage.Le]

theorem le_antisymm {u v : Usage} (huv : u ≤ v) (hvu : v ≤ u) : u = v := by
  simp_all;
  cases u <;> cases v <;> simp_all only [Usage.Le]

/-- The addition operation for combining demands. -/
def add : Usage → Usage → Usage
  | top, top => top
  | top, strict => strict
  | top, unknown => strict
  | top, lazy => top
  | strict, _ => strict
  | unknown, top => strict
  | unknown, strict => strict
  | unknown, unknown => unknown
  | unknown, lazy => unknown
  | lazy, top => top
  | lazy, strict => strict
  | lazy, unknown => unknown
  | lazy, lazy => lazy

/-- Meet in the four-element lattice. -/
def meet : Usage → Usage → Usage
  | top, v => v
  | strict, top => strict
  | strict, strict => strict
  | strict, unknown => unknown
  | strict, lazy => unknown
  | unknown, _ => unknown
  | lazy, top => lazy
  | lazy, strict => unknown
  | lazy, unknown => unknown
  | lazy, lazy => lazy

/-- Join in the four-element lattice. -/
def join : Usage → Usage → Usage
  | unknown, v => v
  | strict, unknown => strict
  | strict, strict => strict
  | strict, lazy => top
  | strict, top => top
  | lazy, unknown => lazy
  | lazy, strict => top
  | lazy, lazy => lazy
  | lazy, top => top
  | top, _ => top

infixl:65 " ⊔ " => Usage.join

theorem le_join_left (u v : Usage) : u ≤ u ⊔ v := by
  cases u <;> cases v <;> trivial

theorem le_join_right (u v : Usage) : v ≤ u ⊔ v := by
  cases u <;> cases v <;> trivial

theorem join_le {u v w : Usage} (hu : u ≤ w) (hv : v ≤ w) : u ⊔ v ≤ w := by
  cases u <;> cases v <;> cases w <;>
    simp [Usage.Le, Usage.join] at hu hv ⊢

theorem join_idem (u : Usage) : u ⊔ u = u := by
  cases u <;> rfl

/-- The non-commutative scalar product on usage annotations. -/
def scale : Usage → Usage → Usage
  | top, _ => top
  | strict, top => top
  | strict, strict => strict
  | strict, unknown => unknown
  | strict, lazy => lazy
  | unknown, top => lazy
  | unknown, strict => unknown
  | unknown, unknown => unknown
  | unknown, lazy => lazy
  | lazy, _ => lazy

@[simp] theorem strict_scale (u : Usage) : scale strict u = u := by
  cases u <;> rfl

@[simp] theorem scale_strict (u : Usage) : scale u strict = u := by
  cases u <;> rfl

theorem scale_assoc (u v w : Usage) : scale u (scale v w) = scale (scale u v) w := by
  cases u <;> cases v <;> cases w <;> rfl

theorem scale_monotone_left {u v w : Usage} (h : u ≤ v) : scale u w ≤ scale v w := by
  simp_all;
  cases u <;> cases v <;> cases w <;> simp_all only [Usage.Le, scale]

theorem scale_monotone_right {u v w : Usage} (h : v ≤ w) : scale u v ≤ scale u w := by
  simp_all;
  cases u <;> cases v <;> cases w <;> simp_all only [Usage.Le, scale]

theorem lazy_le_lazy_scale (u : Usage) : lazy ≤ scale lazy u := by
  cases u <;> trivial

theorem lazy_le_top_scale (u : Usage) : lazy ≤ scale top u := by
  cases u <;> trivial

theorem top_scale_not_le_lazy (u : Usage) : ¬ scale top u ≤ lazy := by
  cases u <;> exact fun h => h

theorem not_lazy_le_unknown : ¬ lazy ≤ unknown := by
  exact fun h => h

theorem not_lazy_le_strict : ¬ lazy ≤ strict := by
  exact fun h => h

theorem lazy_le_lazy : lazy ≤ lazy := by
  trivial

theorem lazy_le_top : lazy ≤ top := by
  trivial

theorem left_distrib_add (u v w : Usage) :
    scale u (add v w) = add (scale u v) (scale u w) := by
  cases u <;> cases v <;> cases w <;> rfl

theorem right_subdistrib_add (u v w : Usage) :
    scale (add u v) w ≤ add (scale u w) (scale v w) := by
  cases u <;> cases v <;> cases w <;> trivial

end Usage


namespace Usage

/-- If a sum is `top`, at least one summand is `top`. -/
theorem add_eq_top_implies_top_left_or_right {u v : Usage}
    (h : add u v = top) : u = top ∨ v = top := by
  cases u <;> cases v <;> simp [add] at h ⊢

/-- A sum is `lazy` only when both summands are `lazy`. -/
theorem add_eq_lazy_implies_both_lazy {u v : Usage}
    (h : add u v = lazy) : u = lazy ∧ v = lazy := by
  cases u <;> cases v <;> simp [add] at h ⊢

/-- If a sum is `strict`, at least one summand is `strict` or `top`. -/
theorem add_eq_strict_implies_strict_or_top {u v : Usage}
    (h : add u v = strict) :
    u = strict ∨ u = top ∨ v = strict ∨ v = top := by
  cases u <;> cases v <;> simp [add] at h ⊢

end Usage

namespace Usage

/-- Classification of the four-point order by the target `unknown`. -/
theorem le_unknown_iff {u : Usage} : u ≤ unknown ↔ u = unknown := by
  cases u <;> simp [Usage.Le]

/-- Classification of the four-point order by a strict target. -/
theorem le_strict_iff {u : Usage} : strict ≤ u ↔ u = strict ∨ u = top := by
  cases u <;> simp [Usage.Le]

/-- Classification of the four-point order by a lazy target. -/
theorem le_lazy_iff {u : Usage} : lazy ≤ u ↔ u = lazy ∨ u = top := by
  cases u <;> simp [Usage.Le]

/-- Classification of the four-point order by a top target. -/
theorem le_top_iff {u : Usage} : top ≤ u ↔ u = top := by
  cases u <;> simp [Usage.Le]

end Usage
