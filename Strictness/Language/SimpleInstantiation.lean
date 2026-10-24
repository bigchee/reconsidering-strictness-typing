import Strictness.Language.SimpleSubstitution

namespace Strictness
namespace Term

/-- Two shifts at the same cutoff add their amounts. -/
theorem shift_same_cutoff_comp (a b c : Nat) (e : Term) :
    shift a c (shift b c e) = shift (b + a) c e := by
  induction e generalizing c with
  | var i =>
      by_cases h : c ≤ i
      · have h' : c ≤ i + b := by omega
        simp [shift, h, h', Nat.add_assoc]
      · simp [shift, h]
  | int n => rfl
  | lam body ih => simp only [shift, ih]
  | fix body ih => simp only [shift, ih]
  | app e₁ e₂ ih₁ ih₂ => simp only [shift, ih₁, ih₂]
  | pair e₁ e₂ ih₁ ih₂ => simp only [shift, ih₁, ih₂]
  | proj p e ih => simp only [shift, ih]
  | op o e₁ e₂ ih₁ ih₂ => simp only [shift, ih₁, ih₂]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ => simp only [shift, ih₀, ih₁, ih₂]
  | letE e₁ e₂ ih₁ ih₂ => simp only [shift, ih₁, ih₂]
  | omega => rfl
  | err => rfl

/-- Prepending a context shifts lookup indices by its length. -/
theorem lookup_append_offset
    {Γ Δ : Ctx} {i : Nat} {τ : SimpleTy}
    (h : lookup Γ i = some τ) :
    lookup (Δ ++ Γ) (i + Δ.length) = some τ := by
  induction Δ with
  | nil => simpa only [List.nil_append, List.length_nil, Nat.add_zero] using h
  | cons σ Δ ih =>
      simp only [List.cons_append, List.length_cons, Nat.add_succ, lookup]
      exact ih

/-- Inserting a context after B preserves lookup, shifting only the
indices outside B. -/
theorem lookup_insert_shift
    {B Γ Δ : Ctx} {i : Nat} {τ : SimpleTy}
    (h : lookup (B ++ Γ) i = some τ) :
    lookup (B ++ Δ ++ Γ)
      (if B.length ≤ i then i + Δ.length else i) = some τ := by
  by_cases hi : B.length ≤ i
  · simp only [if_pos hi]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    have hΓ : lookup Γ j = some τ := lookup_append_right h
    have hΔ := lookup_append_offset (Δ := Δ) hΓ
    have hB := lookup_append_offset (Δ := B) hΔ
    simpa only [List.append_assoc, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hB
  · simp only [if_neg hi]
    have hLt : i < B.length := by omega
    have hB : lookup B i = some τ := lookup_append_bound h hLt
    have hOut : lookup (B ++ (Δ ++ Γ)) i = some τ := lookup_append_left hB
    simpa only [List.append_assoc] using hOut

/-- Inserting bindings after a prefix B preserves simple typing when
free indices outside B are shifted. No closedness assumption is needed. -/
theorem hasType_shift_insert
    {B Γ Δ : Ctx} {e : Term} {τ : SimpleTy}
    (h : HasType (B ++ Γ) e τ) :
    HasType (B ++ Δ ++ Γ) (shift Δ.length B.length e) τ := by
  induction e generalizing B Γ τ with
  | var i =>
      cases h with
      | var hLookup =>
          by_cases hi : B.length ≤ i
          · simp only [shift, if_pos hi]
            apply HasType.var
            simpa only [if_pos hi] using
              (lookup_insert_shift (Δ := Δ) hLookup)
          · simp only [shift, if_neg hi]
            apply HasType.var
            simpa only [if_neg hi] using
              (lookup_insert_shift (Δ := Δ) hLookup)
  | int n =>
      cases h
      exact HasType.int
  | lam body ih =>
      cases h with
      | lam hBody =>
          simp only [shift]
          simpa only [List.cons_append, List.length_cons] using
            HasType.lam (ih (B := _ :: B) (Γ := Γ) hBody)
  | fix body ih =>
      cases h with
      | fix hBody =>
          simp only [shift]
          simpa only [List.cons_append, List.length_cons] using
            HasType.fix (ih (B := τ :: B) (Γ := Γ) hBody)
  | app e₁ e₂ ih₁ ih₂ =>
      cases h with
      | app h₁ h₂ =>
          exact HasType.app (ih₁ h₁) (ih₂ h₂)
  | pair e₁ e₂ ih₁ ih₂ =>
      cases h with
      | pair h₁ h₂ =>
          exact HasType.pair (ih₁ h₁) (ih₂ h₂)
  | proj b e ih =>
      cases h with
      | projLeft hPair => exact HasType.projLeft (ih hPair)
      | projRight hPair => exact HasType.projRight (ih hPair)
  | op o e₁ e₂ ih₁ ih₂ =>
      cases h with
      | op o h₁ h₂ => exact HasType.op o (ih₁ h₁) (ih₂ h₂)
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
      cases h with
      | ite h₀ h₁ h₂ => exact HasType.ite (ih₀ h₀) (ih₁ h₁) (ih₂ h₂)
  | letE e₁ e₂ ih₁ ih₂ =>
      cases h with
      | letE h₁ h₂ =>
          simp only [shift]
          simpa only [List.cons_append, List.length_cons] using
            HasType.letE (ih₁ h₁) (ih₂ (B := _ :: B) (Γ := Γ) h₂)
  | omega => exact HasType.omega
  | err => exact HasType.err

/-- Prepending bindings shifts all free variables of a typed term. -/
theorem hasType_shift_prefix
    {Γ Δ : Ctx} {e : Term} {τ : SimpleTy}
    (h : HasType Γ e τ) :
    HasType (Δ ++ Γ) (shift Δ.length 0 e) τ := by
  simpa only [List.nil_append, List.length_nil] using
    hasType_shift_insert (B := []) (Δ := Δ) h

end Term

namespace Term

/-- Lookup at the boundary of B retrieves the newly inserted binding. -/
theorem lookup_middle
    {B Γ : Ctx} {σ : SimpleTy} :
    lookup (B ++ (σ :: Γ)) B.length = some σ := by
  induction B with
  | nil => rfl
  | cons τ B ih =>
      simp only [List.cons_append, List.length_cons, lookup]
      exact ih

/-- Removing one binding by substitution preserves simple typing.
The argument is typed in Γ and may contain free variables. -/
theorem hasType_subst_prefix
    {B Γ : Ctx} {σ τ : SimpleTy} {body arg : Term}
    (hBody : HasType (B ++ (σ :: Γ)) body τ)
    (hArg : HasType Γ arg σ) :
    HasType (B ++ Γ)
      (subst B.length (shift B.length 0 arg) body) τ := by
  induction body generalizing B τ with
  | var i =>
      cases hBody with
      | var hLookup =>
          by_cases hEq : i = B.length
          · subst i
            have hSlot :
                lookup (B ++ (σ :: Γ)) B.length = some σ :=
              lookup_middle
            have hστ : σ = τ :=
              Option.some.inj (hSlot.symm.trans hLookup)
            cases hστ
            simpa only [subst, if_pos rfl] using
              (hasType_shift_prefix (Δ := B) hArg)
          · by_cases hLt : i < B.length
            · have hNotGt : ¬ B.length < i := by omega
              have hBound : lookup B i = some τ :=
                lookup_append_bound hLookup hLt
              simp only [subst, hEq, if_false, hNotGt]
              exact HasType.var (lookup_append_left hBound)
            · have hGt : B.length < i := by omega
              have hLe : B.length ≤ i := by omega
              obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hLe
              cases j with
              | zero =>
                  simp at hEq
              | succ j =>
                    have hΓ : lookup Γ j = some τ := by
                        have hTail :=
                        lookup_append_right
                            (B := B) (Γ := σ :: Γ) (i := j + 1) hLookup
                        simpa only [lookup] using hTail
                    have hIndex :
                        B.length + (j + 1) - 1 = j + B.length := by
                        omega
                    simp only [subst, hEq, if_false, hGt, if_true]
                    apply HasType.var
                    rw [hIndex]
                    exact lookup_append_offset (Δ := B) hΓ
  | int n =>
      cases hBody
      exact HasType.int
  | lam body ih =>
      cases hBody with
      | lam hInner =>
          simp only [subst]
          simpa only [List.cons_append, List.length_cons,
            shift_same_cutoff_comp] using
              HasType.lam (ih (B := _ :: B) hInner)
  | fix body ih =>
      cases hBody with
      | fix hInner =>
          simp only [subst]
          simpa only [List.cons_append, List.length_cons,
            shift_same_cutoff_comp] using
              HasType.fix (ih (B := τ :: B) hInner)
  | app e₁ e₂ ih₁ ih₂ =>
      cases hBody with
      | app h₁ h₂ =>
          exact HasType.app (ih₁ h₁) (ih₂ h₂)
  | pair e₁ e₂ ih₁ ih₂ =>
      cases hBody with
      | pair h₁ h₂ =>
          exact HasType.pair (ih₁ h₁) (ih₂ h₂)
  | proj b e ih =>
      cases hBody with
      | projLeft hPair => exact HasType.projLeft (ih hPair)
      | projRight hPair => exact HasType.projRight (ih hPair)
  | op o e₁ e₂ ih₁ ih₂ =>
      cases hBody with
      | op o h₁ h₂ =>
          exact HasType.op o (ih₁ h₁) (ih₂ h₂)
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
      cases hBody with
      | ite h₀ h₁ h₂ =>
          exact HasType.ite (ih₀ h₀) (ih₁ h₁) (ih₂ h₂)
  | letE e₁ e₂ ih₁ ih₂ =>
      cases hBody with
      | letE h₁ h₂ =>
          simp only [subst]
          simpa only [List.cons_append, List.length_cons,
            shift_same_cutoff_comp] using
              HasType.letE (ih₁ h₁) (ih₂ (B := _ :: B) h₂)
  | omega => exact HasType.omega
  | err => exact HasType.err

end Term

/-- Beta/let instantiation preserves simple typing for open arguments. -/
theorem hasType_instantiate_open
    {Γ : Term.Ctx} {σ τ : SimpleTy} {body arg : Term}
    (hBody : Term.HasType (σ :: Γ) body τ)
    (hArg : Term.HasType Γ arg σ) :
    Term.HasType Γ (Term.instantiate body arg) τ := by
  simpa only [List.nil_append, List.length_nil,
    Term.shift_zero, Term.instantiate] using
      Term.hasType_subst_prefix (B := []) hBody hArg

namespace Term

/-- Insert a second block immediately above a block inserted by a shift.
The cutoff of the second shift includes the first inserted block. -/
theorem shift_insert_comp (a b c : Nat) (e : Term) :
    shift a (c + b) (shift b c e) = shift (b + a) c e := by
  induction e generalizing c with
  | var i =>
      by_cases h : c ≤ i
      · have h' : c + b ≤ i + b := by omega
        simp [shift, h, h', Nat.add_assoc]
      · have h' : ¬ c + b ≤ i := by omega
        simp [shift, h, h']
  | int n => rfl
  | lam body ih =>
      simp only [shift]
      rw [show c + b + 1 = (c + 1) + b by omega]
      rw [ih]
  | fix body ih =>
      simp only [shift]
      rw [show c + b + 1 = (c + 1) + b by omega]
      rw [ih]
  | app e₁ e₂ ih₁ ih₂ => simp only [shift, ih₁, ih₂]
  | pair e₁ e₂ ih₁ ih₂ => simp only [shift, ih₁, ih₂]
  | proj p e ih => simp only [shift, ih]
  | op o e₁ e₂ ih₁ ih₂ => simp only [shift, ih₁, ih₂]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ => simp only [shift, ih₀, ih₁, ih₂]
  | letE e₁ e₂ ih₁ ih₂ =>
      simp only [shift]
      rw [show c + b + 1 = (c + 1) + b by omega]
      rw [ih₁, ih₂]
  | omega => rfl
  | err => rfl

end Term

namespace Substitution

/-- Applying a substitution after inserting a block of bound variables is
the same as applying it first and then inserting that block.

The source term and the substitution images may be open. Generalizing
`depth` is essential for the lambda and let-body cases. -/
theorem applyAt_shift_insert (ρ : Substitution) (e : Term)
    (depth amount : Nat) :
    applyAt ρ (depth + amount) (Term.shift amount depth e) =
      Term.shift amount depth (applyAt ρ depth e) := by
  induction e generalizing depth with
  | var i =>
      by_cases h : i < depth
      · have hShift : ¬ depth ≤ i := by omega
        have hApply : i < depth + amount := by omega
        simp [Term.shift, applyAt, h, hShift, hApply]
      · have hShift : depth ≤ i := by omega
        have hApply : ¬ i + amount < depth + amount := by omega
        simp only [Term.shift, hShift, if_pos, applyAt, h, hApply, if_false]
        rw [show i + amount - (depth + amount) = i - depth by omega]
        simpa only [Nat.zero_add] using
          (Term.shift_insert_comp amount depth 0 (ρ (i - depth))).symm
  | int n => rfl
  | lam body ih =>
      simp only [Term.shift, applyAt]
      rw [show depth + amount + 1 = (depth + 1) + amount by omega]
      rw [ih]
  | fix body ih =>
      simp only [Term.shift, applyAt]
      rw [show depth + amount + 1 = (depth + 1) + amount by omega]
      rw [ih]
  | app e₁ e₂ ih₁ ih₂ => simp only [Term.shift, applyAt, ih₁, ih₂]
  | pair e₁ e₂ ih₁ ih₂ => simp only [Term.shift, applyAt, ih₁, ih₂]
  | proj p e ih => simp only [Term.shift, applyAt, ih]
  | op o e₁ e₂ ih₁ ih₂ => simp only [Term.shift, applyAt, ih₁, ih₂]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
      simp only [Term.shift, applyAt, ih₀, ih₁, ih₂]
  | letE e₁ e₂ ih₁ ih₂ =>
      simp only [Term.shift, applyAt]
      rw [show depth + amount + 1 = (depth + 1) + amount by omega]
      rw [ih₁, ih₂]
  | omega => rfl
  | err => rfl

/-- Top-level specialization used when commuting closing substitution with
beta/let substitution. No closedness assumption on `arg` is needed. -/
theorem applyAt_shift_zero (ρ : Substitution) (arg : Term) (d : Nat) :
    applyAt ρ d (Term.shift d 0 arg) =
      Term.shift d 0 (apply ρ arg) := by
  simpa only [Nat.zero_add, apply] using
    applyAt_shift_insert ρ arg 0 d

/-- Closing substitution commutes with removing one binder by substitution.
Only the images of `ρ` must be closed; `arg` and `body` may be open. -/
theorem applyAt_subst_shift_of_closed_images
    (ρ : Substitution) (arg : Term)
    (hρ : ∀ i, Term.Closed (ρ i)) (d : Nat) (body : Term) :
    applyAt ρ d (Term.subst d (Term.shift d 0 arg) body) =
      Term.subst d (Term.shift d 0 (apply ρ arg))
        (applyAt ρ (d + 1) body) := by
  induction body generalizing d with
  | var i =>
      by_cases hEq : i = d
      · subst i
        simpa [Term.subst, applyAt] using applyAt_shift_zero ρ arg d
      · by_cases hLt : i < d
        · have hNotGt : ¬ d < i := by omega
          have hLtSucc : i < d + 1 := by omega
          simp [Term.subst, applyAt, hEq, hLt, hNotGt, hLtSucc]
        · have hGt : d < i := by omega
          have hAfter : ¬ i - 1 < d := by omega
          have hFree : ¬ i < d + 1 := by omega
          simp only [Term.subst, hEq, if_false, hGt, if_true,
            applyAt, hAfter, hFree]
          rw [Term.shift_eq_of_closed (hρ (i - 1 - d)),
            Term.shift_eq_of_closed (hρ (i - (d + 1)))]
          rw [Term.subst_eq_of_closedAt (hρ (i - (d + 1))) (Nat.zero_le d)]
          rw [show i - 1 - d = i - (d + 1) by omega]
  | int n => rfl
  | lam body ih =>
      simp only [Term.subst, applyAt, Term.shift_same_cutoff_comp, ih]
  | fix body ih =>
      simp only [Term.subst, applyAt, Term.shift_same_cutoff_comp, ih]
  | app e₁ e₂ ih₁ ih₂ => simp only [Term.subst, applyAt, ih₁, ih₂]
  | pair e₁ e₂ ih₁ ih₂ => simp only [Term.subst, applyAt, ih₁, ih₂]
  | proj p e ih => simp only [Term.subst, applyAt, ih]
  | op o e₁ e₂ ih₁ ih₂ => simp only [Term.subst, applyAt, ih₁, ih₂]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
      simp only [Term.subst, applyAt, ih₀, ih₁, ih₂]
  | letE e₁ e₂ ih₁ ih₂ =>
      simp only [Term.subst, applyAt, Term.shift_same_cutoff_comp, ih₁, ih₂]
  | omega => rfl
  | err => rfl

/-- Top-level beta/let commutation, with no closedness assumption on the
original argument. -/
theorem apply_instantiate_of_closed_images
    (ρ : Substitution) (body arg : Term)
    (hρ : ∀ i, Term.Closed (ρ i)) :
    apply ρ (Term.instantiate body arg) =
      Term.instantiate (applyAt ρ 1 body) (apply ρ arg) := by
  simpa only [apply, Term.instantiate, Term.shift_zero, Nat.zero_add] using
    applyAt_subst_shift_of_closed_images ρ arg hρ 0 body

/- Small computational checks: open arguments and binders. These do not
replace compilation of the general theorems above. -/
example :
    applyAt (fun _ => Term.var 2) 1 (Term.shift 1 0 (.var 0)) = .var 3 := by
  rfl

example :
    applyAt (fun _ => Term.var 2) 1
        (Term.shift 1 0 (.lam (.app (.var 0) (.var 1)))) =
      .lam (.app (.var 0) (.var 4)) := by
  rfl

/- Beta substitution with an open argument; both bound and free variables
occur in the body. -/
example :
    apply (fun _ => Term.int 7)
        (Term.instantiate (.app (.var 0) (.var 1)) (.var 0)) =
      .app (.int 7) (.int 7) := by
  rfl

/- The bound variable is used underneath another lambda. -/
example :
    apply (fun _ => Term.int 7)
        (Term.instantiate (.lam (.app (.var 1) (.var 2))) (.var 0)) =
      .lam (.app (.int 7) (.int 7)) := by
  rfl

/- The same interaction underneath a let binder. -/
example :
    apply (fun _ => Term.int 7)
        (Term.instantiate
          (.letE (.var 0) (.app (.var 1) (.var 2))) (.var 0)) =
      .letE (.int 7) (.app (.int 7) (.int 7)) := by
  rfl

example :
    applyAt (fun _ => Term.var 2) 1
        (Term.shift 1 0 (.letE (.var 0) (.app (.var 0) (.var 1)))) =
      .letE (.var 3) (.app (.var 0) (.var 4)) := by
  rfl

end Substitution


end Strictness
