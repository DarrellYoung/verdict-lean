/-
  Verdict.lean — machine-checked core of the third-verdict algebra.

  Companion to: D. L. Young and M. A. Thornton, "The Indeterminate Verdict"
  (JAL, submitted 2026) and "An Anisotropic-Authority Characterization of
  Pessimistic Verdict Aggregation over a Belnap-Ordered Eight-Valued Policy
  Chain" (ISMVL 2027, submitted).

  Checked with Lean 4.12.0, core library only. No Mathlib, no axioms beyond
  Lean's three standard ones. `#print axioms` at the bottom confirms it.

  Contents
    1. V3, the three-valued verdict set, with blocking precedence
       Valid < Invalid < Insufficient.
    2. Proposition 1 (JAL): the two total collapses to {Valid, Invalid} are
       non-injective and disagree at Insufficient; no property of the
       evidence selects between them.
    3. Pessimistic aggregation Agg = max_e (w_e ⊓ x_e) over a finite list of
       evaluators: recovery, monotonicity, idempotence iff some weight is ⊤.
    4. Descent theorem: for any relabelling ρ, ρ ∘ Agg is idempotent on
       constant profiles iff ρ = id. Hence no post-hoc lowering of a
       reported verdict is an adjudication under any authority row.
-/

namespace Verdict

/-! ### 1. The verdict set and its blocking order -/

inductive V3 where
  | valid
  | invalid
  | insuf
  deriving DecidableEq, Repr

open V3

/-- Blocking precedence: a verdict dominates to the extent that it licenses
less confident reliance. Valid < Invalid < Insufficient. -/
def blk : V3 → Nat
  | valid   => 0
  | invalid => 1
  | insuf   => 2

instance : LE V3 := ⟨fun a b => blk a ≤ blk b⟩
instance : LT V3 := ⟨fun a b => blk a < blk b⟩

instance (a b : V3) : Decidable (a ≤ b) := inferInstanceAs (Decidable (blk a ≤ blk b))
instance (a b : V3) : Decidable (a < b) := inferInstanceAs (Decidable (blk a < blk b))

theorem valid_lt_invalid : valid < invalid := by decide
theorem invalid_lt_insuf : invalid < insuf := by decide

/-- Join and meet in the blocking order. -/
def vmax (a b : V3) : V3 := if blk a ≤ blk b then b else a
def vmin (a b : V3) : V3 := if blk a ≤ blk b then a else b

theorem le_refl (a : V3) : a ≤ a := by cases a <;> decide
theorem le_trans {a b c : V3} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all (config := {decide := true}) [LE.le, blk]
theorem le_antisymm {a b : V3} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  cases a <;> cases b <;> simp_all (config := {decide := true}) [LE.le, blk]
theorem le_total (a b : V3) : a ≤ b ∨ b ≤ a := by cases a <;> cases b <;> decide

theorem vmax_comm (a b : V3) : vmax a b = vmax b a := by cases a <;> cases b <;> decide
theorem vmin_comm (a b : V3) : vmin a b = vmin b a := by cases a <;> cases b <;> decide
theorem le_vmax_left (a b : V3) : a ≤ vmax a b := by cases a <;> cases b <;> decide
theorem le_vmax_right (a b : V3) : b ≤ vmax a b := by cases a <;> cases b <;> decide
theorem vmax_le {a b c : V3} (h₁ : a ≤ c) (h₂ : b ≤ c) : vmax a b ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all (config := {decide := true}) [vmax, LE.le, blk]
theorem vmin_le_left (a b : V3) : vmin a b ≤ a := by cases a <;> cases b <;> decide
theorem vmin_le_right (a b : V3) : vmin a b ≤ b := by cases a <;> cases b <;> decide
theorem vmin_mono_right {a b c : V3} (h : b ≤ c) : vmin a b ≤ vmin a c := by
  cases a <;> cases b <;> cases c <;> simp_all (config := {decide := true}) [vmin, LE.le, blk]
theorem vmax_mono {a b c d : V3} (h₁ : a ≤ c) (h₂ : b ≤ d) : vmax a b ≤ vmax c d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all (config := {decide := true}) [vmax, LE.le, blk]
theorem vmin_insuf (a : V3) : vmin a insuf = a := by cases a <;> decide
theorem vmin_insuf_left (a : V3) : vmin insuf a = a := by cases a <;> decide
theorem vmax_valid (a : V3) : vmax a valid = a := by cases a <;> decide
theorem vmax_valid_left (a : V3) : vmax valid a = a := by cases a <;> decide
theorem vmax_self (a : V3) : vmax a a = a := by cases a <;> decide
theorem vmin_self (a : V3) : vmin a a = a := by cases a <;> decide
theorem vmin_valid (a : V3) : vmin a valid = valid := by cases a <;> decide
theorem valid_le (a : V3) : valid ≤ a := by cases a <;> decide

/-! ### 2. Proposition 1: the two-valued collapse is lossy and unforced -/

/-- The permissive collapse: Insufficient ↦ Valid. -/
def γp : V3 → V3
  | insuf => valid
  | v     => v

/-- The conservative collapse: Insufficient ↦ Invalid. -/
def γc : V3 → V3
  | insuf => invalid
  | v     => v

theorem γp_two_valued (v : V3) : γp v ≠ insuf := by cases v <;> decide
theorem γc_two_valued (v : V3) : γc v ≠ insuf := by cases v <;> decide

theorem γp_fixes_valid   : γp valid   = valid   := rfl
theorem γp_fixes_invalid : γp invalid = invalid := rfl
theorem γc_fixes_valid   : γc valid   = valid   := rfl
theorem γc_fixes_invalid : γc invalid = invalid := rfl

/-- Neither collapse is injective. -/
theorem γp_not_injective : ∃ a b, a ≠ b ∧ γp a = γp b :=
  ⟨insuf, valid, by decide, rfl⟩
theorem γc_not_injective : ∃ a b, a ≠ b ∧ γc a = γc b :=
  ⟨insuf, invalid, by decide, rfl⟩

/-- The two collapses agree everywhere except at Insufficient, where they
disagree. So a specification that enumerates only {Valid, Invalid} places no
constraint on the image of the third state: both maps are admissible, and
they differ by construction. -/
theorem collapses_agree_off_insuf (v : V3) (h : v ≠ insuf) : γp v = γc v := by
  cases v <;> simp_all [γp, γc]
theorem collapses_disagree_at_insuf : γp insuf ≠ γc insuf := by decide

/-- "No property of the underlying evidence selects between them": for any
evidence type `E` and any adjudication `f : E → V3`, both γp ∘ f and γc ∘ f
are two-valued, and they disagree exactly on the evidence adjudicated
Insufficient. -/
theorem collapse_unforced {E : Type} (f : E → V3) (e : E) :
    (γp (f e) ≠ insuf ∧ γc (f e) ≠ insuf) ∧
    (γp (f e) = γc (f e) ↔ f e ≠ insuf) := by
  refine ⟨⟨γp_two_valued _, γc_two_valued _⟩, ?_⟩
  cases h : f e <;> simp [γp, γc]

/-! ### 3. Pessimistic aggregation over a finite list of evaluators -/

variable {E : Type} [DecidableEq E]

/-- Agg w x over evaluators `es`: the weighted maximum max_e (w e ⊓ x e).
`w` is the authority row (a ceiling per evaluator), `x` the verdict profile. -/
def Agg (w x : E → V3) : List E → V3
  | []      => valid
  | e :: es => vmax (vmin (w e) (x e)) (Agg w x es)

/-- Probe profile: ⊤ (Insufficient) at `e`, ⊥ (Valid) elsewhere. -/
def probe (e : E) : E → V3 := fun e' => if e' = e then insuf else valid

theorem agg_le_of_all {w x : E → V3} {c : V3} :
    ∀ es : List E, (∀ e ∈ es, vmin (w e) (x e) ≤ c) → Agg w x es ≤ c
  | [], _ => by simp only [Agg]; exact valid_le c
  | e :: es, h => by
      simp only [Agg]
      exact vmax_le (h e (by simp)) (agg_le_of_all es (fun e' he' => h e' (by simp [he'])))

theorem le_agg_of_mem {w x : E → V3} :
    ∀ {es : List E} {e : E}, e ∈ es → vmin (w e) (x e) ≤ Agg w x es
  | [], _, h => by simp at h
  | e' :: es, e, h => by
      simp only [Agg]
      rcases List.mem_cons.mp h with rfl | h'
      · exact le_vmax_left _ _
      · exact le_trans (le_agg_of_mem h') (le_vmax_right _ _)

/-- RECOVERY. Probing evaluator `e` returns its weight, provided `e` is
among the evaluators. Each authority ceiling is therefore observable from the
aggregate: the operator determines the authority row. -/
theorem agg_probe (w : E → V3) (es : List E) (e : E) (he : e ∈ es) :
    Agg w (probe e) es = w e := by
  apply le_antisymm
  · apply agg_le_of_all
    intro e' _
    by_cases h : e' = e
    · subst h; rw [show probe e' e' = insuf from by simp [probe], vmin_insuf]; exact le_refl _
    · rw [show probe e e' = valid from by simp [probe, h], vmin_valid]; exact valid_le _
  · have h := le_agg_of_mem (w := w) (x := probe e) he
    rw [show probe e e = insuf from by simp [probe], vmin_insuf] at h
    exact h

/-- MONOTONICITY in the verdict profile. -/
theorem agg_mono (w : E → V3) {x y : E → V3} (h : ∀ e, x e ≤ y e) :
    ∀ es : List E, Agg w x es ≤ Agg w y es
  | [] => le_refl _
  | e :: es => by
      simp only [Agg]
      exact vmax_mono (vmin_mono_right (h e)) (agg_mono w h es)

/-- On a constant profile the aggregate is (sup of weights) ⊓ v. -/
theorem agg_const (w : E → V3) (v : V3) :
    ∀ es : List E, Agg w (fun _ => v) es = vmin (Agg w (fun _ => insuf) es) v
  | [] => by simp only [Agg]; cases v <;> rfl
  | e :: es => by
      simp only [Agg]
      rw [agg_const w v es, vmin_insuf]
      generalize Agg w (fun _ => insuf) es = A
      cases w e <;> cases v <;> cases A <;> rfl

/-- IDEMPOTENCE on constant profiles holds iff the weights join to ⊤, i.e.
some evaluator carries full authority. -/
theorem agg_idem_iff (w : E → V3) (es : List E) :
    (∀ v : V3, Agg w (fun _ => v) es = v) ↔ Agg w (fun _ => insuf) es = insuf := by
  constructor
  · intro h; exact h insuf
  · intro h v; rw [agg_const, h, vmin_insuf_left]

/-! ### 4. The descent theorem -/

/-- DESCENT. Fix an authority row `w` under which aggregation is idempotent
(some evaluator has full authority). For any relabelling ρ of reported
verdicts, the relabelled rule ρ ∘ Agg is idempotent on constant profiles iff
ρ is the identity. So no post-hoc lowering (or raising) of a reported verdict
is an adjudication: the only way a verdict descends is by the evidence
profile changing. -/
theorem descent (w : E → V3) (es : List E)
    (hw : Agg w (fun _ => insuf) es = insuf) (ρ : V3 → V3) :
    (∀ v : V3, ρ (Agg w (fun _ => v) es) = v) ↔ ρ = id := by
  have hid := (agg_idem_iff w es).mpr hw
  constructor
  · intro h; funext v; have := h v; rw [hid v] at this; exact this
  · intro h v; subst h; simp [hid v]

/-- In particular the two collapses are not adjudications: neither is the
identity, so neither commutes with an idempotent aggregation. -/
theorem γp_not_adjudication (w : E → V3) (es : List E)
    (hw : Agg w (fun _ => insuf) es = insuf) :
    ¬ (∀ v : V3, γp (Agg w (fun _ => v) es) = v) := by
  intro h
  have := (descent w es hw γp).mp h
  have h2 : γp insuf = id insuf := by rw [this]
  exact absurd h2 (by decide)

theorem γc_not_adjudication (w : E → V3) (es : List E)
    (hw : Agg w (fun _ => insuf) es = insuf) :
    ¬ (∀ v : V3, γc (Agg w (fun _ => v) es) = v) := by
  intro h
  have := (descent w es hw γc).mp h
  have h2 : γc insuf = id insuf := by rw [this]
  exact absurd h2 (by decide)

/-! ### 5. Blocking: Insufficient dominates Invalid in the aggregate -/

/-- If any evaluator with full authority reports Insufficient, the aggregate
is Insufficient, whatever every other evaluator reports. An uncharacterised
gap halts at least as firmly as a characterised violation. -/
theorem insuf_blocks (w x : E → V3) (es : List E) (e : E) (he : e ∈ es)
    (hw : w e = insuf) (hx : x e = insuf) : Agg w x es = insuf := by
  have h := le_agg_of_mem (w := w) (x := x) he
  rw [hw, hx] at h
  cases hA : Agg w x es <;> simp_all (config := {decide := true}) [vmin, LE.le, blk]

end Verdict

#print axioms Verdict.descent
#print axioms Verdict.collapse_unforced
#print axioms Verdict.agg_probe
#print axioms Verdict.insuf_blocks
#print axioms Verdict.agg_idem_iff
#print axioms Verdict.γp_not_adjudication
#print axioms Verdict.γc_not_adjudication
