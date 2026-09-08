/-
  Verdict8.lean — the same theorems over the eight-valued ISMVL chain C_8.

  Companion to: D. L. Young and M. A. Thornton, "The Indeterminate Verdict"
  (JAL, submitted 2026) and "An Anisotropic-Authority Characterization of
  Pessimistic Verdict Aggregation over a Belnap-Ordered Eight-Valued Policy
  Chain" (ISMVL 2027, submitted).

  Checked with Lean 4.12.0, core library only. No Mathlib, no axioms beyond
  Lean's three standard ones. `#print axioms` at the bottom confirms it.

  Contents
    1. V8, the eight-valued policy chain of the ISMVL paper, with blocking
       precedence AllowAll < AwC < Caveat < Review < Reject < Refuse <
       Unknown < Inconsistent. (Constructor names `allowAll`, `refuse`,
       `inconsistent` play the roles ⊥, a determinate block, and ⊤; the
       lemma names inherited from the three-valued file, e.g. `insuf_blocks`,
       refer to the top element.)
    2. Proposition 1 (JAL): the two total collapses to {Valid, Invalid} are
       non-injective and disagree at Insufficient; no property of the
       evidence selects between them.
    3. Pessimistic aggregation Agg = max_e (w_e ⊓ x_e) over a finite list of
       evaluators: recovery, monotonicity, idempotence iff some weight is ⊤.
    4. Descent theorem: for any relabelling ρ, ρ ∘ Agg is idempotent on
       constant profiles iff ρ = id. Hence no post-hoc lowering of a
       reported verdict is an adjudication under any authority row.
    5. Blocking: a top verdict from any full-authority evaluator is absorbing.
    6. Characterization (ISMVL Theorem 2): any F that is maxitive and
       satisfies the ceiling axiom F(c ⊓ x) = c ⊓ F(x) agrees with the
       weighted maximum whose weights are w_e = F(σ_e), on every profile
       supported on a duplicate-free evaluator list; and the weighted
       maximum has both properties (forward direction).
-/

namespace Verdict8

/-! ### 1. The verdict set and its blocking order -/

inductive V8 where
  | allowAll | awc | caveat | review | reject | refuse | unknown | inconsistent
  deriving DecidableEq, Repr

open V8

/-- Blocking precedence: a verdict dominates to the extent that it licenses
less confident reliance. Valid < Invalid < Insufficient. -/
def blk : V8 → Nat
  | allowAll     => 0
  | awc          => 1
  | caveat       => 2
  | review       => 3
  | reject       => 4
  | refuse       => 5
  | unknown      => 6
  | inconsistent => 7

instance : LE V8 := ⟨fun a b => blk a ≤ blk b⟩
instance : LT V8 := ⟨fun a b => blk a < blk b⟩

instance (a b : V8) : Decidable (a ≤ b) := inferInstanceAs (Decidable (blk a ≤ blk b))
instance (a b : V8) : Decidable (a < b) := inferInstanceAs (Decidable (blk a < blk b))

theorem valid_lt_invalid : allowAll < refuse := by decide
theorem invalid_lt_insuf : refuse < inconsistent := by decide

/-- Join and meet in the blocking order. -/
def vmax (a b : V8) : V8 := if blk a ≤ blk b then b else a
def vmin (a b : V8) : V8 := if blk a ≤ blk b then a else b

theorem le_refl (a : V8) : a ≤ a := by cases a <;> decide
theorem le_trans {a b c : V8} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all (config := {decide := true}) [LE.le, blk]
theorem le_antisymm {a b : V8} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  cases a <;> cases b <;> simp_all (config := {decide := true}) [LE.le, blk]
theorem le_total (a b : V8) : a ≤ b ∨ b ≤ a := by cases a <;> cases b <;> decide

theorem vmax_comm (a b : V8) : vmax a b = vmax b a := by cases a <;> cases b <;> decide
theorem vmin_comm (a b : V8) : vmin a b = vmin b a := by cases a <;> cases b <;> decide
theorem le_vmax_left (a b : V8) : a ≤ vmax a b := by cases a <;> cases b <;> decide
theorem le_vmax_right (a b : V8) : b ≤ vmax a b := by cases a <;> cases b <;> decide
theorem vmax_le {a b c : V8} (h₁ : a ≤ c) (h₂ : b ≤ c) : vmax a b ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all (config := {decide := true}) [vmax, LE.le, blk]
theorem vmin_le_left (a b : V8) : vmin a b ≤ a := by cases a <;> cases b <;> decide
theorem vmin_le_right (a b : V8) : vmin a b ≤ b := by cases a <;> cases b <;> decide
theorem vmin_mono_right {a b c : V8} (h : b ≤ c) : vmin a b ≤ vmin a c := by
  cases a <;> cases b <;> cases c <;> simp_all (config := {decide := true}) [vmin, LE.le, blk]
theorem vmax_mono {a b c d : V8} (h₁ : a ≤ c) (h₂ : b ≤ d) : vmax a b ≤ vmax c d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all (config := {decide := true}) [vmax, LE.le, blk]
theorem vmin_insuf (a : V8) : vmin a inconsistent = a := by cases a <;> decide
theorem vmin_insuf_left (a : V8) : vmin inconsistent a = a := by cases a <;> decide
theorem vmax_valid (a : V8) : vmax a allowAll = a := by cases a <;> decide
theorem vmax_valid_left (a : V8) : vmax allowAll a = a := by cases a <;> decide
theorem vmax_self (a : V8) : vmax a a = a := by cases a <;> decide
theorem vmin_self (a : V8) : vmin a a = a := by cases a <;> decide
theorem vmin_valid (a : V8) : vmin a allowAll = allowAll := by cases a <;> decide
theorem valid_le (a : V8) : allowAll ≤ a := by cases a <;> decide

/-! ### 2. Proposition 1: the two-valued collapse is lossy and unforced -/

/-- The permissive collapse: Insufficient ↦ Valid. -/
def γp : V8 → V8
  | inconsistent => allowAll
  | v     => v

/-- The conservative collapse: Insufficient ↦ Invalid. -/
def γc : V8 → V8
  | inconsistent => refuse
  | v     => v

theorem γp_two_valued (v : V8) : γp v ≠ inconsistent := by cases v <;> decide
theorem γc_two_valued (v : V8) : γc v ≠ inconsistent := by cases v <;> decide

theorem γp_fixes_valid   : γp allowAll   = allowAll   := rfl
theorem γp_fixes_invalid : γp refuse = refuse := rfl
theorem γc_fixes_valid   : γc allowAll   = allowAll   := rfl
theorem γc_fixes_invalid : γc refuse = refuse := rfl

/-- Neither collapse is injective. -/
theorem γp_not_injective : ∃ a b, a ≠ b ∧ γp a = γp b :=
  ⟨inconsistent, allowAll, by decide, rfl⟩
theorem γc_not_injective : ∃ a b, a ≠ b ∧ γc a = γc b :=
  ⟨inconsistent, refuse, by decide, rfl⟩

/-- The two collapses agree everywhere except at Insufficient, where they
disagree. So a specification that enumerates only {Valid, Invalid} places no
constraint on the image of the third state: both maps are admissible, and
they differ by construction. -/
theorem collapses_agree_off_insuf (v : V8) (h : v ≠ inconsistent) : γp v = γc v := by
  cases v <;> simp_all [γp, γc]
theorem collapses_disagree_at_insuf : γp inconsistent ≠ γc inconsistent := by decide

/-- "No property of the underlying evidence selects between them": for any
evidence type `E` and any adjudication `f : E → V8`, both γp ∘ f and γc ∘ f
are two-valued, and they disagree exactly on the evidence adjudicated
Insufficient. -/
theorem collapse_unforced {E : Type} (f : E → V8) (e : E) :
    (γp (f e) ≠ inconsistent ∧ γc (f e) ≠ inconsistent) ∧
    (γp (f e) = γc (f e) ↔ f e ≠ inconsistent) := by
  refine ⟨⟨γp_two_valued _, γc_two_valued _⟩, ?_⟩
  cases h : f e <;> simp [γp, γc]

/-! ### 3. Pessimistic aggregation over a finite list of evaluators -/

variable {E : Type} [DecidableEq E]

/-- Agg w x over evaluators `es`: the weighted maximum max_e (w e ⊓ x e).
`w` is the authority row (a ceiling per evaluator), `x` the verdict profile. -/
def Agg (w x : E → V8) : List E → V8
  | []      => allowAll
  | e :: es => vmax (vmin (w e) (x e)) (Agg w x es)

/-- Probe profile: ⊤ (Insufficient) at `e`, ⊥ (Valid) elsewhere. -/
def probe (e : E) : E → V8 := fun e' => if e' = e then inconsistent else allowAll

theorem agg_le_of_all {w x : E → V8} {c : V8} :
    ∀ es : List E, (∀ e ∈ es, vmin (w e) (x e) ≤ c) → Agg w x es ≤ c
  | [], _ => by simp only [Agg]; exact valid_le c
  | e :: es, h => by
      simp only [Agg]
      exact vmax_le (h e (by simp)) (agg_le_of_all es (fun e' he' => h e' (by simp [he'])))

theorem le_agg_of_mem {w x : E → V8} :
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
theorem agg_probe (w : E → V8) (es : List E) (e : E) (he : e ∈ es) :
    Agg w (probe e) es = w e := by
  apply le_antisymm
  · apply agg_le_of_all
    intro e' _
    by_cases h : e' = e
    · subst h; rw [show probe e' e' = inconsistent from by simp [probe], vmin_insuf]; exact le_refl _
    · rw [show probe e e' = allowAll from by simp [probe, h], vmin_valid]; exact valid_le _
  · have h := le_agg_of_mem (w := w) (x := probe e) he
    rw [show probe e e = inconsistent from by simp [probe], vmin_insuf] at h
    exact h

/-- MONOTONICITY in the verdict profile. -/
theorem agg_mono (w : E → V8) {x y : E → V8} (h : ∀ e, x e ≤ y e) :
    ∀ es : List E, Agg w x es ≤ Agg w y es
  | [] => le_refl _
  | e :: es => by
      simp only [Agg]
      exact vmax_mono (vmin_mono_right (h e)) (agg_mono w h es)

/-- On a constant profile the aggregate is (sup of weights) ⊓ v. -/
theorem agg_const (w : E → V8) (v : V8) :
    ∀ es : List E, Agg w (fun _ => v) es = vmin (Agg w (fun _ => inconsistent) es) v
  | [] => by simp only [Agg]; cases v <;> rfl
  | e :: es => by
      simp only [Agg]
      rw [agg_const w v es, vmin_insuf]
      generalize Agg w (fun _ => inconsistent) es = A
      cases w e <;> cases v <;> cases A <;> rfl

/-- IDEMPOTENCE on constant profiles holds iff the weights join to ⊤, i.e.
some evaluator carries full authority. -/
theorem agg_idem_iff (w : E → V8) (es : List E) :
    (∀ v : V8, Agg w (fun _ => v) es = v) ↔ Agg w (fun _ => inconsistent) es = inconsistent := by
  constructor
  · intro h; exact h inconsistent
  · intro h v; rw [agg_const, h, vmin_insuf_left]

/-! ### 4. The descent theorem -/

/-- DESCENT. Fix an authority row `w` under which aggregation is idempotent
(some evaluator has full authority). For any relabelling ρ of reported
verdicts, the relabelled rule ρ ∘ Agg is idempotent on constant profiles iff
ρ is the identity. So no post-hoc lowering (or raising) of a reported verdict
is an adjudication: the only way a verdict descends is by the evidence
profile changing. -/
theorem descent (w : E → V8) (es : List E)
    (hw : Agg w (fun _ => inconsistent) es = inconsistent) (ρ : V8 → V8) :
    (∀ v : V8, ρ (Agg w (fun _ => v) es) = v) ↔ ρ = id := by
  have hid := (agg_idem_iff w es).mpr hw
  constructor
  · intro h; funext v; have := h v; rw [hid v] at this; exact this
  · intro h v; subst h; simp [hid v]

/-- In particular the two collapses are not adjudications: neither is the
identity, so neither commutes with an idempotent aggregation. -/
theorem γp_not_adjudication (w : E → V8) (es : List E)
    (hw : Agg w (fun _ => inconsistent) es = inconsistent) :
    ¬ (∀ v : V8, γp (Agg w (fun _ => v) es) = v) := by
  intro h
  have := (descent w es hw γp).mp h
  have h2 : γp inconsistent = id inconsistent := by rw [this]
  exact absurd h2 (by decide)

theorem γc_not_adjudication (w : E → V8) (es : List E)
    (hw : Agg w (fun _ => inconsistent) es = inconsistent) :
    ¬ (∀ v : V8, γc (Agg w (fun _ => v) es) = v) := by
  intro h
  have := (descent w es hw γc).mp h
  have h2 : γc inconsistent = id inconsistent := by rw [this]
  exact absurd h2 (by decide)

/-! ### 5. Blocking: Insufficient dominates Invalid in the aggregate -/

/-- If any evaluator with full authority reports Insufficient, the aggregate
is Insufficient, whatever every other evaluator reports. An uncharacterised
gap halts at least as firmly as a characterised violation. -/
theorem insuf_blocks (w x : E → V8) (es : List E) (e : E) (he : e ∈ es)
    (hw : w e = inconsistent) (hx : x e = inconsistent) : Agg w x es = inconsistent := by
  have h := le_agg_of_mem (w := w) (x := x) he
  rw [hw, hx] at h
  cases hA : Agg w x es <;> simp_all (config := {decide := true}) [vmin, LE.le, blk]

/-! ### 6. Characterization: maxitivity and the ceiling axiom force the form -/

namespace Char

/-- Pointwise join of profiles. -/
def pjoin (x y : E → V8) : E → V8 := fun e => vmax (x e) (y e)
/-- Scalar meet of a profile: the profile (c ⊓ x_e)_e. -/
def pscale (c : V8) (x : E → V8) : E → V8 := fun e => vmin c (x e)
/-- The bottom profile. -/
def pbot : E → V8 := fun _ => allowAll

theorem vmax_assoc (a b c : V8) : vmax (vmax a b) c = vmax a (vmax b c) := by
  cases a <;> cases b <;> cases c <;> decide
theorem vmin_assoc (a b c : V8) : vmin (vmin a b) c = vmin a (vmin b c) := by
  cases a <;> cases b <;> cases c <;> decide
theorem vmin_vmax_distrib (a b c : V8) :
    vmin a (vmax b c) = vmax (vmin a b) (vmin a c) := by
  cases a <;> cases b <;> cases c <;> decide
theorem vmin_bot (a : V8) : vmin allowAll a = allowAll := by cases a <;> decide

/-- Forward direction (i): the weighted maximum is maxitive. -/
theorem agg_maxitive (w x y : E → V8) :
    ∀ es : List E, Agg w (pjoin x y) es = vmax (Agg w x es) (Agg w y es)
  | [] => by simp only [Agg]; decide
  | e :: es => by
      simp only [Agg, pjoin]
      rw [agg_maxitive w x y es, vmin_vmax_distrib]
      generalize vmin (w e) (x e) = p
      generalize vmin (w e) (y e) = q
      generalize Agg w x es = A
      generalize Agg w y es = B
      cases p <;> cases q <;> cases A <;> cases B <;> decide

/-- Forward direction (ii): the weighted maximum satisfies the ceiling axiom. -/
theorem agg_hom (w x : E → V8) (c : V8) :
    ∀ es : List E, Agg w (pscale c x) es = vmin c (Agg w x es)
  | [] => by simp only [Agg]; cases c <;> decide
  | e :: es => by
      simp only [Agg, pscale]
      rw [agg_hom w x c es, vmin_vmax_distrib]
      congr 1
      generalize w e = a; generalize x e = b
      cases a <;> cases b <;> cases c <;> decide

/-- Decomposition of a profile into scaled probes over an evaluator list. -/
def decompose (x : E → V8) : List E → (E → V8)
  | []      => pbot
  | e :: es => pjoin (pscale (x e) (probe e)) (decompose x es)

theorem decompose_apply_notin (x : E → V8) :
    ∀ (es : List E) (e' : E), e' ∉ es → decompose x es e' = allowAll
  | [], _, _ => rfl
  | e :: es, e', h => by
      have h1 : e ≠ e' := fun he => h (by simp [he])
      have h2 : e' ∉ es := fun he => h (by simp [he])
      simp only [decompose, pjoin, pscale, probe]
      rw [decompose_apply_notin x es e' h2]
      have : (if e' = e then inconsistent else allowAll) = allowAll := by
        simp [Ne.symm h1]
      rw [this]
      generalize x e = a
      cases a <;> decide

theorem decompose_apply_mem (x : E → V8) :
    ∀ (es : List E) (e' : E), es.Nodup → e' ∈ es → decompose x es e' = x e'
  | [], _, _, h => by simp at h
  | e :: es, e', hnd, h => by
      simp only [decompose, pjoin, pscale, probe]
      rcases List.mem_cons.mp h with rfl | h'
      · have : e' ∉ es := (List.nodup_cons.mp hnd).1
        rw [decompose_apply_notin x es e' this]
        simp only [if_true]
        generalize x e' = a
        cases a <;> decide
      · have hne : e' ≠ e := fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ h')
        rw [decompose_apply_mem x es e' (List.nodup_cons.mp hnd).2 h']
        simp only [hne, if_false]
        generalize x e = a; generalize x e' = b
        cases a <;> cases b <;> decide

/-- A profile supported on a duplicate-free list equals its decomposition. -/
theorem decompose_eq (x : E → V8) (es : List E) (hnd : es.Nodup)
    (hsupp : ∀ e, e ∉ es → x e = allowAll) : decompose x es = x := by
  funext e'
  by_cases h : e' ∈ es
  · exact decompose_apply_mem x es e' hnd h
  · rw [decompose_apply_notin x es e' h, hsupp e' h]

/-- Converse (Theorem 2 of the ISMVL paper). Any F that is maxitive and
satisfies the ceiling axiom agrees, on every profile supported on a
duplicate-free evaluator list, with the weighted maximum whose weights are
read off by probing: w_e = F(σ_e). -/
theorem characterization (F : (E → V8) → V8)
    (hmax : ∀ x y, F (pjoin x y) = vmax (F x) (F y))
    (hhom : ∀ c x, F (pscale c x) = vmin c (F x))
    (x : E → V8) (es : List E) (hnd : es.Nodup)
    (hsupp : ∀ e, e ∉ es → x e = allowAll) :
    F x = Agg (fun e => F (probe e)) x es := by
  have hbot : F (pbot (E := E)) = allowAll := by
    have h1 : pscale allowAll (pbot (E := E)) = pbot := by
      funext e; simp only [pscale, pbot]; decide
    have := hhom allowAll (pbot (E := E))
    rw [h1] at this
    rw [this]; generalize F (pbot (E := E)) = a; cases a <;> decide
  have key : ∀ es' : List E, F (decompose x es') = Agg (fun e => F (probe e)) x es' := by
    intro es'
    induction es' with
    | nil => simp only [decompose, Agg]; exact hbot
    | cons e rest ih =>
        simp only [decompose, Agg]
        rw [hmax, hhom, ih]
        congr 1
        generalize x e = a; generalize F (probe e) = b
        cases a <;> cases b <;> decide
  have hx := decompose_eq x es hnd hsupp
  calc F x = F (decompose x es) := by rw [hx]
    _ = Agg (fun e => F (probe e)) x es := key es

end Char

end Verdict8

#print axioms Verdict8.descent
#print axioms Verdict8.collapse_unforced
#print axioms Verdict8.agg_probe
#print axioms Verdict8.insuf_blocks
#print axioms Verdict8.Char.characterization
#print axioms Verdict8.Char.agg_maxitive
#print axioms Verdict8.Char.agg_hom
#print axioms Verdict8.agg_idem_iff
#print axioms Verdict8.γp_not_adjudication
#print axioms Verdict8.γc_not_adjudication
