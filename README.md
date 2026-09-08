# verdict-lean — machine-checked core of the third-verdict algebra

Two files, no dependencies. `Verdict.lean` is the three-valued instance used by
*The Indeterminate Verdict* (J. Applied Logics, submitted 2026). `Verdict8.lean`
is the eight-valued instance used by the ISMVL 2027 paper below. Both check under
Lean 4.12.0 with the core library only: no Mathlib, no `lakefile`, no `sorry`.

    elan toolchain install leanprover/lean4:v4.12.0   # or let elan read lean-toolchain
    lean Verdict.lean
    lean Verdict8.lean

## Verdict8.lean — ISMVL 2027

Companion to: D. L. Young and M. A. Thornton, "An Anisotropic-Authority
Characterization of Pessimistic Verdict Aggregation over a Belnap-Ordered
Eight-Valued Policy Chain," ISMVL 2027 (submission deadline 2026-11-01).

Checked 2026-09-08 with Lean 4.12.0, core library only (no Mathlib, no `sorry`).
Every theorem depends on at most `propext` and `Quot.sound`.

    lean Verdict8.lean          # about 20 s; the 8^3 and 8^4 case splits dominate

Carrier: `V8` = the paper's C_8 in blocking order, ⊥ = `allowAll`, ⊤ = `inconsistent`.
Aggregation `Agg w x es` = ⋁_{e ∈ es} (w e ⊓ x e) over a finite evaluator list.

| Paper | Lean | Statement |
|---|---|---|
| Thm 1(b) recovery | `agg_probe` | Agg w (σ_e) = w_e for e in the list |
| Thm 1(c) idempotence | `agg_idem_iff` | Agg w is idempotent on constants iff Agg w ⊤ = ⊤ |
| Thm 1(a) monotone | `agg_mono` | x ≤ y pointwise ⇒ Agg w x ≤ Agg w y |
| Thm 2 (⇒) maxitive | `Char.agg_maxitive` | Agg w (x ⊔ y) = Agg w x ⊔ Agg w y |
| Thm 2 (⇒) ceiling axiom A7 | `Char.agg_hom` | Agg w (c ⊓ x) = c ⊓ Agg w x |
| Thm 2 (⇐) characterization | `Char.characterization` | F maxitive ∧ ceiling ⇒ F x = Agg (λe. F σ_e) x es for x supported on a nodup list es |
| Prop. descent (ii) | `descent` | ρ ∘ Agg idempotent on constants iff ρ = id (given ⋁w = ⊤) |
| corollary | `γp_not_adjudication`, `γc_not_adjudication` | neither two-valued collapse of the top is an adjudication |
| Prop. Belnap stability (absorbing top) | `insuf_blocks` | full-authority ⊤ makes the aggregate ⊤ |
| — | `collapse_unforced` | the two collapses agree off ⊤ and disagree at ⊤; no evidence selects between them |

Not in the file: Prop. joint-blocking boundary; Prop. epistemic segregation;
Prop. oligarchy. All three are one-line consequences of `le_agg_of_mem` /
`agg_le_of_all` and could be added in an hour.

`Verdict.lean` is the three-valued instance used by the JAL paper; the proofs
are identical with the carrier replaced, which is what "the proofs do not depend
on the chain's size" means.

## License

MIT. Copyright (c) 2026 Darrell L. Young.
