Files written:

- `dag/nodes/sec-trace-formula/lem-trf-integral-compact-transport-recurrence.json`: statement-only prerequisite for coherent integral compact-support transport recurrence; Mathlib searches found no match.
- `dag/nodes/sec-trace-formula/lem-trf-rational-global-frobenius-powers.json`: repaired split item; no Mathlib match.
- `citations.json`: verbatim citation quotations for every cited node in every item proof step.

Attachments: none.

WANTED: none.

The returned version had a C4/E5/F2 gap in Step 1. It used the finite-level recurrence and then invoked rationalization without proving that the specified finite-level maps form one coherent tower, or that the two recurrence sides agree before derived realization. I added `lem-trf-integral-compact-transport-recurrence`, whose statement is strictly smaller than the item: it has no rational object or coefficient morphism and only establishes coherence and recurrence for the specified integral transports. The item now uses that equality first, and invokes rational extension only afterward. No statement was weakened or changed.

## Review by N9

I reread the returned item, the current `prop-trf-rational-frobenius-integral-model`, `lem-trf-compact-frobenius-transport-composition`, `prop-weil-pbc-rational-transport`, `def-weil-frobenius-cohomology-transport`, `lem-trf-global-frobenius-iterate-formula`, the compact-support reduction-tower node `lem-weil-compact-support-reduction-tower-functor`, and `lem-trf-integral-point-transport-tower-realization`. I also reread the Global powers paragraph and its proof in `literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-thm-trace-transport/thm-trf-l-function-euler-product.proof.md`, and clause (3) of the integral-model blueprint proof.

The new lemma's Step 1 checks the actual transition square: the fixed compactification exchange and the point-transport maps are evaluated at every reduction and are natural for the quotient transitions, so their composites are a single morphism of coherent reduction towers. The cited reduction-tower statement supplies the evaluation and transition maps of compact support; the point-transport realization statement supplies the tower morphism and its naturality. Step 2 applies the finite transport-composition statement at every level. Since both sides are already tower morphisms built from the same specified comparisons, equality of their components is equality of the coherent tower maps themselves; this is the explicit pre-realization equality missing from the returned version. Step 3 applies the specified derived-limit realization and obtains the integral identity for `U_{m+1}`.

For the repaired item, Step 1 now takes exactly this integral tower equality, then uses the rational-transport proposition's unique extension of the specified functors and natural transformations and the integral-model proposition's identification of the specified `B_m` with the rationalized `U_m`. Scalar extension is applied only after the integral identity is established. The naturality hypothesis comes from the compact-support Frobenius transport definition. Step 2 uses the generic categorical transport-power identity with `G = Lg_γ^*`, `C = RΓ_c`, and `t = B_1`; its arbitrary morphism hypothesis matches the item. Step 3 performs the induction identifying the successive degree-one transport with `B_m` and then uses the operator formula from the integral-model proposition. Step 4 checks that neither the generic identity nor the integral-model proposition introduces invertibility of `φ_E` or of a lattice map.

I checked `m=1` and `m=2`, the empty scheme and zero object, and the point example with `φ_E=diag(1,ℓ)`. I also checked that the new lemma does not duplicate the finite-level recurrence: it adds the coherent integral tower and pre-realization equality, while the existing finite node has a single finite coefficient ring and no reduction tower. All entries in `citations.json` were checked as verbatim substrings of the cited statements. The Mathlib searches for the new lemma used LeanFinder, LeanSearch, Loogle, and Mathlib grep with two independent natural-language phrasings; only unrelated ring-Frobenius and inverse-system declarations appeared.

Nothing remains unfinished in this repair. No Lean was written and no compiler, Lake, build, or live-project command was run.
