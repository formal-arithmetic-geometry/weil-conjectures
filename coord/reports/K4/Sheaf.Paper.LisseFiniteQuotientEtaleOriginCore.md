## What changed

Proved `AlgebraicGeometry.Scheme.lisse_finite_quotient_etale_origin_core` in
`Sheaf.Paper.LisseFiniteQuotientEtaleOriginCore`. The theorem signature, core structure,
existing public imports and source-library files are unchanged.

The proof translates the actual inverse image of `K` into fixed finite coefficients,
uses bounded constructible derived descent to obtain an étale complex `L`, reflects finite
local constancy and zero cohomology, transfers `L` to the completion quotient, and pulls it
back to `V`. For refinements, the comparison/pullback square transports finite local models
of `L` to the original pullback of `K`. In particular, the chosen level is an actual descended
origin; the proof does not fill the level with an unrelated zero object.

Added proved private helpers for exact inverse image, fixed-coefficient pullback/homology
comparison, and preservation of finite locally constant sheaves under scalar restriction.
Proof-only imports reuse the proved private coefficient encodings in
`ProEtaleConstantModuleConstructibility` and `PbcFinitePullbackConstructibility`,
`quotient_map_bijective` in `ConstantAdicQuotientScalarComparison`, and
`origin_boundedConstructible_of_homology` in `FiniteCoefficientDerivedOriginPresentation`.
The latter is a bounded finite-truncation argument already present in the library;
no additional existence obligation is introduced. The remaining proof imports provide
finite-local-constancy reflection, étale pullback, finite-value models and scalar restriction.
Updated only this module's node proof, proof dependencies and proof origin.

LeanFinder found only unrelated condensed-category results; Loogle and the requested grep
search found no exact theorem for this interface. Repository searches found the proved
bounded-descent helper, which gives the shorter route used here. The unit's finite-coefficient
descent route is retained. The final file compiled cleanly in 13.5 seconds through the prescribed remote compiler.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.lisse_finite_quotient_etale_origin_core`
(node `lem-weil-pbc-lisse-finite-quotient-etale-origin-core`).

Added 0 holes and split off 0 statements. The item has 0 `sorry` occurrences; every private
helper is completely proved. No other Lean module is delivered. This is a proof from the
existing library declarations, rather than a claim that every imported dependency's own
axiom closure has already been completed.

## No longer needed

No existing public import or declaration is removed, and no module is withdrawn.
The original direct proof dependencies `prop-weil-pbc-site-comparison-finite-level`,
`thm-weil-pbc-site-comparison` and `lem-weil-pbc-adic-completion-mod-ideal` are replaced
by the precise bounded-descent, reflection and proved quotient-comparison APIs named in
the updated node. Some are still transitive dependencies; this is not a claim that they
are globally unused or may be deleted.

The full public finite-coefficient presentation theorem is unnecessary here: its proved
bounded-origin helper already supplies the required étale complex and comparison.
`NormalizedTowerLissePropagation` and `ProEtaleOriginFromFiniteModels`, considered during
development, are not needed as imports: local comparison glue and the same descended `L`
prove the refinement assertion. No new tower or origin obligation is left for another worker.

## Where the brief, the DAG or earlier work was wrong

The existing DAG's one-step plan concealed the distinction between ring-sheaf modules and
fixed-coefficient sheaves, and the exact derived coefficient/pullback square. The local
proved comparison helpers now supply that glue. The main statement is proved unchanged,
including empty charts, empty refinement sites and arbitrary vanishing degrees; no point,
nonempty chart or simultaneous constant model is assumed.

STATEMENT-DISPUTED: the adjacent
`AlgebraicGeometry.Scheme.lisse_finite_quotient_etale_origin_transport`
in `Sheaf.Paper.LisseFiniteQuotientEtaleOriginTransport` refers in its proof text to a
"core comparison", but `LisseFiniteQuotientEtaleOriginCore` has no comparison field linking
`level` to `K`. Its universally quantified `C` can have `level = 0` even when `K` is a nonzero
constant complex: lisse and vanishing hold for zero, while refinementLisse is a condition
only on `K`. With identity charts and `E = 0`, its claimed transport then identifies zero
with that nonzero pullback of `K`. This is a genuine missing invariant, not a missing proof
step. The intended descent constructed in this delivery does have a comparison locally in
the proof, but the current structure forgets it, so it cannot justify transport for arbitrary
`C`. The transport item was held by M1 when checked. Its owner/reviewer needs to retain the
comparison in the core interface, or combine descent and transport before forgetting it.
No unrelated held module or public interface was altered by this delivery.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.LisseFiniteQuotientEtaleOriginCore": "9785c896b5d07afabbe219ee690bd18a07ac6168"}, "results": {"Sheaf.Paper.LisseFiniteQuotientEtaleOrigin": {"hash": "cf194cfc144c76044546ae2873a5578cc30d42e8", "status": "OK"}, "Sheaf.Paper.LisseFiniteQuotientEtaleOriginTransport": {"hash": "71e4990fb446590a309b27d4852de82b5797a5c5", "status": "OK"}}, "seconds": 48, "time": "2026-10-28T04:16:27+0800", "transitive": 0, "version": 1}
```

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
