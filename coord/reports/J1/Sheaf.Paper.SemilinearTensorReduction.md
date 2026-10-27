## What changed

Proved `WeilConjectures.SemilinearSections.systemTensorReduction` in
`Sheaf.Paper.SemilinearTensorReduction`, retaining its exact public signature and public import.
Added proved private helpers adapting the existing ordinary, cochain and derived reduction
arguments to `SystemScalarCoherence`, `SystemTensorBase` and `SystemTensorComparisons`.
The complete `Data` interface cannot be passed to the existing theorem: it additionally
requires internal-Hom data, which this obligation neither supplies nor needs.

Private proof imports reuse the existing sectionwise pure-tensor lemmas, tensor summand
naturality, localized transition factorization, generic diagram cancellation and K-flat
representative helpers. `SystemEvaluationFlat` supplies preservation of flat terms.
The original adjunction transpose definitions and normalized model squares are used throughout;
there is no choice of extra mathematical data and no restriction on the inputs or coefficient maps.
The proof covers equal indices, zero rings and unbounded inputs by the same identities.

The node proof now records the actual ordinary/cochain/localization/naturality argument.
Lean search used LeanFinder, Loogle and grep through msearch.py, followed by source searches;
the existing larger-interface proof supplies the route, whereas the Mathlib results only
supply generic adjunction APIs. Source checked: Zheng Construction 4.1, printed p. 21,
and Stacks sites-cohomology.tex, lemma-pullback-tensor-product (07A4).

Validation: the complete proof compiled in 56.9 seconds before two style-warning repairs.
The final delivery tool recompiles the final file with its axiom probe.
Change record: `coord/changes/J1-semilinear-tensor-reduction-proof-context.md`.

## Proved and sorry left

Closed 1 hole: `WeilConjectures.SemilinearSections.systemTensorReduction`
(node `lem-coef-semilinear-tensor-reduction`).
There are zero remaining `sorry` declarations in the item and zero holes added elsewhere.
All new private helpers are proved; this is a proof, not a decomposition.
Existing imported obligations are unchanged.

## No longer needed

No existing imports were removed and no module or node is withdrawn. The sole original
public import remains needed for the theorem's statement. Both original dependency modules
remain needed for the supplied structures; their existence theorems are not applied.
No new `Data` existence theorem, internal-Hom comparison or reduction compatibility split
is needed. No public source-library declaration was changed or removed.

## Where the brief, the DAG or earlier work was wrong

The old node described only an unspecified strict component of K-flat descent. The library
already contains a complete proof for the larger `Data` package. Its private generic tools
and its scalar/tensor proof steps suffice here after removing the unrelated interface
requirements. The node now states these steps explicitly. No mathematical statement,
canonical construction, target signature or unit route was changed.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
