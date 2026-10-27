## What changed

Proved `AlgebraicGeometry.ProEtale.relative_profinite_test_labels` with its exact original
statement. The proof constructs the labels by the specified homeomorphism, uses pullback
symmetry and pasting for comparison and base change, constructs finite coproduct legs from
point maps, and proves the affine Hom bijection by composing the pullback equivalence with
the existing stronger `affineMapEquiv`. Canonical component factorization follows from
surjectivity and injectivity of this bijection.

Private proved helpers are reused with `import all` from
`Sheaf.Paper.ProEtalePointComponentsMaps` and `Sheaf.Paper.ProfiniteTestObjectFunctor`.
No upstream source file, existing public declaration signature, or target changes.
The item node now records the actual route and dependencies. Import changes are recorded
in `coord/changes/M2-relative-profinite-test-labels-imports.md`. Its unit has no realized nodes
or realized proof steps to bypass.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.relative_profinite_test_labels`
(node `lem-sfb-relative-profinite-test-labels`), the one original hole.
Added: zero holes. Remaining in the item: zero. Split off: none.
All private definitions are explicit constructions; every private lemma is proved.
The finite cofan construction allows an empty index type; affine-map equivalence and
component quotient arguments allow empty schemes, empty targets, and the zero ring.

## No longer needed

Removed the direct import `Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite`:
its theorem is unnecessary; the required component-space instances already come from the
existing compact/quasi-separated scheme and connected-component imports.

The following original proof dependencies are not used directly by the replacement proof:
`lem-weil-pbc-finite-affine-coproduct-spectrum`,
`lem-sc-etale-fibre-product-base-change-coproduct`, and
`lem-weil-pbc-scheme-coproduct-family`: the existing continuity/coproduct-preservation
argument supplies the finite cofan, and evaluation at the point normalizes its legs.
`lem-weil-pbc-affine-scheme-qcqs`, `lem-weil-pbc-qcqs-scheme-spectral`,
`lem-pe-spectral-components-profinite`, and
`def-weil-pbc-profinite-locally-constant-hom-equiv`: the proved affine map equivalence
already gives the exact normalized bijection without explicitly factoring through
components. These results may still be used elsewhere, including inside reused proofs;
no module or upstream declaration is withdrawn and no global pruning is claimed.

Removed the obsolete proof-tool approval for `lem-pe-spectral-components-profinite`;
its statement dependency is retained.

The pullback-pasting import is needed only by the proof and becomes private. The
profinite-test-object module is likewise a proof import; the statement imports its
underlying definitions directly from `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.

## Where the brief, the DAG or earlier work was wrong

The DAG's locally constant ring-Hom equivalence is a private upstream declaration.
`import all` permits reusing proved private helpers without changing the source-library
interface. More directly useful here, `ProEtalePointComponentsMaps` already contains a
proved affine-map equivalence for all affine schemes, stronger than its public theorem's
weakly contractible pro-etale formulation. Its evaluation-prime formula is exactly the
normalization this item requires. Reusing that construction avoids rebuilding the ring
argument or imposing the public theorem's extra hypotheses.

Searches: launcher LeanFinder for affine maps into spectra of locally constant integers;
Loogle for finite colimit cofans; launcher grep and repository ripgrep for the ring-Hom
and normalized affine-map equivalences. The existing helpers were the shorter route.

Fresh remote compilation of the item and both unchanged direct importers passed:
`RelativeProfiniteTestLabels` (20.5 seconds), `NormalizedContinuousSetComparisonCoherence`
(7.3 seconds), and `NormalizedContinuousSetKanEvaluation` (8.2 seconds). The consumer
sources remain unchanged; their check copies live only under scratchpad and are excluded
from delivery. The change record lists both current holders, R6 and R7.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
