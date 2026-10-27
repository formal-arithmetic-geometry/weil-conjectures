## What changed

Replaced the body of `WeilConjectures.fdNormalizedIntegralCompletionComparison` with
an assembly of the recorded normalized comparisons. Its signature and the two restriction
definitions are unchanged. The proof obtains the signed representative shifts from
`completedScalarComparison_commutesWithShift`, proves invertibility on intrinsic
constructible objects using `sfDerivedComplete_iff_legacy` and the finite-free comparison,
and constructs the natural isomorphism in the literal full subcategories. The shifts
are descended through the fully faithful inclusion, with their inclusion normalization
proved explicitly. The ambient comparison shift square then restricts, its inverse follows
by cancellation, and exactness transfers along the same natural isomorphism. The canonical
localization equation, quotient and zero coordinates, and identity unit specialization
are taken from the existing uniquely normalized constructions.

Two auxiliary modules isolate ordinary exactness with the specified counit-normalized
shift and the remaining coefficient-presentation scalar lift. These are strictly smaller
parts of original steps 5 and 2–3 respectively. The proposed exactness argument compares the actual
ordinary derived functor with the exact termwise model and identifies their shift maps
using the retained counits on good representatives. The coefficient lift records only
the generator transport and representative equation: it asserts neither the main
restricted comparison nor its exactness or shift compatibility.

## Proved and sorry left

The original module has one hole, in
`WeilConjectures.fdNormalizedIntegralCompletionComparison`. Its replacement is a complete
Lean assembly from the listed dependencies and the auxiliary statements.

The packet is a decomposition, not an unconditional proof of the entire comparison.
The remaining coefficient-presentation step is
`WeilConjectures.fdCoefficientScalarLift_normalization`, node
`lem-fd-coefficient-scalar-lift-normalization`. Its statement is a proper part of the
argument, with its complete proof in words in the module and its node. The other remaining hole is
`WeilConjectures.completedScalarOrdinary_normalized_exact`, node
`lem-fd-ordinary-scalar-normalized-exact`. Thus one original hole is closed and two
strictly smaller holes are added; no hole remains in the assigned module. This is a
decomposition, with net minus one hole closed, not a net hole reduction.

## No longer needed

The direct proof imports of `Sheaf.Paper.SfIntegralConstructible`,
`Sheaf.Paper.IntegralCoefficientPresentationComparison`,
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact` and
`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` are unnecessary for the main
assembly. Constructibility is already part of the statement imports; the normalized
finite-free and shift theorems already supply the actual maps, coordinates and descent.
The original public imports are preserved as the published interface. The isolated coefficient transport step also imports
`Sheaf.Paper.CompletedCoefficientPresentationTransport` for its proof plan.

The main proof no longer directly invokes
`lem-weil-pbc-integral-stratified-perfect-characterization`,
`lem-weil-pbc-integral-coefficient-presentation-comparison`,
`lem-weil-proetale-countable-products-exact`,
`lem-pur-quotient-scalar-comparison-descent`,
`lem-weil-completed-scalar-chain-shift`,
`lem-weil-completed-scalar-shift-descent`, or `lem-pur-derived-change-of-rings`.
Their needed work is encapsulated by the existing normalized comparison interfaces or
by the new smaller steps. No existing Lean module is withdrawn, and no whole-library
pruning is claimed; some of these remain transitive dependencies.

## Where the brief, the DAG or earlier work was wrong

The existing completed scalar shift theorem already supplies all three specified
shift structures and the ambient comparison shift square. No new cone-coordinate,
representative-independence, or shift-descent statements are needed. The original
plan did not state exactness for the ordinary shift fixed by the recorded counit;
existence of some triangulated shift alone does not prove that normalization.
The auxiliary exactness statement isolates precisely this distinction. A concrete
proof attempt uses the existing exact termwise model and canonical left-derived
isomorphism. The attempt reached `ordinaryScalarModelIso`, present in current source
but unavailable in the compiled snapshot; it is retained locally as proof-development
notes, not as an additional library declaration.

The current blueprint trace definition is now in
`literature/blueprint/latest/blueprint/sec-fourier-transform/sk-cor-plancherel/`;
the old node cites the historical `sk-def-trace` location. The target signature is
preserved and no claim about changed blueprint content is used to weaken it.

Edge cases checked mathematically: an empty scheme (all maps are the unique maps),
zero complexes, identity coefficient inclusions, equal fields, ramified finite
extensions, shifts zero and negative, and arbitrary coefficient subfields of Ω.
The auxiliary finite-field datum used solely for the legacy completeness presentation
has characteristic greater than l, and imposes no structure map on T. Normalized
ordinary exactness makes no completeness or constructibility assumption.

## New nodes

`lem-fd-ordinary-scalar-normalized-exact`:
`Sheaf.Paper.CompletedScalarOrdinaryNormalizedExact`,
`WeilConjectures.completedScalarOrdinary_normalized_exact`. This is original proof
step 5 for ordinary derived tensor alone. It does not assert constructible restriction,
the completed comparison, its inverse, or the coefficient lift.

`lem-fd-coefficient-scalar-lift-normalization`:
`Sheaf.Paper.FdCoefficientScalarLiftNormalization`,
`WeilConjectures.fdCoefficientScalarLift_normalization`. This is the original
coefficient-generator and representative-localization transport of steps 2–3 only.
It retains the actual counits, coefficient factors and quotient completion chain map.

No statement or definition change record is needed: no existing signature, definition,
visibility, or public import is changed. No forced consumer adaptations are made.

The proof uses `lem-weil-point-completed-scalar-shift` as a generic normalized-shift
tool, in place of reproving its chain calculation and descent. It is not part of the
other unit's specific point-coefficient equivalence argument. The maintainer should
record the corresponding tool approval if required; the delivery does not add or
reorder existing `tool_uses` approvals.

The parent node withdraws its obsolete direct `tool_uses` approvals for
`lem-weil-pbc-integral-stratified-perfect-characterization`,
`lem-weil-pbc-integral-coefficient-presentation-comparison`,
`lem-weil-proetale-countable-products-exact`,
`lem-pur-quotient-scalar-comparison-descent`,
`lem-weil-completed-scalar-chain-shift`, `lem-weil-completed-scalar-shift-descent`,
and `lem-pur-derived-change-of-rings`. Existing direct approvals for the
triangulated, constructibility-preservation and finite-free comparison results remain
in their original order. These withdrawals are only for the parent's new proof;
the relevant existing modules and declarations are preserved.

Validation: the complete three-module packet compiled through `lcompile.py --all`.
The delivery preflight supplies the final mechanical checks and review classification.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
