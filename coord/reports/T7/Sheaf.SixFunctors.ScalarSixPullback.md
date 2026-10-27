## What changed

`scalarSixPullback` is assembled from normalized geometry, the canonical derived pullback
comparison, uniqueness of the ordinary open comparison, and the locally closed comparison.
The original interfaces move to `ScalarSixDefinitions`, publicly re-exported by the original
module. The first 27 declarations retain their types and values; four aliases become abbreviations,
and the three transport formulas specialize generic equivalence-cancellation definitions.
The extension proposition is repackaged
as nonemptiness of a structure with exactly its former witnesses and equations. Its
single-arrow fields form a nested structure; the assembly proves the closed and tower
fields. The proof clauses retain their exact formulas in named propositions, keeping constructor
and projection types compact. This avoids repeated checking of dependent existential predicates.
No target statement changes. The independent statement review must verify the correspondence
in `coord/changes/T7-scalar-six-interface-location.md`. Unused generated constructor and size
helpers are suppressed; the consumer search found no users of those helpers.

Geometry is constructed from the unique cartesian coefficient isomorphism, explicit identity
maps on sections, and adjunction conjugation. The non-flat pullback comparison is the existing
free-parameter scalar comparison by its component mate formula. Its geometric and coefficient
composition laws are proved by exact derived square composition and mate pasting. The ordinary
open comparison is constructed by uniqueness of adjoints. The immersion assembly proves the
closed witness by conjugation and proves the beta tower equation by restricting to supported
objects and using full faithfulness. All new proof imports are private.

Validation: the final dependency-ordered check of all seven packet modules completed
with exit code 0 (`scratchpad/packet-named-clauses.log`). This includes the repaired
interface, geometry, derived theta and both coherence equations, ordinary open comparison,
immersion assembly and the original top-level theorem. The original theorem signature was
also checked byte for byte against the shared source. The required delivery command runs
its own compile and preflight checks before pushing.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.ProEtale.CondensedRing.scalarSixPullback`.

Proved new public declarations:

- `scalarSixGeometry_exists` (normalized coefficient and geometric comparisons);
- `scalarSixPullbackData_exists` (canonical non-flat theta, geometric composition and tower);
- `scalarSixOpenComparison_exists` (ordinary open mate comparison);
- `scalarSixExtensionData_exists` (closed witness and beta tower from the normalized
  single-arrow construction).

Added hole: `scalarSixNormalizedImmersion_exists`, node
`lem-sfb-scalar-six-normalized-immersion`. It isolates the single-coefficient-arrow transport
of the existing normalized open/closed immersion construction to the fixed internal-module
presentation, including geometric composition and the prescribed open value. It does not
assert geometry, canonical theta invertibility, theta coherence, the closed witness, or the
beta tower square. Its source and complete proof in words are in the theorem docstring and
node. It is the sole named theorem left with `sorry` in the packet; there is no hollow data.
The packet is a decomposition: one original hole closed, one strictly smaller hole added,
net zero holes before accounting for newly reached existing dependency modules. The proof
uses the pre-existing `scalarPullComparison_isIso` declaration, whose own proof remains
another item's responsibility; it is not counted as newly proved here.

The empty scheme, identity immersion, open/closed overlap, zero coefficient ring and non-flat
coefficient maps impose no additional hypotheses on the new statements. Normalization
uniquely determines the immersion comparison by the supported Hom bijection. No arbitrary
witness of a mere existence theorem is used to define data.

## No longer needed

The 13 former private imports are removed from the interface module. Proof modules import
the declarations their proofs use explicitly; the interface keeps its four public
imports and a private operations-transport import for its two proved additive instances. The removed direct imports are KFlatResolutionIndependentCoefficients,
ProEtaleConstantRingOperations, ProEtaleModuleObjects, ProEtaleRingedOpenClosed,
RightDerivedFunctorOfQuasiIsoResolutions, KFlatRingedToposPullback,
ProfinitePointPullback, DerivedExtendScalars, ExtendScalars, UpperLowerStar.Monoidal,
ModuleObject.Basic, ModuleObject.Derived.BoundedConstructible and
ModuleObject.LowerShriek.Defs. This removes direct imports, without claiming that their
entire modules leave the targets' import closure.

The four former public imports remain re-exported through `ScalarSixDefinitions`.
The top-level proof does not directly use its former detailed K-flat, scalar-tower,
Noetherianity or open/closed prerequisites: the new nodes record where those are still
needed. In particular the direct proof of theta composition and its tower square uses
`new-comap-upper-star-iso-composition`, `new-comap-upper-star-iso-mate`, and
`lem-pod-derived-exact-square-composition`, rather than
`lem-sfb-scalar-inverse-image-tower-diagram` or a fresh K-flat resolution argument.
The full-faithfulness argument also uses additivity from internal-module operations transport.
The single-arrow immersion lemma still cites the normalized section-scalar transport,
open/closed calculus and normalized immersion coherence. No source declaration is removed,
no module is withdrawn, and no whole-library pruning count is claimed. The scalar-six unit's
pullback, extension and coefficient-tower assertions all remain.

The old top-level `tool_uses` approvals are withdrawn because the assembly now cites
its explicit comparison nodes. The removed entries are:

- `lem-sfb-alpha-iso`;
- `lem-sfb-finite-upper-star-tensor`;
- `lem-pc-kflat-resolution`;
- `lem-weil-pbc-ringed-pullback-preserves-kflat`;
- `lem-weil-pbc-profinite-point-pullback`;
- `lem-weil-pbc-proetale-ringed-open-closed`;
- `lem-sfb-internal-module-operations-transport`;
- `lem-sfb-successive-derived-quotient-normalization`;

The corresponding mathematical inputs still needed below the assembly are recorded in
the new nodes' proof dependencies and tool-use explanations. The old direct proof edges
are replaced by these new comparison nodes. In particular no direct edge remains to the
old K-flat-resolution, pullback-preserves-K-flat, localization-universal-property,
profinite-point-pullback, successive-derived-quotient-normalization or
scalar-inverse-image-tower-diagram nodes. This is removal of direct planned work from
this proof, not withdrawal of any existing declaration or module.

## Where the brief, the DAG or earlier work was wrong

No target or mathematical statement was found false. The advertised short assembly also
requires concrete internal/section presentation transport, canonical map identifications,
and the exact coefficient-composition equations. The new proof records this glue explicitly.
The ordinary open comparison needs only uniqueness of adjoints, so its construction does
not need K-flat computations. The beta tower follows from normalized restriction and
supported faithfulness once C.tower is known; it needs no further resolution theorem.

A read-only dependency audit also encountered an existing cycle outside this packet:
`lemma-weil-pbc-derived-exchange-replacement` →
`lem-weil-pbc-derived-exchange-termwise` →
`lem-weil-pbc-derived-exchange-unbounded-transport` →
`lem-weil-pbc-derived-exchange-bounded-comparison` →
`lemma-weil-pbc-derived-exchange-replacement`. No packet node belongs to that cycle, and
this delivery changes none of those records. The maintainer should reconcile that
existing graph issue independently.

## New nodes

`lem-sfb-scalar-six-geometry`: explicit normalized geometry, proved from the existing
cartesian coefficient theorem, identity section maps and adjunction conjugation.

`lem-sfb-scalar-six-derived-pullback-normalization`: canonical non-flat scalar mate,
its invertibility, and both coherence equations. This uses existing named prerequisites
and formal mate calculations.

`lem-sfb-scalar-six-open-comparison`: uniqueness-of-adjoints construction of the ordinary
open comparison with its exact mate normalization.

`lem-sfb-scalar-six-normalized-immersion`: the remaining single-arrow normalized immersion
transport and geometric compositor. This is strictly part of clause (2), without clause (1)
or either coefficient-tower equation; its source proof is the normalized open/closed
assembly, and its node records the existing prerequisites still needed.

`lem-sfb-scalar-six-immersion-comparison`: the proved closed witness and beta tower assembly
from the single-arrow normalization. Private generic helpers prove faithfulness under
restriction on supported objects and the natural-transformation tower calculation.

The existing interface node's Lean attachment follows the definitions and their equivalent
structured representation to
`ScalarSixDefinitions`; see `coord/changes/T7-scalar-six-interface-location.md`.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
