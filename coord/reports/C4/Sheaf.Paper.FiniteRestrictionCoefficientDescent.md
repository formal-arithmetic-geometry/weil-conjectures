## What changed

Replaced the main finiteRestrictionCoefficientDescent hole with a complete assembly
from two strictly smaller steps: finiteRestrictionIntegralAssembly constructs only the
integral normalized geometry and arrows; finiteRestrictionRationalAssembly rationalizes
that normalized geometry and proves conditional exact-heart/direct-image descent.
The latter takes scalar-normalized endpoints, so it does not assume arbitrary natural
isomorphisms commute with shifts.

The item proves finiteData directly using finite upper bounds, actual stage quotient
representatives, the distinguished-triangle criterion, canonical transition/inclusion
comparisons, and associator naturality. It proves TExactDescent by mapping the finite-stage
representing isomorphism, finite fibres by finitePoints, and SectionsCompatible by
naturality of the actual sections-tensor/completion map and rational fibre comparison.
The two remaining steps have their complete source arguments in docstrings and nodes.
All four delivery modules compiled through lcompile.py --all; delivery checks repeat
that validation with warnings treated as errors.

Moved RationalComparisons, its two descended transformation definitions, SectionsCompatible,
and DirectImageDescent verbatim into FiniteRestrictionCoefficientDescentData and publicly
reexported that module. This prevents circular imports. No existing declaration name,
signature, visibility, defining term, or target meaning changes. The change record is
coord/changes/finite-restriction-coefficient-descent-data.md. Downstream checks found
no consumers beyond the item itself.

## Proved and sorry left

Closed the original syntactic hole in
WeilConjectures.FiniteRestrictionCoefficient.finiteRestrictionCoefficientDescent, using
two new intermediate holes. This is a decomposition, not a net proof: 0 of the original
1 hole fully proved; 1 hole replaced and 2 added. The only holes left in the packet are:

- WeilConjectures.FiniteRestrictionCoefficient.finiteRestrictionIntegralAssembly
  (lem-zl-finite-restriction-integral-assembly).
- WeilConjectures.FiniteRestrictionCoefficient.finiteRestrictionRationalAssembly
  (lem-zl-finite-restriction-rational-assembly).

There are no holes in definitions or private helpers. The item theorem itself is complete.

## No longer needed

No mathematical dependency is globally withdrawn. The original proof dependencies are
retained across the two new step nodes where needed. The item no longer directly needs
lem-zl-finite-completed-image-comparison, lem-pur-integral-operations-preserve-constructible,
lem-zl-finite-rational-heart-comparison, prop-weil-pbc-scalar-extension,
lem-pur-integral-operations-scalar-extension, lem-weil-finite-free-completed-scalar-comparison,
lem-pur-ordinary-adjunction-scalar-compatibility, prop-weil-pbc-rational-transport,
lem-sbc-coherent-pair-functor-descent, lem-per-adic-common-stage-truncations,
lem-a1-texact-pair-descent, and lem-weil-heart-short-exact-triangles: their work is now in
the integral/rational steps. The item proves finite data and preservation of halves
without additional truncation or t-exact pair-descent imports.

The four former public imports (FiniteRestrictionCoefficientCore,
FiniteRestrictionCoefficientNormalization, FiniteRestrictionCoefficientFiniteData,
FiniteRestrictionGeometricArrows) are now reexported through the data module; their
visibility and transitive mathematical dependencies are retained. No module is pruned.
The removed parent tool_uses entries are lem-pur-integral-operations-preserve-constructible,
prop-weil-pbc-scalar-extension, lem-pur-integral-operations-scalar-extension,
lem-weil-finite-free-completed-scalar-comparison,
lem-pur-ordinary-adjunction-scalar-compatibility, prop-weil-pbc-rational-transport,
lem-sbc-coherent-pair-functor-descent, lem-per-adic-common-stage-truncations, and
lem-weil-heart-short-exact-triangles. Their uses now lie in the new step nodes; approval
of those cross-unit tools is left to the maintainer. The remaining approval keeps its
original order; no approvals are added.

## Where the brief, the DAG or earlier work was wrong

The existing dependency statements provide general geometric comparisons and quotient
descent, but do not directly assemble the large normalized records in this item. The
remaining integral assembly and raw rational/heart passage are precisely those missing
glue steps. No false statement or target change is asserted.

Edge cases checked in the proof design: finite upper bounds include empty families;
finiteData uses no choice of a nonexistent arrow in an empty indexing type; every
equality has a transported witness; triangle representatives include all connecting
arrows through mapTriangle; point naturality applies to all morphisms, not only the
two specific restrictions. Integral assembly explicitly includes the empty fibre and
ramified extensions. Neither new statement adds geometric restrictions beyond those
already assumed by the parent.

## New nodes

- def-zl-finite-restriction-coefficient-descent-data records the relocated existing
  rational comparison and descent interfaces, with their unchanged definitions.
- lem-zl-finite-restriction-integral-assembly is the integral construction and
  normalization portion (steps 1--4), with the actual geometric arrow comparisons.
- lem-zl-finite-restriction-rational-assembly is raw rational transport, common-stage
  functor descent, and conditional exact-heart passage (steps 5, 6, 8).

Blueprint searches for finite restriction, coefficient descent, and rational comparisons
found no duplicate imported blueprint node.

Mathlib searches used leanfinder (directed functor descent and t-exactness), loogle
(StageSystem), leansearch (finite diagrams and triangles), and grep
(coefficient descent/scalar counits). No Mathlib result assembles these prescribed
geometric coefficient records. Existing project StageSystem APIs are reused directly.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
