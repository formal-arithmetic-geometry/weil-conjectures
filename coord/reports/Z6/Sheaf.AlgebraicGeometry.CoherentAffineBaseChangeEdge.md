## What changed

Constructed the normalized top projection from the local upper bound, the
simultaneous sheaf isomorphisms beta from gamma and the assumed base-change
isomorphisms, and the affine linear equivalences from the specified Leray edge.
The upper bound uses exact open restriction and the given splitting. Affine
qcqs higher-direct-image vanishing makes the Leray edge invertible; naturality
at scalar endomorphisms proves its linearity.

The compatibility proof combines normalized tensor horizontal pasting,
naturality and composition of the top-cohomology comparison, the Leray square
identity, naturality of section pullback, and cancellation of beta. Tensor
pasting is proved in this packet. The global-class Leray square is a separate,
more general remaining theorem.

The original theorem header is verbatim unchanged. All twelve existing maps
have definitionally equal types and the same values. Six maps now abbreviate
shared explicit constructions: the derived image, single-module base change,
Leray edge, scalar-restricted cohomology module, cohomology pullback, and section
pullback. No data is supplied by an arbitrary unproved existence statement.
The Leray edge's cocycle formula determines its value on every class.

Three shared local instances expose the existing native category, additive and
abelian structures before the derived-category family is bound. Eight supporting
local instances expose existing scalar, injective and slice-site sheafification
structures in the item. The two slice-site caches use Mathlib’s existing
constructions for arbitrary topological spaces; the general fallback adjoint
instance is disabled only while elaborating the final theorem.
The scalar caches use direct native `ModuleCat` projections, avoiding an
auxiliary reconstructed scalar-action record. These change no group, scalar
action, or category. The original Mathlib homology
functor is used directly. The selected classical Leray transformation has a
named definition and a proved vanishing API; its cocycle formula determines
it on every class. The linearity calculation is proved for an arbitrary natural
transformation before specializing to this edge.

Private interfaces expose the specified second mate, its projection equations
and its pasting law. Tensor pasting uses the existing named composition
isomorphism, a generic single-complex counit calculation and a named fixed
counit. These retain the same pinned maps while avoiding repeated reduction
of their selection formulas. The beta factory chooses from proved unique existence. Linear equivalences
use a generic proved bijective-linear-map constructor and its evaluation API;
normalization equations determine both constructions up to equality.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.coherent_affine_base_change_edge_naturality`.
The item contains zero `sorry`s.

Added and proved:
`AlgebraicGeometry.tensorSingleBaseChange_pasting`, with zero `sorry`s.
Its private helpers prove the single-complex composition formula, the
normalized tensor compositor equation, composition of the pinned counits,
pasting using the existing coefficient-naturality theorem.

The sole added hole is
`AlgebraicGeometry.topDegreeLeray_commutativeSquare`, in its own module and node.
It is exactly the global-class comparison step. Its docstring and node contain
the source and full resolution-roof proof. It assumes the top upper bound but
neither cartesianness nor invertible base change, and asserts no simultaneous
beta/e family or composition law. This is a decomposition: one original hole
closed and one new hole added, net zero before import-closure pruning.

All three modules compile, including the complete parent proof. The final
delivery reruns the compiler and consumer checks.

## No longer needed

Removed proof imports from the item:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`;
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`;
- `WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`;
- `Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComposition`;
- `WeilConjectures.AlgebraicGeometry.DerivedBaseChangeHorizontalPasting`;
- `WeilConjectures.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses`;
- `Sheaf.Paper.HigherDirectImagePresheaf`.

Horizontal pasting, coefficient naturality and canonical single-pullback
composition remain transitive dependencies where used. No library module or
declaration is withdrawn.

The item's direct proof-dependency list drops
`def-pc-flat-sheaf-modules`, `lem-pc-bounded-above-flat-kflat`,
`lem-pc-derived-pullback-open-restriction-universes`,
`def-pc-derived-module-base-change-map`, `def-pc-derived-pullback`,
`def-sc-finite-locally-free-sheaf`, `lem-pc-affine-vanishing`,
`lem-pc-canonical-single-pullback-composition`,
`lem-pc-derived-base-change-horizontal-pasting`,
`lem-pc-ringed-spaces-derived-pullback-composition`,
`lem-weil-pbc-higher-direct-image-presheaf`,
`lem-weil-pbc-top-base-change-presheaf`, and `pqf-def-coherent`.
These are direct-dependency removals, not claims that every such node leaves the
whole target closure. Needed ones remain through statements or the new lemmas.

The source-square skeleton imports only what its statement/constructions use.
`DerivedSquareUnitMap`, `DerivedSquareLocalClasses`,
`ModuleCohomologyFMapFunctorial`, and `DerivedAdjunctionTopEdge` remain recorded
mathematical dependencies of its proof plan, with unused proof imports removed. `TopBaseChangePresheaf` is unnecessary for this arbitrary-square
route. Original tool approvals are retained.

## Where the brief, the DAG or earlier work was wrong

The stated top-base-change-presheaf theorem uses the reversed chosen fiber
product, restricted opens/resolutions and the classical higher-image adjunct.
It does not directly give Step 6's whole-open identity for an arbitrary square
and the specified coefficient isomorphism. Existing `DerivedSquareLocalClasses`
already supplies the arbitrary-square local equation. The separate Leray-square
node records its remaining whole-open normalization and coefficient transport.

The old local K-flat calculation is stronger than needed. The local splitting
provides the upper bound, while ordinary qcqs quasi-coherent higher images give
affine Leray vanishing. Finite local freeness is unused in this shorter proof;
all original hypotheses are retained. Nodes follow the actual proof route.

A dependency audit encountered the existing external cycle
`lem-sp-grothendieck-edge-maps` → `thm-sp-grothendieck` →
`lem-sp-ce-acyclic-abutment` → `lem-sp-ce-second-image-truncation` →
`lem-sp-ce-decalage-truncation-diagram` →
`lem-pc-grothendieck-resolution-unit-comparison` →
`lem-sp-grothendieck-edge-maps`. Those records are unchanged. The packet's
return-path audit found no cycle through either new node or the modified item.

## New nodes

`lem-weil-pbc-tensor-single-base-change-pasting` realizes Step 4's normalized
single-module pasting identity, using arbitrary composable squares and the
specified outer-projection equality. Source: Stacks cohomology Tags 0ATM and
08HY. Its full proof is included. Identity arrows, zero modules, empty schemes
and noncartesian squares require no added hypothesis.

`lem-weil-pbc-top-degree-leray-square` realizes Step 6 for arbitrary coefficient
morphisms. Source: Stacks Tags 01E4, 01FB and 08HY, using the existing top-edge
adjunction interface. Only the source upper bound is assumed; no mate or
local-class map is inverted. Empty schemes and zero coefficients give zero
maps; identity squares recover coefficient naturality. Its supporting constructions are actual existing maps/modules and native
structures. The classical edge and its vanishing API have no admissions; the
only admitted declaration in that module is the square theorem.

Change records:
`coord/changes/Z6-coherentEdgeK-shared-construction.md`,
`coord/changes/Z6-coherentEdgeDelta-shared-construction.md`,
`coord/changes/Z6-coherentEdgeEpsilon-shared-construction.md`,
`coord/changes/Z6-coherentEdgeH-shared-construction.md`,
`coord/changes/Z6-coherentEdgePullback-shared-construction.md`, and
`coord/changes/Z6-coherentEdgeSectionPullback-shared-construction.md`.
Each records the old/new construction and consumer audit. There are zero Lean
importers downstream of the item, and no forced adaptation of another group's
module or source-library edit.

Local transparency attributes expose the same canonical structures for the
proof. Imported reducibility attributes are changed only locally. The scoped
`allowUnsafeReducibility` option changes these local transparency settings;
it introduces no unsafe declaration or trusted axiom.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
