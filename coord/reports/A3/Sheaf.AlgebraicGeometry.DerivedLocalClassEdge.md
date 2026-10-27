## What changed

`Sheaf.AlgebraicGeometry.DerivedLocalClassEdge` now supplies an explicit witness and
combines its local equation, proved naturality, and single-complex properties. Its
statement and its public import are unchanged.

`Sheaf.CategoryTheory.LeftExactHomologyEdge` constructs the general homology edge of
an additive functor preserving finite limits, using preservation of the kernel of
the outgoing differential and the cokernel of the incoming boundary. It proves the
cycle formula and naturality, without assuming preservation of cokernels.

`Sheaf.AlgebraicGeometry.DerivedLocalClassEdgeMap` transports that actual map through
the fixed K-injective representative and proves naturality in arbitrary derived
morphisms. No object is chosen from an unproved existence theorem.

`Sheaf.AlgebraicGeometry.DerivedSingleDirectImageUnitIso` proves invertibility of Hq
of the single direct-image comparison: use the existing degree-zero unit theorem,
then the canonical unit's shift compatibility and the single/homology shift isos.

`Sheaf.AlgebraicGeometry.DerivedResolutionEdgeSingle` proves the normalization of the
constructed edge. First a calculation with a lifted map into the fixed resolution
cancels the derived unit on every complex; the kernel and cokernel maps on a single
then give the required equation.

`Sheaf.AlgebraicGeometry.DerivedResolutionEdgeLocal` isolates the remaining equation
between this *specified* edge and the fixed local-class maps. It asserts neither the
existence of an edge nor naturality nor either single-complex property. Its docstring
and node describe the representative comparison, the cycle calculation for exact
abelian sheafification, and transport by the fixed normalizations.

All added imports of the item's proof are private proof imports. All new Lean files
use `module`, explicit parameters, and at most 100 characters per line. No existing
module other than the assigned item, existing definition, statement or instance has
been changed. There are no forced adaptations or change records.

Validation: the full sandbox compiled through `lcompile.py --all`, with no warnings.
Per-file times were 0.0 s, 1.4 s, 1.5 s, 44.9 s, 5.6 s and 7.4 s; every file is below
60 s. JSON parsing, referenced-node existence, line widths and the exact single-hole
count were also checked. The delivery tool performs the independent server preflight.

## Proved and sorry left

Closed in the assigned module: `AlgebraicGeometry.exists_topEdgeLocalClassEdge` (one
original hole), by construction and combination of the displayed clauses.

Added one hole: `AlgebraicGeometry.resolutionLocalClassEdge_local`, node
`lem-weil-pbc-resolution-local-class-edge-local`. This is the sole `sorry` in the
packet. Thus this delivery is a decomposition, with one hole closed, one added and
net zero holes closed; it is not a claim to a sorry-free proof of the original result.

Fully proved with no new holes: `CategoryTheory.ShortComplex.leftExactHomologyEdge`
and its cycle and naturality API; `AlgebraicGeometry.resolutionLocalClassEdge_naturality`;
`AlgebraicGeometry.topEdgeSingleDirectImageMap_isIso_homology`;
`AlgebraicGeometry.resolutionLocalClassEdge_single` and their private proof helpers.
All data definitions have complete bodies and all their necessary proof fields are
proved. The remaining lemma is strictly a part of the original argument: it identifies
a separately constructed map, after the naturality and single clauses have been
proved independently. It is not a renamed existential package.

The arguments cover all integer q, including negative degrees, zero coefficients,
and empty schemes or opens: the construction uses kernel/cokernel universal properties,
and the single invertibility proof uses integer shifts rather than a positivity premise.

## No longer needed

The assigned module retains its original public import and adds only the proof
modules it uses; no pre-existing public import is removed. No module is withdrawn.

The original proof dependency `def-weil-presheaf-modules-sheafification` and its
module `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` are not needed as
a direct step in this construction. The edge is constructed in sheaves of modules
using kernels and cokernels, rather than by first constructing and sheafifying a
module presheaf map. The remaining local comparison uses the already fixed *abelian*
sheafification comparisons. This does not claim that the module is unused elsewhere
or that its existing declarations may be removed.

The original unbounded section-presheaf comparison, cohomology/sheafification
normalization, derived direct image, and integer single comparison remain needed,
now through the new nodes. The fixed blueprint unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or incompatible signature was found. The planned bounded-below
resolution is unnecessary for the single-complex isomorphism: the already proved
zero-degree unit theorem and shift compatibility prove it in every integer degree.
Naturality is proved directly on fixed K-injective representatives by lifting derived
maps; it does not require uniqueness of module-presheaf sheafification.

The local comparison is still genuine work. The original node does not separately
state the compatibility of the explicit kernel/cokernel edge with its chosen local
Leray and abelian sheafification comparisons. That equation is the one remaining
named obligation; the node and docstring give its complete cycle-level proof plan.

## New nodes

`def-weil-pbc-left-exact-homology-edge`: the constructed left exact homology edge and
its proved cycle and naturality API, in `Sheaf.CategoryTheory.LeftExactHomologyEdge`.

`def-weil-pbc-resolution-local-class-edge`: the fixed-resolution module edge and
proved derived naturality, in `Sheaf.AlgebraicGeometry.DerivedLocalClassEdgeMap`.

`lem-weil-pbc-integer-single-direct-image-unit-iso`: the proved integer-degree single
isomorphism, in `Sheaf.AlgebraicGeometry.DerivedSingleDirectImageUnitIso`.

`lem-weil-pbc-resolution-local-class-edge-single`: the proved normalization on singles,
in `Sheaf.AlgebraicGeometry.DerivedResolutionEdgeSingle`.

`lem-weil-pbc-resolution-local-class-edge-local`: the sole remaining local equation,
in `Sheaf.AlgebraicGeometry.DerivedResolutionEdgeLocal`.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
