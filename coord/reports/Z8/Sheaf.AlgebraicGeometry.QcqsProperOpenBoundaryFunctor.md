## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.qcqs_proper_open_boundary_functor`
in `Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryFunctor`, with its entire statement
unchanged. Exact pullbacks use the existing instances and the underlying-functor
comparison obtained by whiskering `cartesianCoefficientPullbackIso` with forget.
The two underived adjunctions preserve coproducts in the specified universe;
`Functor.mapDerivedCategory_preservesCoproducts` passes this to derived categories.
The generator-preservation clause of
`qcOpenExtension_constantModelConstructible_finiteTor` and the defining intersection
prove transport of the localizing hull. The source hull is triangulated by checking
zero, shifts, and distinguished triangles in each defining replete triangulated
property. Existing triangulated-functor instances prove the composite clause.
Finally, apply `qcqs_proper_localizing_preservesCoproduct` to the family of open
extensions, transfer along `Discrete.compNatIsoDiscrete`, and compose preservation
instances. This uses canonical colimit preservation and covers the empty family.

Added the proof-only import `Sheaf.Paper.QcOpenExtensionConstantModelFiniteTor`.
Updated the existing node's proof, proof dependencies, and proof origin to record
the direct intersection argument. No public imports, definitions, signatures,
consumer modules, or target statements change; no change record is needed.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.ProEtale.CondensedRing.qcqs_proper_open_boundary_functor`
(node `lem-sfb-qcqs-proper-open-boundary-functor`).
Added 0 holes; split off 0 statements. There are 0 textual `sorry`s left in the
item and no additional Lean modules in the packet. Existing imported geometric
results may still depend on their own holes; this is a proof from those declared
inputs, not a claim that the full transitive closure is sorry-free.

Validation: complete item compiled through `lcompile.py`; final delivery performs
the required compilation and axiom checks. The import-direction check for the new
proof-only import reports no cycle. The unchanged hypotheses include `hc`, which
the argument does not need; `have _hc := hc` records its intentional nonuse.

## No longer needed

Removed proof-only imports:
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`;
- `WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian`;
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`.

The Grothendieck instances remain used transitively through the retained derived
coproduct interfaces; their nodes are retained. The separate resolution interface
is unnecessary as a direct import because the existing right-derived functor and
its triangulated instance suffice; the derived-category convention remains used.

Pruned dependency `det-proper-image-localizing-principle`, whose recorded module is
`Sheaf.CategoryTheory.Triangulated.LocalizingFunctor`: the required transport is
proved here from the intersection definition, Mathlib's triangulated inverse-image
instance, and the canonical colimit comparison. That module was already deleted;
this packet does not delete or restore any files. No other node or module is
claimed globally unnecessary. The unit route and all geometric inputs remain.

## Where the brief, the DAG or earlier work was wrong

The DAG's localizing-principle attachment names the deleted
`Sheaf.CategoryTheory.Triangulated.LocalizingFunctor`; its own attachment note
already records that deletion. A direct proof from the defining intersection
repairs the proof route without introducing a replacement hole or duplicate
public declaration. The source-hull triangulated structure also needed an
explicit intersection argument. No mathematical statement was changed.

Read the latest blueprint refinement proof (2), the unit realization record,
and all listed dependency statements and their Lean interfaces. The proof uses
no separation or disjointness relation between the images of the open and closed
immersions, no cohomological bounds, and no completeness hypothesis. Zero objects
and empty indexing families are included by the same categorical arguments.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
