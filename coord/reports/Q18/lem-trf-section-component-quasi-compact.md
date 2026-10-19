## Worker report

The item is already stated by the published declaration
`AlgebraicGeometry.isCompact_setOf_mem_connectedComponentIn_preimage_singleton` in
`WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat`.  I therefore added no Lean module
and changed only the node's `lean` record to an `existing: true` record.

The declaration signature is:

```
theorem isCompact_setOf_mem_connectedComponentIn_preimage_singleton {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f] [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) :
    IsCompact {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (σ (f x))}
```

This renders the node clause by clause.  The schemes `P,T` are `X,Y`, and `g` is `f`.
The section hypothesis is exactly `σ ≫ f = 𝟙 Y`.  The set in the conclusion is the union,
over fibres, of the connected components containing the section, so `IsCompact` is the
node's quasi-compactness conclusion.  The published theorem has the stronger interface
needed to express compactness: `[CompactSpace X]`, `[QuasiSeparatedSpace X]`,
`[CompactSpace Y]`, and `[QuasiSeparatedSpace Y]`, together with
`[LocallyOfFinitePresentation f]` and `[QuasiCompact f]`.  The node's finite-presentation
and quasi-compact/quasi-separated assumptions over the affine base provide these standard
instances; its flatness and geometrically reduced-fibre assumptions are retained by the
node but are unnecessary for this stronger existing theorem.  Affineness of `T` supplies
compactness and quasi-separatedness of the base.  No fibre is excluded: empty fibres have
empty connected-component loci, and the section makes the component nonempty whenever the
base has a point.

Dependency declarations read and used in checking the match:

- `AlgebraicGeometry.Flat` (Mathlib, `Mathlib.AlgebraicGeometry.Morphisms.Flat`), the
  recorded flat-morphism notion;
- `AlgebraicGeometry.LocallyOfFinitePresentation` (Mathlib,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`);
- `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` (Mathlib,
  `Mathlib.AlgebraicGeometry.Scheme`);
- `AlgebraicGeometry.GeometricallyIrreducible`/`GeometricallyReduced` (Mathlib,
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` and its imported reduced/irreducible
  declarations);
- `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map` (Mathlib,
  `Mathlib.AlgebraicGeometry.Scheme`);
- `ConnectedSpace` (Mathlib, `Mathlib.Topology.Connected.Basic`), the connected-space
  interpretation of the recorded connected-scheme node;
- `CompactSpace` (Mathlib, `Mathlib.Topology.Defs.Filter`), the recorded quasi-compact
  scheme notion.

Searches performed:

- `msearch.py ... leanfinder "relative connected component of a section quasi-compact"`:
  no exact relative-component theorem was returned (only general compactness/quasi-compactness
  declarations).
- `msearch.py ... loogle "isCompact connectedComponentIn"`: no hits (unknown identifier in
  the service).
- `msearch.py ... grep "isCompact_setOf_mem_connectedComponentIn_preimage_singleton"`:
  found the exact theorem and its module in `WeilConjectures/AlgebraicGeometry/Morphisms/SlicingFlat.lean`.
- `rg` over `WeilConjectures` and project `lean/Sheaf`: no duplicate project declaration;
  the only exact declaration is the published upstream theorem.
- `scompile.py --source WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat`:
  printed the source module and the full theorem signature/docstring.

No statement correction, disputed statement, new node, or dependency module is needed.

## Second reading by Q18

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
