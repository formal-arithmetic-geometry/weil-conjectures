## What changed

Filled the five proof bodies in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`.
The public signatures, attributes, imports and existing definition bodies are preserved.
Proved private helpers handle shifted Hom continuity and exact-derived comparisons.
Private `import all` declarations reuse proved factorization and degree-zero model
helpers in `Sheaf.Paper.CondensedFiniteModelProofAPI` and the isomorphism/shift continuity
helpers in `Sheaf.CategoryTheory.HomColimitExtension`. Local instance priorities select the existing canonical
module and sheaf structures, and local opacity controls preserve sharing of those structures.
There is no definition or statement repair and no consumer requires adaptation.
The local proof context and complete consumer inventory are recorded in
`coord/changes/c2-two-colimit-proof-scope.md`, as required by server preflight.
Private proof imports supply the already stated preservation, coefficient faithfulness,
coefficient-complex presentation, sheaf continuity, finite-model and devissage APIs.

The scalar-preservation clauses specialize the generic exact scalar-extension theorem.
Hom injectivity uses ambient derived faithfulness and takes the later field to be the
original field. Hom surjectivity uses the canonical coefficient-complex presentation
and the finite extension/restriction adjunctions. Object descent uses the triangulated
union of finite essential images and bounded cohomological devissage.

## Proved and sorry left

Five original holes closed, zero holes added, zero split off:

- `AlgebraicGeometry.ProEtale.boundedConstructible_derivedExtendScalarsSubfield_obj`
  (`lem-sfb-extend-subfield-constructible`).
- `AlgebraicGeometry.ProEtale.boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj`
  (`lem-sfb-extend-to-qlbar-constructible`).
- `AlgebraicGeometry.ProEtale.constructibleCocone_essSurjObj`
  (`lem-sfb-constructible-cocone-obj`).
- `AlgebraicGeometry.ProEtale.constructibleCocone_homSurj`
  (`lem-sfb-constructible-cocone-hom-surj`).
- `AlgebraicGeometry.ProEtale.constructibleCocone_homInj`
  (`lem-sfb-constructible-cocone-hom-inj`).

No sorry remains in the delivered module. Its named dependencies retain their own
independent proof obligations; this packet adds none.

Validation: the resumed session compiled the complete current module without errors or
warnings through `lcompile.py` in 52.8 seconds. It repaired the private ambient
Hom-surjectivity transfer by exposing the associator identity components and the full
subcategory lift before applying the category identity laws. The added proof instances
are local to the file or the object-descent proof; an earlier server preflight required
the proof-scope change record above.
All five original holes are closed and no holes are added or split off.
The preserved public-import list and existing non-theorem declaration blocks were
checked against the shared source. All delivery Lean lines have at most 100 characters.

## No longer needed

No existing public import or source declaration was removed. No module is withdrawn.
All declared proof dependencies remain needed. No node or module becomes globally unused.
No proof import is removed. Reusing the existing private finite-model proof API avoids
duplicating its factorization and degree-zero constructibility lemmas; the existing
Hom-continuity API also replaces duplicate isomorphism and shift lemmas.

## Where the brief, the DAG or earlier work was wrong

The private support module
`Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`
contains relevant proved helper arguments but imports the item itself. It cannot be
imported back here. The needed comparison arguments are proved privately in the item; factorization and
degree-zero constructibility use the earlier finite-model proof API below it. No new public interface is introduced.

The Mathlib searches (LeanFinder, Loogle and grep, run through msearch.py) found generic
faithful-functor injectivity and unrelated filtered algebraic-geometry results, rather
than a replacement for the coefficient-descent proof. The proof retains the unit's
finite-coefficient extension, morphism descent and Postnikov devissage route.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
