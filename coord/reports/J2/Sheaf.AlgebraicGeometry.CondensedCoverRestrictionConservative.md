## What changed

Proved `AlgebraicGeometry.ProEtale.condensed_cover_restriction_conservative` in
`Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative`, keeping its full signature
unchanged. The proof first reflects module-sheaf isomorphisms by forgetting the action,
transporting scalar extension along the coefficient isomorphism to restriction of scalars,
and applying the existing arbitrary-cover localization conservativity theorem. It then
applies the natural exact-functor homology comparison and `DerivedCategory.isIso_iff`.
Zero-object detection follows by applying this result to `K ⟶ 0`.

Added the proof-only import
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative`.
Updated the existing node's proof, proof dependencies and proof origin to describe this
reuse of established infrastructure. No definitions or theorem signatures changed.
The public-import cleanup and local zero-object scope are recorded in
`coord/changes/J2-condensed-cover-conservativity-imports.md`, with every downstream user.
The unit's realized statement and steps are unchanged. The existing sandbox proof was
retained and repaired against current sources: the weak-etaleness API and zero-object scope
had changed, and the forgetful-map instance needed an explicit type.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.ProEtale.condensed_cover_restriction_conservative`
(node `lem-zl-condensed-cover-restriction-conservative`).
Zero holes remain in the item; zero holes were added and no results were split off.
The proof passed the resumed delivery dry run and compiles through `lcompile.py`
(28.6 seconds with profiling). Both unchanged direct consumers,
`CondensedLisseProEtaleLocality` and `MateOpenRestriction`, compile against it in
15.0 and 30.7 seconds respectively. Its earlier `#print axioms` result is
exactly `propext`, `Classical.choice`, and `Quot.sound`: the theorem has no transitive holes.
Profiler options and axiom-printing commands are absent from the delivered file.
An initial consumer-set compile timed out on this same item; the profiled check then
compiled the whole set within the per-file limit, with no slow proof step identified.
The empty-cover and zero-coefficient cases require no additional hypotheses.

## No longer needed

Removed public imports (none is needed to state this theorem):

- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`

Removed proof imports:

- `Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties`
- `Mathlib.CategoryTheory.Sites.LocalProperties`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`

The last three APIs are already exposed by the retained derived-module import.
The separate proof obligations `lem-weil-proetale-weakly-etale-localization`,
`lem-sfb-proetale-object-inverse-image-restriction`, `det-pe-topos-functoriality-site`,
and `lem-sfb-sheaf-cover-local-isomorphism` are not used by this proof: the published
localization comparison and arbitrary-cover sheaf conservativity already supply their
needed consequences. Removed the two now-unused top-level tool approvals for
`lem-sfb-proetale-object-inverse-image-restriction` and `det-pe-topos-functoriality-site`.
This is pruning from this proof, not a claim that other consumers no longer need them;
statement dependencies have not been changed.

## Where the brief, the DAG or earlier work was wrong

The planned reconstruction of localization, covering sieves, linear inverses and derived
naturality duplicates infrastructure already proved in the source library. The retained
proof uses those existing declarations directly and adds no substitute assumptions.
The resumed dry run required an import-interface change record; it is now included,
with the unchanged signatures and the downstream audit.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
