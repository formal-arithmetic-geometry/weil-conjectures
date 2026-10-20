## What changed

Completed the proof of `AlgebraicGeometry.Scheme.inverseImage_tensor_hom_iso` from
normalized tensor, internal-Hom and scalar-extension comparisons, positive tensor-power
induction, and the existing limit-preservation theorem for pro-etale immersions.
The original theorem signature is unchanged.

The five existing section and tensor-power definitions are moved verbatim into
`Sheaf.Paper.PurInverseImageTensorHomDefinitions`, publicly reexported by the original
module. Three new comparison modules prove the separate tensor, Hom and scalar results.
The Hom proof constructs reindexing on slice categories and restriction of scalars along
an invertible ring unit, then takes the canonical adjunction mate. Its naturality and
section formula are proved generically before specialization to schemes, avoiding
repeated unfolding of the large inverse-image construction. Private constructions have
explicit morphism APIs and local irreducibility boundaries. No definition contains a hole.

Validation: all five modules compile together without warnings. The Hom module compiles
in 16.4 seconds and the assembled theorem in 6.3 seconds in the final set check.
Unchanged copies of `PurityFiniteKummerLevel`, `TateInverseLimitBaseChange`, and
`TateTwistLocallyFree` compile against that overlay in 6.8, 4.4, and 8.5 seconds.
The original theorem signature was compared verbatim against the current shared source.
The final Hom API uses pointwise evaluation to avoid converting whole presheaf morphisms.
A later delivery recompile hit the time limit in the main module; caching its two
sheafification instances gives a clean 12.7-second check. The assembly proof is unchanged.

## Proved and sorry left

The original module has one hole:
`AlgebraicGeometry.Scheme.inverseImage_tensor_hom_iso`.
The delivery replaces it by a complete proof. The following new public theorems also
have complete proofs: `AlgebraicGeometry.Scheme.purInverseImageTensorComparison`,
`AlgebraicGeometry.Scheme.purInverseImageHomComparison`, and
`AlgebraicGeometry.Scheme.purInverseImageScalarComparison`.
All private helpers are proved. Holes closed: 1 of 1. Holes added: 0.
Sorries remaining in the five delivered modules: 0. No unfinished statement is split off.
The proof uses existing declared dependencies, whose own proofs are outside this item.

## No longer needed

The parent no longer directly uses `def-weil-sheaf-of-modules-category`,
`lem-weil-pbc-site-sheafification-iso-locally-bijective`, or
`lem-pc-sheaf-modules-tensor-closed`. Tensor normalization comes from the existing
pro-etale tensor comparison; Hom is constructed explicitly using slice equivalences.
The top-level `tool_uses` entry for `lem-pc-sheaf-modules-tensor-closed` is removed.

Removed direct proof imports from the item:
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`,
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`,
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
`Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage`,
`Sheaf.CategoryTheory.RingedSiteModules`,
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
`Mathlib.CategoryTheory.Sites.LocallyBijective`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`, and
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`.
The Hom comparison module supplies InternalHom and the site-isomorphism theorem where
needed. The former public imports of ProEtaleInverseImage, Scheme, Iso and
TensorProductOfUniverses are supplied transitively by the shared definitions module.
These are direct-dependency changes; no entire library module is claimed withdrawn.

## Where the brief, the DAG or earlier work was wrong

The baseline is one hole, not the six reported in an earlier draft: the other holes
were temporary private helpers during proof development. The retained report also
claimed compilation before the full Hom proof had been restored and checked; this report
replaces that claim with the final validation evidence. No statement is disputed.

The existing unit route is retained. The scalar argument needs no flatness, and the Hom
argument needs no finite-presentation hypothesis: it uses an equivalence of slice sites,
not Tag 0GN2's general pullback-Hom criterion. The empty site and zero ring do not require
exceptions. The tensor-power induction treats zero by contradiction and one by identity.

## New nodes

`def-pur-inverse-image-tensor-hom-sections`: the five original definitions, relocated
verbatim into a common module. Change record:
`coord/changes/pur-inverse-image-definitions-location.md`.

`lem-pur-inverse-image-tensor-comparison`: specialization of the existing pro-etale
tensor comparison, with unit-section normalization and first-variable naturality.

`lem-pur-inverse-image-hom-comparison`: explicit Hom reindexing and scalar restriction,
followed by the canonical adjunction mate, with section normalization and naturality.

`lem-pur-inverse-image-scalar-comparison`: uniqueness of composite left adjoints and
pure scalar normalization. All three comparison nodes are fully proved in this delivery.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
