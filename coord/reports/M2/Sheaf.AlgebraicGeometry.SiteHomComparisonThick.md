## What changed

Proved the canonical restriction assertion `AlgebraicGeometry.ProEtale.siteHomComparison_restriction` without changing its statement. The canonical derived monoidal structure is shared through an irreducible helper with the same body, avoiding repeated kernel unfolding. Added two fully proved generic modules: `Sheaf.Algebra.Homology.ExactClosedDerivedHom` proves that an exact ordinary closed strong monoidal functor with an exact left adjoint preserves native unbounded derived internal Hom; `Sheaf.CategoryTheory.DerivedCategory.ExactDerivedTensorSquare` proves monoidality of the canonical exact derived square. Private helpers identify the prescribed tensor structures using their tensor components. The restriction equation is the naturality/composition square for the actual evaluation transpose.

The two restriction evaluation definitions also share the identical canonical comparison component through `Functor.closedComparison`. All existing public imports and theorem signatures are preserved. The item publicly imports the shared construction needed by its definition. No source-library file is changed. The ordinary étale and pro-étale Hom-restriction results, the extension-by-zero adjunctions and the ordinary monoidal site-comparison square are used through private proof imports.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.siteHomComparison_restriction` (node `lem-sf-site-hom-comparison-thick`). Proved 1 of the original 2 holes. Added 0 holes; split off 0 unfinished results.

Unchanged original hole: `AlgebraicGeometry.ProEtale.siteHomComparison_exact_thick` (node `lem-sf-site-hom-comparison-thick`). All new public generic theorems and every private helper are proved. This is a partial delivery of the module, not a proof of its exactness clause.

## No longer needed

The proved restriction clause does not need nodes `lem-weil-pbc-localize-ringed-site-morphism`, `lem-weil-pbc-ringed-slice-pullback-mate-normalization`, or `lem-weil-pbc-ringed-slice-evaluation-transpose`: the exact ordinary closed restriction and the canonical monoidal square prove that clause directly. Removed these three entries from the item's `tool_uses`, and removed them from step 7 and its dependency union. No module is withdrawn and no whole-library pruning is claimed.

Removed unused private proof imports: `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, `Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose`, `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`, `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`, `Sheaf.CategoryTheory.SignedDerivedInternalHomExact`, `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`, `Sheaf.Paper.RingedSlicePullbackMateNormalization`, `WeilConjectures.Algebra.Homology.HomComplex`, and `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`. Dependencies still named in unchanged steps 1–6 remain planned dependencies of the original exactness hole; this delivery does not prune them from the DAG.

## Where the brief, the DAG or earlier work was wrong

No statement dispute. The definition changes only share existing expressions through equivalent constructors; their change record documents the unchanged mathematical meaning. Step 7 admits a shorter generic derived-closed argument than the ringed-slice model route. The original normalized exactness clause is substantially stronger than merely asserting existence of a triangulated structure: its explicit shifts must also be proved, and that hole remains untouched. The unit route is retained.

## New nodes

`lem-sf-exact-closed-derived-hom` attaches `CategoryTheory.Functor.isIso_ihomComparison_exactDerived` in `Sheaf.Algebra.Homology.ExactClosedDerivedHom`. Its proof uses K-injective preservation, the ordinary Hom-complex comparison and the monoidal quotient/localization squares; it is fully proved. The node also attaches the canonical shared comparison and its monoidal-square and invertibility APIs.

`lem-sf-exact-derived-tensor-square` attaches `CategoryTheory.Functor.exactDerivedSquare_monoidal` in `Sheaf.CategoryTheory.DerivedCategory.ExactDerivedTensorSquare`. Its proof transports the left-derived tensor square through the canonical exact-functor identifications; it is fully proved. The definition-sharing change record is `coord/changes/M2-site-hom-derived-monoidal-sharing.md`; its old and new bodies construct the same object.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
