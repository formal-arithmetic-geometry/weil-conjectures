## What changed

Proved AlgebraicGeometry.Etale.nonempty_stratumAmbientHomIso from the existing
AlgebraicGeometry.Etale.immersionInternalHomIso by forgetting its extra evaluation
compatibility. The existing theorem implements exactly the unit's projection,
adjunction, tensor-Hom and Yoneda calculation. No unit step is bypassed.

The etale signature uses the existing named immersion functors and explicitly spells
out the derived categories. The change is definitional and is documented in
coord/changes/j2-stratum-ambient-hom-presentation.md. The original public imports are
retained for their downstream reexports. The new public import is
Sheaf.AlgebraicGeometry.EtaleGenericStratumMate. The DAG records this route and
retains the pending pro-etale plan.

## Proved and sorry left

Closed 1 of the original 2 holes:
AlgebraicGeometry.Etale.nonempty_stratumAmbientHomIso.
Added 0 holes; split off 0 statements.

One original hole remains: AlgebraicGeometry.ProEtale.nonempty_stratumAmbientHomIso
(blueprint: lem-weil-stratum-ambient-hom). Its statement and proof docstring are unchanged.
The intrinsic constant-ring internal Hom is not the condensed coefficient internal Hom;
the available condensed projection theorems therefore do not directly prove this clause.
Fixed-coefficient comparison still requires a derived tensor/internal-Hom transport.

## No longer needed

Removed direct private proof imports (the following modules are not withdrawn):

- WeilConjectures.SixFunctors.OpenClosed.Stalk
- WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
- Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
- Sheaf.CategoryTheory.SitePullbackAbelianExact
- Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
- WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
- Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
- Sheaf.CategoryTheory.RingedSliceExtensionTensor
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.Algebra.Homology.KInjectiveHomComplex
- WeilConjectures.Algebra.Homology.HomTensorTotal
- WeilConjectures.Algebra.Homology.RhomGlobalSections
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
- Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
- Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
- Sheaf.Paper.ProEtaleCanonicalTensorPullback
- Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
- Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients

For the etale clause, the ten-step local reconstruction is replaced by the existing
lem-sf-etale-generic-stratum-mate. In particular the direct stalk, exactness, K-flat,
projection and tensor-Hom proof imports are unnecessary here; their needed mathematics
is already encapsulated in that theorem. The pending pro-etale clause still cites the
original planned dependencies, so no whole DAG node or module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG plan did not exploit the already proved, stronger evaluation-normalized etale
immersion identity. Expanding the original derived-category abbreviations and shriek
functors during kernel conversion repeatedly exceeded the single-file compile limit;
the equivalent explicit-category/named-functor presentation compiles. Empty strata,
identity immersions and the zero ring remain covered by the reused theorem with exactly
the same hypotheses. No mathematical statement was found false. No new nodes.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
