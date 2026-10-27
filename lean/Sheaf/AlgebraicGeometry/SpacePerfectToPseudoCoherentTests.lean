module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import Sheaf.AlgebraicGeometry.SpacePseudoCoherentPerfectApproximation
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.SpaceDerivedQCohPullbackTensor
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.MPseudoCoherent

/-! # Perfect tests suffice for pseudo-coherent tensor tests on algebraic spaces

Source: Stacks Project, Derived Categories of Spaces, Tag 0CWH, lemma-perfect-enough
(blueprint: lem-sfb-space-perfect-to-pseudocoherent-tests).

The map to the affine base is presented by a scheme Y over an ambient scheme S,
a specified identification Y = Spec A, and the structure map f. All derived module
operations use the existing equivalent small affine etale ringed model.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a bounded-above quasi-coherent complex on a qcqs algebraic space over A,
pseudo-coherence of all perfect tensor section tests implies pseudo-coherence of
all pseudo-coherent tensor section tests. Bounds on K are cohomological, and no
uniform bound on the local finite-free models of a test object is imposed.
Source: Stacks Project, Derived Categories of Spaces, Tag 0CWH, lemma-perfect-enough
(blueprint: lem-sfb-space-perfect-to-pseudocoherent-tests).

Proof:
1. Spec A is qcqs by lem-weil-pbc-affine-scheme-qcqs. Use
   lem-sfb-space-qcqs-permanence and lem-sfb-space-affine-chart-uniform-qcoh-vanishing
   to obtain N >= 1 with higher quasi-coherent sections zero in degrees p >= N.
   The enlarged-site model of lem-trf-space-enlarged-etale-ringed-site-model
   identifies its section functor with the ordinary Hom(O,-) functor. This is left
   exact and preserves countable products. Apply
   lem-sfb-space-product-preserving-derived-functor-upper-bound: if L has cohomology
   zero above t, its derived sections vanish in degrees at least t + N. The same
   K-injective representative computes A-valued sections; forgetting scalars detects zero.
2. Fix a pseudo-coherent E and m, and put a = m - N - 1 - b, where b bounds K.
   By lem-sfb-space-pseudocoherent-perfect-approximation choose a triangle
   P -> E -> C -> P[1] in D_QCoh with P perfect, cohomology isomorphisms above a
   and an epimorphism at a.
3. The long exact sequence (lem-sf-derived-homology-long-exact) shows H^i(C) = 0
   for i >= a: the preceding map is surjective and the following map is injective.
4. Standard truncation (def-sbc-standard-tstructure-derived-category) gives
   representatives of C and K zero above a-1 and b. Use
   lem-pc-kflat-bounded-flat-replacement and lem-pc-bounded-above-flat-kflat-site
   to replace them by flat-term K-flat complexes with those same term bounds.
   The total tensor model of lem-weil-pbc-site-derived-tensor-descent has no
   nonzero summands in degrees j >= a+b = m-N-1.
5. By lem-sfb-space-derived-qcoh-pullback-tensor this tensor is quasi-coherent.
   Step 1 with t = m-N-2 shows its derived sections vanish for i >= m-2,
   and in particular for i >= m-1.
6. Tensor the triangle using lem-weil-pbc-kflat-fixed-tensor-triangulated and
   apply sections using lem-pc-right-derived-functor-triangulated. The long exact
   cohomology sequence and both adjacent vanishings from step 5 show that the map
   from the P-test to the E-test is a cohomology isomorphism for i >= m.
7. The P-test is pseudo-coherent by hypothesis. By
   lem-pc-ring-pseudo-coherent-iff-all-m choose a finite-free m-approximation of it.
   Compose with the map to the E-test. Step 6 preserves the required isomorphisms
   above m and epimorphism at m, giving an m-pseudo-coherent E-test by
   def-pc-ring-m-pseudo-coherent. This holds for every m, so the same all-m
   criterion proves that the E-test is pseudo-coherent. -/
theorem isPseudoCoherent_tensor_sections_of_perfect_tests
    {S : Scheme.{u}} (A : Type u) [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
    [HasDerivedCategory.{w} X.SmallModules]
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : X.IsAbsolutelyQuasiSeparated)
    (K : X.DerivedModules) (hK : X.derivedQCohProperty K)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor X.SmallModules i).obj K))
    (hTests : ∀ P : X.DerivedModules,
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
        X.smallStructureSheaf P →
      DerivedCategory.IsPseudoCoherent
        ((affineDerivedSections A Y e X f).obj
          (X.derivedDualityModel.closed.tensor.obj (P, K)))) :
    ∀ E : X.DerivedModules, X.IsPseudoCoherent E →
      DerivedCategory.IsPseudoCoherent
        ((affineDerivedSections A Y e X f).obj
          (X.derivedDualityModel.closed.tensor.obj (E, K))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
