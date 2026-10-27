module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses

import Sheaf.CategoryTheory.RingedSitePerfectDuality
import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel
import Mathlib.CategoryTheory.Triangulated.Generators
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.SpaceQcqsDistinguishedSquareInduction
import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution

/-! # Perfect generators detect lower bounds on algebraic spaces

Source: Stacks Project, Derived Categories of Spaces, Tag 0GFI,
`proposition-detecting-bounded-below`, conditions (1), (2)/(3), (6)
(blueprint: lem-sfb-space-generator-detects-lower-bound).

The existing small affine etale ringed model presents the same module topos.
Condition (iii) uses H⁰ RΓ of integer shifts to express every degree of RΓ.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A perfect generator detects bounded-below quasi-coherent cohomology by negative
Hom vanishing, equivalently by bounded-below global sections of its dual tensor K.

Source: Stacks Project, Tag 0GFI, `proposition-detecting-bounded-below`
(blueprint: lem-sfb-space-generator-detects-lower-bound).

Proof:
1. For (i) implies (ii), lem-sfb-space-perfect-ext-window supplies a finite test
   interval [a,b] for G. If H^q(K)=0 for q<c, then H^q(K[j])=0 on that interval
   for j<c-b, so Hom(G,K[j]) vanishes.
2. Lemma lem-sfb-ringed-site-perfect-duality identifies dual G tensor K with
   RHom(G,K). Lemma lem-sfb-derived-internal-hom-sections-model identifies degree j
   of its derived sections with Hom(G,K[j]). This proves (ii) iff (iii).
3. Fix K satisfying (ii). Eventual negative Hom vanishing is stable under zero,
   isomorphisms, finite sums, retracts and shifts. Hom-out-of-triangle exactness
   (lem-weil-pbc-hom-out-of-triangle-exact), including rotations and translated
   bounds, gives two-out-of-three. By def-pc-thick-closure and
   lem-sfb-space-perfect-generator-thick it holds for every perfect test object.
4. By the standard truncation triangle (def-sbc-standard-tstructure-derived-category),
   the finite-window lemma and lem-weil-pbc-hom-into-triangle-exact, this test
   condition for any perfect P is equivalent for E and tau_le a E: the remaining
   truncation is bounded below and its adjacent Hom groups eventually vanish.
5. Apply lem-sfb-space-qcqs-distinguished-square-induction to the assertion that
   all perfect tests force a lower bound. On an affine, test with O. By
   lem-sfb-affine-etale-derived-module-realization and the global-Hom sections model,
   the bound transfers from derived sections through the exact faithful associated
   module functor. This includes the zero ring and empty affine.
6. In a distinguished square U -> W <- V, with U quasi-compact open and V affine,
   lem-sfb-space-supported-koszul-low-localization gives a perfect supported test B.
   Its eventual vanishing gives tau_le a E isomorphic to tau_le a Ri_*(E|_U).
7. Put M=Ri_*(E|_U). Quasi-coherent direct image is supplied by
   lem-sfb-space-derived-pushforward-coproducts. Step 4 transfers all perfect tests
   from E to M. By lem-sfb-space-perfect-open-retract, every perfect A on U is a
   retract of i^*Q for a perfect Q on W. The adjunction in
   lem-sfb-space-derived-etale-chart-calculus transfers the test for Q to i^*Q,
   hence to A. The induction hypothesis on U gives a lower bound for E|_U.
8. By lem-sc-bounded-below-injective-resolution, choose a bounded-below K-injective
   representative of E|_U. Its direct image computes M and stays bounded below.
   If c is a lower bound for M, the truncation comparison gives vanishing for E
   below min(c,a+1). This proves the square step, hence (ii) implies (i) by induction.
-/
theorem generator_detects_lower_bound
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules]
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : X.IsAbsolutelyQuasiSeparated)
    (G : X.DerivedQCoh)
    (hG : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      X.smallStructureSheaf G.obj)
    (hgen : ∀ F : X.DerivedQCoh,
      (∀ n : ℤ, Subsingleton (G.obj⟦n⟧ ⟶ F.obj)) → IsZero F.obj)
    (K : X.DerivedQCoh) :
    ((∃ c : ℤ, ∀ j : ℤ, j < c →
        IsZero ((DerivedCategory.homologyFunctor X.SmallModules j).obj K.obj)) ↔
      (∃ c : ℤ, ∀ j : ℤ, j < c → Subsingleton (G.obj ⟶ K.obj⟦j⟧))) ∧
    ((∃ c : ℤ, ∀ j : ℤ, j < c → Subsingleton (G.obj ⟶ K.obj⟦j⟧)) ↔
      (∃ c : ℤ, ∀ j : ℤ, j < c →
        IsZero ((ringedSiteZerothHypercohomologyOfUniverses.{u, u, u, w}
          X.smallEtaleModelTopology X.smallStructureSheaf).obj
            ((X.derivedDualityModel.closed.tensor.obj
              (X.derivedHom.obj (op G.obj, X.derivedStructure), K.obj))⟦j⟧)))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
