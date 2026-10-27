module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses

import Sheaf.CategoryTheory.KInjectiveComputes
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.Algebra.Category.ModuleCat.AB

/-! # Finite amplitude of algebraic-space global sections

Source: Stacks Project, Tags 08F7(3), 072C and 05TC(1)
(blueprint: lem-sfb-space-global-sections-amplitude).

The existing equivalent small ringed model represents the original étale module topos.
Degree m hypercohomology is written as H⁰ RΓ(E[m]), using the recorded zeroth functor.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Global sections have a uniform finite upper amplitude on unbounded D_QCoh and
preserve every lower cohomological bound. The shifts in the conclusions encode
H^m RΓ(E) as H⁰ RΓ(E[m]); no opposite bound on E is assumed in either clause.

Source: Stacks Project, Tags 08F7(3), 072C and 05TC(1)
(blueprint: lem-sfb-space-global-sections-amplitude).

Proof: global sections are Hom(O_X,-), hence additive, left exact and product preserving
by the kernel and product universal properties. Choose C ≥ 1 from
lem-sfb-space-qcoh-cohomology-finite-bound (072C). The module/abelian cohomology comparison
lem-sfb-ringed-site-global-module-abelian-cohomology and lem-sp-kinjective-computes
identify its vanishing with R^pΓ(M)=0 for p ≥ C on all quasi-coherent modules.
Apply lem-sfb-space-product-preserving-derived-functor-upper-bound (08F7) with b=t:
it gives vanishing for m ≥ t+C even when E is unbounded below. Put N=C-1.
For the lower clause use def-sbc-standard-tstructure-derived-category to take a
bounded-below representative, then lem-sc-bounded-below-injective-resolution to take
one bounded-below K-injective resolution computing both versions of derivation.
Lemma lem-weil-pbc-derived-functor-negative-vanishing (05TC) gives vanishing for m<t
without an upper bound. The small ringed model equivalence preserves all these objects
and computations, and the derived shift identity identifies H⁰ RΓ(E[m]) with H^m RΓ(E). -/
theorem globalSections_finiteAmplitude
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [CompactSpace (Point X.obj.obj)] (hqs : X.IsAbsolutelyQuasiSeparated)
    [HasDerivedCategory.{w} X.SmallModules] :
    ∃ N : ℤ, 0 ≤ N ∧ ∀ (E : X.DerivedQCoh) (t : ℤ),
      ((∀ i : ℤ, t < i →
          IsZero ((DerivedCategory.homologyFunctor X.SmallModules i).obj E.obj)) →
        ∀ m : ℤ, t + N < m →
          IsZero ((ringedSiteZerothHypercohomologyOfUniverses.{u, u, u, w}
            X.smallEtaleModelTopology X.smallStructureSheaf).obj (E.obj⟦m⟧))) ∧
      ((∀ i : ℤ, i < t →
          IsZero ((DerivedCategory.homologyFunctor X.SmallModules i).obj E.obj)) →
        ∀ m : ℤ, m < t →
          IsZero ((ringedSiteZerothHypercohomologyOfUniverses.{u, u, u, w}
            X.smallEtaleModelTopology X.smallStructureSheaf).obj (E.obj⟦m⟧))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
