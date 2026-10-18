/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!
# Closed support Tor bound

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-prop-sf-rf-shriek-preservation/sk-prop-sf-rf-shriek-preservation.proof.md`,
Step 3 (blueprint: lem-sf-closed-support-tor-bound).
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- A distinguished closed-support triangle adds one to the upper Tor bound.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-prop-sf-rf-shriek-preservation/sk-prop-sf-rf-shriek-preservation.proof.md`,
Step 3 (blueprint: lem-sf-closed-support-tor-bound).

Proof, following the five steps of the node:
1. Put E = i^× K and F = i_* E. Exact functors act termwise on derived categories
   (lem-sf-exact-functor-derived-triangulated). The counit isomorphisms in each degree
   identify i^* F with E. For any module sheaf N on Z, put M = i_* N; the same counit
   identifies i^* M with N, including their degree-zero complexes.
2. Tensor the assumed distinguished triangle with M[0]. The tensor functor is
   triangulated (lem-kun-derived-tensor-triangulated). The two assumed Tor bounds
   give cohomology of K tensor M only in [a,b], and of Q tensor M only in [a,b+e].
3. The long exact sequence (lem-sf-derived-homology-long-exact) has the segment
   H^(r-1)(Q tensor M) → H^r(F tensor M) → H^r(K tensor M).
   If r < a, both outer terms vanish. If r > b+e+1, then r-1 > b+e and r > b
   since e ≥ 0, so both again vanish. Hence the middle term vanishes outside
   [a,b+e+1], including the exact claimed endpoints.
4. Apply the exact-functor cohomology comparison
   (lem-weil-pbc-exact-functor-bounded-below) to i^*. It has no boundedness
   hypothesis for this comparison. Thus i^*(F tensor M) has the same cohomology bound.
5. The inverse-image monoidal comparison (lem-kun-inverse-image-monoidal), followed
   by the counit identifications from step 1, identifies i^*(F tensor M) with
   E tensor N. Since N was arbitrary, def-kun-tor-amplitude gives the conclusion.
-/
theorem closedSupport_torAmplitude
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T V : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : V ⟶ T) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    [PreservesFiniteLimits (lowerStar (ModuleCat.{u + 1} A) i)]
    [PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) i)]
    [PreservesFiniteLimits (upperStar (ModuleCat.{u + 1} A) i)]
    [PreservesFiniteColimits (upperStar (ModuleCat.{u + 1} A) i)]
    [IsIso (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit]
    (a b e : ℤ) (hab : a ≤ b) (he : 0 ≤ e)
    (K : DerivedCategoryModule A T)
    (hK : DerivedCategory.hasTorAmplitudeIn A T a b K)
    (hQ : DerivedCategory.hasTorAmplitudeIn A T a (b + e)
      ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
        (((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory).obj K)))
    (δ : ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
        (((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory).obj K)) ⟶
      (shiftFunctor (DerivedCategory
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) (1 : ℤ)).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) i)).obj
          ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K)))
    (hδ : Triangle.mk
          ((Adjunction.ofIsLeftAdjoint
            (R(lowerStar (ModuleCat.{u + 1} A) i))).counit.app K)
          ((mapDerivedUpperStarLowerStarAdjunction
            (ModuleCat.{u + 1} A) j).unit.app K)
          δ ∈ distTriang _) :
    DerivedCategory.hasTorAmplitudeIn A Z a (b + e + 1)
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj K) := by
  sorry

end AlgebraicGeometry.Etale
