/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import Sheaf.SixFunctors.GeometricStalkTensorConstantSingle
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! # Geometric-stalk test for Tor intervals on the small etale site

Source: Stacks Project, sites-cohomology.tex, Tag 0DJJ; etale-cohomology.tex,
Tags 03PT, 03PU and 03Q1; blueprint main-20261015, opening and affine-space
paragraphs of sk-prop-sf-rf-shriek-preservation
(blueprint: lem-sf-etale-stalk-tor-test).

The geometric stalk is the exact pointed-neighbourhood colimit functor, applied
termwise and localized. Both the test and the inverse-image consequence apply to
arbitrary unbounded derived complexes over any commutative coefficient ring.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- Tor amplitude is detected on every geometric stalk by all ordinary module tests,
and exact constant-coefficient inverse image preserves the same interval.
Source: Stacks Project, Tag 0DJJ and Tag 03Q1; blueprint main-20261015,
sk-prop-sf-rf-shriek-preservation, opening and affine-space paragraphs
(blueprint: lem-sf-etale-stalk-tor-test).

Proof:
1. Kernels, images, quotients and cohomology of module sheaves are computed on
underlying abelian sheaves. Exactness of geometric stalks and the exact-functor
homology comparison give H^i(E)_t = H^i(E_t), for unbounded E as well. Stalk
conservativity detects vanishing of each cohomology sheaf. Use
prop-weil-pbc-geometric-stalks-exact, lem-sp-exact-functor-preserves-homology and
lemma-weil-pbc-geometric-stalk-conservative.
2. If K has the interval, test def-kun-tor-amplitude on the constant sheaf of
any A-module M in degree zero. Apply step 1 and
lem-sfb-geometric-stalk-tensor-constant-single to identify the stalk of this
derived tensor with K_t tensor^L M[0], giving the required vanishing.
3. Conversely, test against an arbitrary module sheaf F in degree zero. By
lem-sfb-etale-derived-tensor-stalk its tensor with K has stalk K_t tensor^L F_t[0].
The assumed condition with M = F_t makes every out-of-interval cohomology stalk
zero. Step 1 and conservativity give the vanishing sheaf, precisely
 def-kun-tor-amplitude. No boundedness assumption is used.
4. For any u : U -> T, prop-weil-pbc-inverse-image-modules-exact identifies the
constant rings and supplies exact inverse image, hence its termwise derived
functor. The natural comparison lemma-openclosed-stalk-upperstar identifies
(u^*K)_v with K_(v followed by u). Its additivity and naturality for every scalar
multiplication make this comparison A-linear, and naturality for differentials
makes it a comparison of complexes. Exactness of stalks passes it to derived
categories. Apply step 2 on T and step 3 on U to preserve the interval. -/
theorem geometricStalk_torAmplitude_test
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K : DerivedCategoryModule A T) (a b : ℤ) (_hab : a ≤ b) :
    (DerivedCategory.hasTorAmplitudeIn A T a b K ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
        (M : ModuleCat.{u + 1} A) (i : ℤ), i < a ∨ b < i →
        IsZero ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) i).obj
          (((pointSmallEtale t).sheafFiber
            (A := ModuleCat.{u + 1} A)).mapDerivedCategory.obj K ⊗
            (_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj M))) ∧
    (∀ (U : Scheme.{u}) (f : U ⟶ T),
      DerivedCategory.hasTorAmplitudeIn A T a b K →
        DerivedCategory.hasTorAmplitudeIn A U a b
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)) := by
  sorry

end AlgebraicGeometry.Etale
