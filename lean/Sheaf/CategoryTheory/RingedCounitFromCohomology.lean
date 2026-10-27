/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.ExactDerivedAdjunctionBounds
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import Sheaf.CategoryTheory.HeartTestBoundedBelow

/-! # Detecting the bounded-below ringed counit on cohomology

Source: Stacks Project, Cohomology on Sites, Tag 0D7S,
lemma-bounded-in-image-upstairs (blueprint: lem-sfb-ringed-counit-from-cohomology).
-/

@[expose] public section

set_option autoImplicit false

universe u wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.RingedToposMorphism

/-- The canonical derived adjunction for an exact module pullback. Its right adjoint
is the published total right derived functor computed by K-injective resolutions.
The small-site Grothendieck theorem supplies the resolution instance internally.
The ordinary left adjoint to the induced module direct image is the module pullback,
uniquely up to its adjunction-compatible isomorphism.

Source: Stacks Project, Cohomology on Sites, Tags 07A6 and 0D7S
(blueprint: lem-sfb-ringed-counit-from-cohomology). -/
noncomputable def exactModuleDerivedAdjunction
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {T : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf T CommRingCat.{u})
    [HasDerivedCategory.{wA} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))]
    [HasDerivedCategory.{wB} (ringedSiteModules.{u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj B))]
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj B))
    (L : ringedSiteModules.{u} ((sheafCompose T (forget₂ CommRingCat RingCat)).obj B) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ f.modules) :=
  letI := SheafOfModules.isGrothendieckAbelian
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
  adj.mapDerivedCategoryRightDerivedAdjunction

/-- The canonical derived counit at a bounded-below complex is invertible if it is
invertible at every cohomology sheaf placed in degree zero.

Source: Stacks Project, Cohomology on Sites, Tag 0D7S,
lemma-bounded-in-image-upstairs (blueprint: lem-sfb-ringed-counit-from-cohomology).

Proof:
1. Small-site module categories have K-injective resolutions
   (prop-pur-kinjective-resolutions-exist). Exact pullback induces the termwise
   triangulated functor and commutes with cohomology
   (lem-weil-pbc-exact-functor-derived-factorization and
   lem-weil-pbc-exact-functor-complex-cohomology), preserving every lower bound.
2. The right derived direct image is triangulated
   (lem-pc-right-derived-functor-triangulated). Its adjunction to the exact
   pullback makes it preserve every lower bound
   (lem-pur-exact-derived-adjunction-bounds, clause 1).
3. The ordinary module adjunction (lem-weil-pbc-ringed-topoi-module-adjunction)
   induces the very canonical derived adjunction used here. Its counit commutes
   with shifts (lem-sp-canonical-right-derived-adjunction-shift).
4. Restrict the composite and identity to D+ and apply
   lem-weil-pbc-heart-test-bounded-below. Finite Postnikov induction makes the
   counit invertible on each upper truncation. In each degree m, the truncation
   maps induce cohomology isomorphisms for both functors, so naturality makes
   H^m of the counit invertible. Cohomology detects isomorphisms, giving the claim
   without an upper bound or preservation of infinite limits. -/
theorem counit_isIso_of_cohomology
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {T : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf T CommRingCat.{u})
    [HasDerivedCategory.{wA} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))]
    [HasDerivedCategory.{wB} (ringedSiteModules.{u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj B))]
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj B))
    (L : ringedSiteModules.{u} ((sheafCompose T (forget₂ CommRingCat RingCat)).obj B) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ f.modules)
    (K : DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)))
    (hK : ∃ a : ℤ, ∀ q : ℤ, q < a → IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hH : ∀ q : ℤ, IsIso ((exactModuleDerivedAdjunction A B f L adj).counit.app
      ((DerivedCategory.singleFunctor _ 0).obj ((DerivedCategory.homologyFunctor _ q).obj K)))) :
    IsIso ((exactModuleDerivedAdjunction A B f L adj).counit.app K) := by
  sorry

end CategoryTheory.RingedToposMorphism
