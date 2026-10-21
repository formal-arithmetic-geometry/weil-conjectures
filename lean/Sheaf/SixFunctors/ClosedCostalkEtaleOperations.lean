/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients

/-! # Exact-operation presentations for the closed étale costalk comparison

Source: Stacks, Modules on Sites, Tags 03D1 and 03D6; Tag 05RU.
These are the unchanged operations previously defined in ClosedCostalkDuality.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Modules over arbitrary commutative etale coefficients, without boundedness.
Source: Stacks, Modules on Sites, Tag 03D1
(blueprint: def-weil-closed-costalk-etale-operations). -/
abbrev closedCostalkEtaleModules (X : Scheme.{u})
    (R : Sheaf X.smallEtaleTopology CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1} ((sheafCompose X.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The standard ordinary unbounded localization on the small etale site.
Source: Stacks, Tag 05RU (blueprint: def-weil-closed-costalk-etale-operations). -/
noncomputable instance closedCostalkEtaleModules_hasDerivedCategory (X : Scheme.{u})
    (R : Sheaf X.smallEtaleTopology CommRingCat.{u + 1}) :
    HasDerivedCategory (closedCostalkEtaleModules X R) :=
  HasDerivedCategory.standard _

/-- Ring inverse image, by left Kan extension and sheafification on the actual etale sites.
Source: Stacks, Tags 00VC and 00WX (blueprint: def-weil-closed-costalk-etale-operations). -/
noncomputable def closedCostalkEtaleRingPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology CommRingCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology CommRingCat.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @Etale ⊤ f) CommRingCat.{u + 1}
    (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)

/-- The canonical ring-sheaf adjunction determining the coefficient unit.
Source: Stacks, Tag 00YV (blueprint: def-weil-closed-costalk-etale-operations). -/
noncomputable def closedCostalkEtaleRingAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    closedCostalkEtaleRingPullback f ⊣
      (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (Y.smallGrothendieckTopology @Etale)
        (X.smallGrothendieckTopology @Etale) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) CommRingCat.{u + 1}
    (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)

/-- Actual closed direct image with scalars restricted through the inverse-image unit.
Source: Stacks, Modules on Sites, Tag 03D6
(blueprint: def-weil-closed-costalk-etale-operations). -/
noncomputable def closedCostalkEtaleModulePush {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf Y.smallEtaleTopology CommRingCat.{u + 1}) :
    closedCostalkEtaleModules X ((closedCostalkEtaleRingPullback f).obj R) ⥤
      closedCostalkEtaleModules Y R :=
  SheafOfModules.pushforward.{u + 1}
    (F := MorphismProperty.Over.pullback @Etale ⊤ f)
    (J := Y.smallGrothendieckTopology @Etale) (K := X.smallGrothendieckTopology @Etale)
    (S := (sheafCompose Y.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    (R := (sheafCompose X.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((closedCostalkEtaleRingPullback f).obj R))
    ⟨Functor.whiskerRight ((closedCostalkEtaleRingAdjunction f).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Closed direct image is additive since its linear components are unchanged.
Source: Stacks, Tag 03D6 (blueprint: def-weil-closed-costalk-etale-operations). -/
noncomputable instance closedCostalkEtaleModulePush_additive {X Y : Scheme.{u}}
    (f : X ⟶ Y) (R : Sheaf Y.smallEtaleTopology CommRingCat.{u + 1}) :
    (closedCostalkEtaleModulePush f R).Additive where
  map_add := by intros; rfl

end AlgebraicGeometry.Scheme
