/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedGlobalProper.CondensedGlobalProperFrobenius

/-! # Proper normalization of the native derived compact exchange

Source: identity-compactification specialization of normalized cohomology transport.
(blueprint: lem-a1-condensed-proper-native-exchange-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedProperNative
variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] [IsAlgClosed k]
  {Y : Scheme.{u}} (a : Y ⟶ Spec (.of k))
  (g : Y ⟶ Y) [IsIso g] (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h]
  (w : g ≫ a = a ≫ h)

/-- The actual derived ordinary operator, before zero homology or scalar sections.
Source: the ordinary unit--square--counit mate and inverse canonical point pullback.
(blueprint: lem-a1-condensed-proper-native-exchange-comparison). -/
def ordinary
    (K : CondensedRing.CohomologyTransport.D (Profinite.padicAlgClRingObj l) Y)
    (θ : (CondensedRing.CohomologyTransport.L
      (Profinite.padicAlgClRingObj l) g).obj K ≅ K) :
    End ((CondensedRing.CohomologyTransport.R (Profinite.padicAlgClRingObj l) a).obj K) :=
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
      (Profinite.padicAlgClRingObj l) h ≪≫
    Functor.mapDerivedCategoryNatIso
      (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) h) ≪≫
    Functor.mapDerivedCategoryIdIso _).inv.app
      ((CondensedRing.CohomologyTransport.R (Profinite.padicAlgClRingObj l) a).obj K) ≫
    (CondensedRing.CohomologyTransport.ordinary (Profinite.padicAlgClRingObj l)
      g a a h w).app K ≫
    (CondensedRing.CohomologyTransport.R (Profinite.padicAlgClRingObj l) a).map θ.hom

end WeilConjectures.CondensedProperNative
