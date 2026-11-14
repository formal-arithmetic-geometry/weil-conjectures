/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback

/-! # Constructibility across a complementary open and closed pair

The finite stratifications of the two pieces concatenate. Normalizing the
coefficient pullback lets us apply its composition isomorphism directly.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

namespace CondensedRing

/-- Extension by zero along a quasi-compact open immersion and direct image along its
complementary closed immersion preserve constructibility, for any condensed ring. -/
theorem constructible_open_closed_images
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (k : Z ⟶ X) [IsClosedImmersion k]
    (hjk : Set.range j = (Set.range k)ᶜ)
    :
    (∀ PU : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U),
      IsConstructibleModuleObject (condensedRingObj Λ U) PU →
      IsConstructibleModuleObject (condensedRingObj Λ X)
        ((openImmersionLowerShriek Λ j).obj PU)) ∧
    (∀ PZ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z),
      IsConstructibleModuleObject (condensedRingObj Λ Z) PZ →
      IsConstructibleModuleObject (condensedRingObj Λ X) ((lowerStar Λ k).obj PZ)) := by
  have := moduleCounitOfAbelian Λ k (ProEtale.abelian_closed_support_counit_and_unit k j hjk).1
  let e := asIso (upperStarLowerStarAdjunction Λ k).counit
  have hkj : Set.range k = (Set.range j)ᶜ := by rw [hjk, compl_compl]
  constructor
  · exact isConstructibleModuleObject_openImmersionLowerShriek Λ j
  · intro PZ hPZ
    apply constructible_of_restrictions j k hkj
    · let φ := condensedPullbackHom Λ j
      let A := ((ProEtale.upperStar Ab.{u + 1} j).mapMod _).obj ((lowerStar Λ k).obj PZ)
      have h := constructible_of_isZero _ _ (openRestrictionPushforwardZero Λ k j hjk PZ)
      have h' := constructible_comap φ
        (constructible_of_iso ((Mod.extendScalarsIsoComapInv φ).app A) h)
      exact constructible_of_iso
        (((Mod.comapComp φ (inv φ)).symm ≪≫
          Mod.comapCongr (IsIso.hom_inv_id φ) ≪≫ Mod.comapId _).app A) h'
    · let φ := condensedPullbackHom Λ k
      let A := ((ProEtale.upperStar Ab.{u + 1} k).mapMod _).obj ((lowerStar Λ k).obj PZ)
      have h := constructible_of_iso (e.app PZ).symm hPZ
      have h' := constructible_comap φ
        (constructible_of_iso ((Mod.extendScalarsIsoComapInv φ).app A) h)
      exact constructible_of_iso
        (((Mod.comapComp φ (inv φ)).symm ≪≫
          Mod.comapCongr (IsIso.hom_inv_id φ) ≪≫ Mod.comapId _).app A) h'

end CondensedRing
end AlgebraicGeometry.ProEtale
