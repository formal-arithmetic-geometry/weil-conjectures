/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
import Sheaf.AlgebraicGeometry.AbelianDerivedExchangePlusCompatibility
import Sheaf.AlgebraicGeometry.AllowableTorsionInverseImage
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtension
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.AlgebraicGeometry.QcqsHigherImagesPrimeTorsion
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Bounded allowable-torsion smooth base change

Source: blueprint, sec-smooth-base-change/sk-rem-rest,
sbc-thm-bounded-allowable-torsion (blueprint: sbc-thm-bounded-allowable-torsion).
The ambient conclusion uses the unbounded derived category of abelian sheaves.
The bounded-output clause includes membership and invertibility in the full subcategory.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem allowableTorsionSheafProperty_of_iso {V : Scheme.{u}} {P : Set ℕ}
    {F G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : allowableTorsionSheafProperty V P F) (e : F ≅ G) :
    allowableTorsionSheafProperty V P G := by
  intro Ω _ _ s x
  let φ := (Scheme.pointSmallEtale s).sheafFiber.mapIso e
  obtain ⟨n, hn, hp, hx⟩ := hF Ω s (φ.inv.hom x)
  refine ⟨n, hn, hp, ?_⟩
  have hφ : φ.hom.hom (φ.inv.hom x) = x := by
    rw [← AddCommGrpCat.comp_apply, φ.inv_hom_id, AddCommGrpCat.id_apply]
  rw [← hφ, ← map_nsmul, hx, map_zero]

private theorem isTorsionSheafOfPrimes_of_allowable_forget {V : Scheme.{u}} {P : Set ℕ}
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (hF : allowableTorsionSheafProperty V P
      ((sheafCompose V.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj F)) :
    Scheme.IsTorsionSheafOfPrimes P F := by
  constructor
  intro Ω _ _ s x
  let Φ := Scheme.pointSmallEtale s
  let U := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}
  have : LocallySmall.{u + 1} V.Etale :=
    @locallySmall_of_univLE V.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  let φ := (Φ.uliftSheafFiberIso AddCommGrpCat.{u + 1}).symm.app
      ((sheafCompose V.smallEtaleTopology U).obj F)
    ≪≫ ((Φ.ulift.{u + 1}).sheafFiberCompIso U).app F ≪≫
    U.mapIso ((Φ.uliftSheafFiberIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).app F)
  obtain ⟨n, hn, hp, hx⟩ := hF Ω s (φ.inv.hom x)
  refine ⟨n, hn, fun p hpn ↦ hp p (Nat.prime_of_mem_primeFactors hpn)
    (Nat.dvd_of_mem_primeFactors hpn), ?_⟩
  have hφ : φ.hom.hom (φ.inv.hom x) = x := by
    rw [← AddCommGrpCat.comp_apply, φ.inv_hom_id, AddCommGrpCat.id_apply]
  have hh := congrArg φ.hom.hom hx
  simpa only [map_nsmul, map_zero, hφ] using hh

private theorem isIso_derivedBaseChangeMapPlus_single_of_allowable
    {X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    [Smooth f] [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g f)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : allowableTorsionSheafProperty T S.invertiblePrimes F) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  let U := sheafCompose T.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  let G := U.objPreimage F
  let eF : U.obj G ≅ F := U.objObjPreimageIso F
  have : Scheme.IsTorsionSheafOfPrimes S.invertiblePrimes G :=
    isTorsionSheafOfPrimes_of_allowable_forget G
      (allowableTorsionSheafProperty_of_iso hF eF.symm)
  have : Scheme.IsTorsionSheafOfInvertibleOrder S G :=
    Scheme.IsTorsionSheafOfInvertibleOrder.of_isTorsionSheafOfPrimes _ G
  let τ := derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq
  apply (NatTrans.isIso_app_iff_of_iso τ
    ((_root_.DerivedCategory.Plus.singleFunctor _ 0).mapIso eF)).1
  apply (NatTrans.isIso_app_iff_of_iso τ
    ((U.mapDerivedCategoryPlusSingleFunctor 0).app G)).1
  apply (isIso_derivedBaseChangeMapPlus_app_forget₂_iff sq.toCommSq
    ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G)).2
  rw [← baseChange_eq_derivedBaseChangeMapPlus]
  exact isIso_baseChange_app_singleFunctor_obj_of_smooth _ f sq G

private theorem allowableTorsionPlusProperty_rightDerived_single
    {U V : Scheme.{u}} (g : U ⟶ V) [QuasiCompact g] [QuasiSeparated g]
    (P : Set ℕ) (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : allowableTorsionSheafProperty U P F) :
    allowableTorsionPlusProperty V P
      (R(lowerStar AddCommGrpCat.{u + 1} g).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  let G := lowerStar AddCommGrpCat.{u + 1} g
  have hge := G.isGE_rightDerivedFunctor_obj_singleFunctor F
  refine ⟨?_, ⟨0, hge⟩⟩
  intro q
  by_cases hq : q < 0
  · have hz := (_root_.DerivedCategory.isGE_iff _ 0).1 hge q hq
    intro Ω _ _ s x
    have := (Scheme.pointSmallEtale s).sheafFiber_additive
      (A := AddCommGrpCat.{u + 1})
    have := AddCommGrpCat.subsingleton_of_isZero
      (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map_isZero hz)
    refine ⟨1, by omega, fun p hp hpn ↦ False.elim (hp.not_dvd_one hpn), ?_⟩
    simpa only [one_nsmul] using Subsingleton.elim x 0
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hq)
    let H := (_root_.DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      (G.rightDerivedFunctorPlus.obj
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))
    have hH : allowableTorsionSheafProperty V P H := by
      intro Ω _ _ s x
      let c := Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω)))
      let φ := (Scheme.pointSmallEtalePrecomp s c).sheafFiber.app H
      have : IsIso φ := Scheme.isIso_pointSmallEtalePrecomp_sheafFiber s c H
      obtain ⟨n, hn, hx, hp⟩ := qcqs_higherDirectImages_prime_torsion g P F
        (fun Ω _ _ s x ↦ by
          obtain ⟨n, hn, hp, hx⟩ := hF Ω s x
          exact ⟨n, hn, hx, hp⟩) q (AlgebraicClosure Ω) (c ≫ s) (φ.hom x)
      refine ⟨n, hn, hp, ?_⟩
      apply (ConcreteCategory.bijective_of_isIso φ).1
      change φ.hom (n • x) = φ.hom 0
      simpa only [map_nsmul, map_zero] using hx
    apply allowableTorsionSheafProperty_of_iso hH
    exact (_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
      (G.rightDerivedFunctorPlusCompatibility.app
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))

/-- Smooth base change for bounded allowable-torsion abelian complexes.
Source: blueprint sec-smooth-base-change/sk-rem-rest, bounded allowable-torsion theorem
(blueprint: sbc-thm-bounded-allowable-torsion).

Proof: view K in the bounded-below derived category. Identify abelian sheaves with
sheaves of ULift ℤ-modules. Their geometric stalk comparisons preserve positive
annihilators, so allowable torsion gives torsion of invertible order. Upstream smooth
base change therefore makes the bounded-below exchange invertible on sheaves in degree
zero. Apply the library's bounded triangulated dévissage to K and transport the result
through `abelianDerivedBaseChangeArrow_eq_plus` to the unbounded canonical arrow.
For the output assertion, qcqs higher direct images preserve allowable prime torsion.
Extend the algebraically closed stalk statement to separably closed stalks using the
proved field-extension comparison. Negative higher images vanish. Bounded dévissage
for the inverse image of the triangulated allowable-torsion subcategory then proves
allowable torsion of Rg_* K. Exact inverse image commutes with cohomology, and its stalk
comparison preserves annihilators. Thus the source has allowable-torsion cohomology.
The ambient exchange isomorphism transfers membership to the target. With the asserted
boundedness, form both objects of the full subcategory; its inclusion reflects
isomorphisms, proving the final clause. -/
theorem isIso_abelianDerivedBaseChangeArrow_of_bounded_allowable_torsion
    {X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (sq : ChosenCartesianSquare h e f g)
    (K : AbelianDerivedCategoryBoundedTorsionOfPrimes T S.invertiblePrimes) :
    IsIso (abelianDerivedBaseChangeArrow sq K.obj) ∧
      (DerivedCategory.TStructure.t.bounded
        (D(upperStar AddCommGrpCat.{u + 1} f).obj
          (R(lowerStar AddCommGrpCat.{u + 1} g).obj K.obj)) →
       DerivedCategory.TStructure.t.bounded
        (R(lowerStar AddCommGrpCat.{u + 1} h).obj
          (D(upperStar AddCommGrpCat.{u + 1} e).obj K.obj)) →
       ∃ hs : allowableTorsionBoundedProperty X S.invertiblePrimes
          (D(upperStar AddCommGrpCat.{u + 1} f).obj
          (R(lowerStar AddCommGrpCat.{u + 1} g).obj K.obj)),
       ∃ ht : allowableTorsionBoundedProperty X S.invertiblePrimes
          (R(lowerStar AddCommGrpCat.{u + 1} h).obj
          (D(upperStar AddCommGrpCat.{u + 1} e).obj K.obj)),
       IsIso (ObjectProperty.homMk
         (X := ⟨D(upperStar AddCommGrpCat.{u + 1} f).obj
          (R(lowerStar AddCommGrpCat.{u + 1} g).obj K.obj), hs⟩)
         (Y := ⟨R(lowerStar AddCommGrpCat.{u + 1} h).obj
          (D(upperStar AddCommGrpCat.{u + 1} e).obj K.obj), ht⟩)
         (abelianDerivedBaseChangeArrow sq K.obj))) := by
  let Kplus : _root_.DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) := ⟨K.obj, K.property.2.1⟩
  have hpull : IsPullback e h g f :=
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd).flip
  obtain ⟨a, b, hab⟩ :=
    (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded K.obj).2 K.property.2
  have : (allowableTorsionSheafProperty T S.invertiblePrimes).IsClosedUnderIsomorphisms :=
    ⟨fun e hF ↦ allowableTorsionSheafProperty_of_iso hF e⟩
  have : Kplus.IsGE a := (_root_.DerivedCategory.Plus.isGE_ι_obj_iff Kplus a).1 hab.1
  have : Kplus.IsLE b := (_root_.DerivedCategory.Plus.isLE_ι_obj_iff Kplus b).1 hab.2
  have hplus := _root_.DerivedCategory.Plus.isIso_app_of_bounded
    (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} hpull.toCommSq)
    (allowableTorsionSheafProperty T S.invertiblePrimes)
    (isIso_derivedBaseChangeMapPlus_single_of_allowable hpull) Kplus a b K.property.1
  have hamb : IsIso (abelianDerivedBaseChangeArrow sq K.obj) := by
    change IsIso (abelianDerivedBaseChangeArrow sq Kplus.obj)
    rw [abelianDerivedBaseChangeArrow_eq_plus]
    infer_instance
  refine ⟨hamb, ?_⟩
  intro hsource htarget
  have hsourceTor : _root_.DerivedCategory.homologyProperty
      (allowableTorsionSheafProperty X S.invertiblePrimes)
      (D(upperStar AddCommGrpCat.{u + 1} f).obj
        (R(lowerStar AddCommGrpCat.{u + 1} g).obj K.obj)) := by
    let P := S.invertiblePrimes
    let Q := (allowableTorsionPlusProperty S P).inverseImage
      R(lowerStar AddCommGrpCat.{u + 1} g)
    have hpush : allowableTorsionPlusProperty S P
        (R(lowerStar AddCommGrpCat.{u + 1} g).obj K.obj) :=
      _root_.DerivedCategory.prop_of_bounded Q (allowableTorsionSheafProperty T P)
        (allowableTorsionPlusProperty_rightDerived_single g P) K.obj
        K.property.2 K.property.1
    intro q
    apply allowableTorsionSheafProperty_of_iso
      (allowable_upperStar f P _ (hpush.1 q))
    exact ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryHomologyFunctorIso q).app _
  let hs : allowableTorsionBoundedProperty X S.invertiblePrimes
      (D(upperStar AddCommGrpCat.{u + 1} f).obj
        (R(lowerStar AddCommGrpCat.{u + 1} g).obj K.obj)) := ⟨hsourceTor, hsource⟩
  let ht := (allowableTorsionBoundedProperty X S.invertiblePrimes).prop_of_iso
    (asIso (abelianDerivedBaseChangeArrow sq K.obj)) hs
  refine ⟨hs, ht, ?_⟩
  exact (ObjectProperty.isIso_hom_iff _).1 hamb

end AlgebraicGeometry.Etale
