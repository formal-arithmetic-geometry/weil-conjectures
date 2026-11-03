/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenProjectionMate
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
import WeilConjectures.AlgebraicGeometry.ProperOpenSquareSupport.ProperOpenSquareDerivedSupport
import all WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import Mathlib.Algebra.Ring.Shrink

/-! # Invertibility of the ordinary proper/open mate

Source: Stacks 0F7B, the support argument for a proper/open square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale

private theorem open_unit_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (properOpenAdj A j).unit := by
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).unit := inferInstance
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  rw [properOpenAdj, Adjunction.ofNatIsoRight_unit]
  infer_instance

-- Support is membership in the essential image, so no equality of chosen adjunctions
-- is needed when transferring it through coefficient equivalences.
private theorem supported_of_equivalence
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {J : C ⥤ D} {P : D ⥤ C} (a : J ⊣ P) [IsIso a.unit]
    (F : C ≌ C') (G : D ≌ D') (j : C' ⥤ D')
    (sq : J ⋙ G.functor ≅ F.functor ⋙ j)
    (M : D) (N : C') (e : G.functor.obj M ≅ j.obj N) :
    IsIso (a.counit.app M) := by
  let ff := a.fullyFaithfulLOfIsIsoUnit
  have : J.Full := ff.full
  have : J.Faithful := ff.faithful
  apply a.isIso_counit_app_of_iso
  exact G.functor.preimageIso
    (e ≪≫ j.mapIso (F.counitIso.app N).symm ≪≫ (sq.app (F.inverse.obj N)).symm)

private def intrinsic_open_comparison
    (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Scheme.sfIntrinsicDerivedEquivalence U A).functor ⋙ Scheme.sfIntrinsicDerivedOpen A j ≅
      ProperOpenShriek (ULift.{u + 1, u} A) j ⋙
        (Scheme.sfIntrinsicDerivedEquivalence X A).functor := by
  let EU := Scheme.sfIntrinsicModuleEquivalence U A
  let EX := Scheme.sfIntrinsicModuleEquivalence X A
  let L := openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j
  let e : EU.functor ⋙ Scheme.sfIntrinsicExtensionByZero j A ≅ L ⋙ EX.functor :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight EU.unitIso.symm _ ≪≫ Functor.leftUnitor _
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso _ _

private theorem ulift_support
    (A : Type u) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : ProperOpenDerived (ULift.{u + 1, u} A) U) :
    IsIso ((properOpenAdj (ULift.{u + 1, u} A) i).counit.app
      ((ProperOpenPush (ULift.{u + 1, u} A) p).obj
        ((ProperOpenShriek (ULift.{u + 1, u} A) k).obj M))) := by
  let eU := Scheme.sfIntrinsicDerivedEquivalence U A
  let eW := Scheme.sfIntrinsicDerivedEquivalence W A
  let eZ := Scheme.sfIntrinsicDerivedEquivalence Z A
  let P := Scheme.proEtaleConstantDerivedDirectImage p A
  let N := P.obj ((Scheme.sfIntrinsicDerivedOpen A k).obj (eU.functor.obj M))
  have hs := Scheme.ProperOpenSquareSupport.derived_support_square p k i r h A
    (eU.functor.obj M)
  let d : eZ.functor.obj ((ProperOpenPush (ULift.{u + 1, u} A) p).obj
      ((ProperOpenShriek (ULift.{u + 1, u} A) k).obj M)) ≅ N :=
    ((Scheme.sfIntrinsicDerivedDirectImageComparison p A).app
      ((ProperOpenShriek (ULift.{u + 1, u} A) k).obj M)).symm ≪≫
      P.mapIso ((intrinsic_open_comparison A k).app M).symm
  have : IsIso (properOpenAdj (ULift.{u + 1, u} A) i).unit := open_unit_isIso _ i
  have : IsIso ((Scheme.exceptionalOpenAdjunction i A).counit.app N) := hs
  exact supported_of_equivalence (properOpenAdj (ULift.{u + 1, u} A) i)
    eW eZ (Scheme.sfIntrinsicDerivedOpen A i) (intrinsic_open_comparison A i).symm
    _ ((Scheme.sfIntrinsicDerivedPullback A i).obj N)
    (d ≪≫ (asIso ((Scheme.exceptionalOpenAdjunction i A).counit.app N)).symm)

private def coefficient_sheaf_equivalence
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (e : B ≃+* A) (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ≌
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B) := by
  let E : ModuleCat.{u + 1} A ≌ ModuleCat.{u + 1} B :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  have : (sheafCompose (Scheme.ProEt.topology X) E.functor).IsEquivalence :=
    isEquivalence_sheafCompose_of_isEquivalence _ E.functor
  exact (sheafCompose (Scheme.ProEt.topology X) E.functor).asEquivalence

private instance coefficient_sheaf_equivalence_additive
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (e : B ≃+* A) (X : Scheme.{u}) :
    (coefficient_sheaf_equivalence e X).functor.Additive := by
  change (sheafCompose (Scheme.ProEt.topology X)
    (ModuleCat.restrictScalars.{u + 1} e.toRingHom)).Additive
  infer_instance

private def coefficient_open_comparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (e : B ≃+* A)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (coefficient_sheaf_equivalence e U).functor ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} B) j ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⋙
        (coefficient_sheaf_equivalence e X).functor := by
  let E : ModuleCat.{u + 1} A ≌ ModuleCat.{u + 1} B :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let TU := (coefficient_sheaf_equivalence e U).functor
  let TX := (coefficient_sheaf_equivalence e X).functor
  let au := sheafComposeAdjunction (Scheme.ProEt.topology U) E.toAdjunction
  let ax := sheafComposeAdjunction (Scheme.ProEt.topology X) E.toAdjunction
  let a₁ := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).comp au
  let a₂ := ax.comp (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j)
  let r : upperStar (ModuleCat.{u + 1} A) j ⋙ TU ≅
      TX ⋙ upperStar (ModuleCat.{u + 1} B) j :=
    (conjugateIsoEquiv a₂ a₁).symm (Iso.refl _)
  let b₁ := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let b₂ := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  have := isIso_inverseMate_of_equivalences b₁ b₂ r
  exact asIso (((mateEquiv b₁ b₂).symm r.hom).natTrans)

-- Shrinking the finite coefficient ring lets the intrinsic support theorem apply
-- without changing the scheme or module universes.
private theorem ordinary_support
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : ProperOpenDerived A U) :
    IsIso ((properOpenAdj A i).counit.app
      ((ProperOpenPush A p).obj ((ProperOpenShriek A k).obj M))) := by
  let B := Shrink.{u} A
  let e : ULift.{u + 1, u} B ≃+* A := (ULift.ringEquiv : ULift.{u + 1, u} B ≃+* B).trans
    (Shrink.ringEquiv.{u} A)
  let EU := coefficient_sheaf_equivalence e U
  let EV := coefficient_sheaf_equivalence e V
  let EW := coefficient_sheaf_equivalence e W
  let EZ := coefficient_sheaf_equivalence e Z
  let dU := EU.mapDerivedCategory
  let dW := EW.mapDerivedCategory
  let dZ := EZ.mapDerivedCategory
  let jk := Functor.mapDerivedCategorySquareIso (coefficient_open_comparison e k)
  let ji := Functor.mapDerivedCategorySquareIso (coefficient_open_comparison e i)
  obtain ⟨pp, _⟩ := intrinsicDerivedSquare EV.functor EZ.functor
    (lowerStar (ModuleCat.{u + 1} A) p)
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) p) (Iso.refl _)
  let N := (ProperOpenPush (ULift.{u + 1, u} B) p).obj
    ((ProperOpenShriek (ULift.{u + 1, u} B) k).obj (dU.functor.obj M))
  have hs := ulift_support B k r p i h (dU.functor.obj M)
  let d : dZ.functor.obj ((ProperOpenPush A p).obj ((ProperOpenShriek A k).obj M)) ≅ N :=
    (pp.app ((ProperOpenShriek A k).obj M)).symm ≪≫
      (ProperOpenPush (ULift.{u + 1, u} B) p).mapIso (jk.app M).symm
  have : IsIso (properOpenAdj A i).unit := open_unit_isIso A i
  have : IsIso ((properOpenAdj (ULift.{u + 1, u} B) i).counit.app N) := hs
  exact supported_of_equivalence (properOpenAdj A i) dW dZ
    (ProperOpenShriek (ULift.{u + 1, u} B) i) ji.symm _
    ((ProperOpenPull (ULift.{u + 1, u} B) i).obj N)
    (d ≪≫ (asIso ((properOpenAdj (ULift.{u + 1, u} B) i).counit.app N)).symm)

set_option maxRecDepth 2048 in
private theorem mate_app_isIso_of_support
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : ProperOpenDerived A U)
    (hs : IsIso ((properOpenAdj A i).counit.app
      ((ProperOpenPush A p).obj ((ProperOpenShriek A k).obj M)))) :
    IsIso ((properOpenMate A k r p i h).app M) := by
  let s := StrictTower.squareLift k r p i h
  let b := CategoryTheory.Limits.pullback.fst p i
  let q := CategoryTheory.Limits.pullback.snd p i
  let ar := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r
  let ap := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p
  let aq := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q
  let ass := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s
  let ai := properOpenAdj A i
  let ab := properOpenAdj A b
  have : IsIso ab.unit := open_unit_isIso A b
  let β := properOpenBeta A q b i p
    (CategoryTheory.IsPullback.of_hasPullback p i).flip
  let d : ProperOpenShriek A s ⋙ ProperOpenShriek A b ≅ ProperOpenShriek A k :=
    properOpenShriekComp A s b ≪≫ properOpenShriekCongr A
      (CategoryTheory.Limits.pullback.lift_fst k r h)
  let e : ProperOpenPull A r ≅ ProperOpenPull A q ⋙ ProperOpenPull A s :=
    (leftDerivedUpperStarCongr (ModuleCat.{u + 1} A)
      (CategoryTheory.Limits.pullback.lift_snd k r h)).symm ≪≫
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s q
  let t : ProperOpenShriek A s ≅ ProperOpenPush A s :=
    (rightDerivedLowerStarIsoOfIsClosedRange (ModuleCat.{u + 1} A) s
      s.isClosedEmbedding.isClosed_range).symm
  -- Use the adjunction conjugate itself; no comparison of chosen push compositors is needed.
  let δ := conjugateIsoEquiv (aq.comp ass) ar e
  let f : (ProperOpenPull A q).obj ((ProperOpenPush A r).obj M) ⟶
      (ProperOpenShriek A s).obj M :=
    (properOpenClopenProjection A s).app _ ≫ (ProperOpenShriek A s).map
      (e.inv.app ((ProperOpenPush A r).obj M) ≫ ar.counit.app M)
  have hα : properOpenAlpha A k r p i h =
      SemilinearProperOpenCoreAliases.projection_square β d e
        (properOpenClopenProjection A s) := by
    rfl
  have hword := SemilinearProperOpenCoreAliases.projection_square_formula_of_eq
    β d e (properOpenClopenProjection A s) (properOpenAlpha A k r p i h) hα
    ((ProperOpenPush A r).obj M) M (ar.counit.app M)
  have hf : f ≫ t.hom.app M = ass.unit.app _ ≫ (ProperOpenPush A s).map
      (e.inv.app ((ProperOpenPush A r).obj M) ≫ ar.counit.app M) := by
    have hn := t.hom.naturality
      (e.inv.app ((ProperOpenPush A r).obj M) ≫ ar.counit.app M)
    simp only [Functor.id_obj] at hn
    dsimp only [f, properOpenClopenProjection, NatTrans.comp_app,
      Functor.whiskerLeft_app]
    change ((ass.unit.app _ ≫ t.inv.app _) ≫ (ProperOpenShriek A s).map _) ≫
      t.hom.app M = _
    simp only [Functor.comp_obj] at hn ⊢
    simp only [Category.assoc]
    rw [hn, ← Category.assoc (t.inv.app _),
      t.inv_hom_id_app, Category.id_comp]
  let comparison := SemilinearProperOpenCoreAliases.adjunct_comparison ap ai ab aq β d t δ
  have hmain : ai.homEquiv _ _ ((properOpenMate A k r p i h).app M) ≫
      comparison.hom.app M = 𝟙 _ :=
    SemilinearProperOpenCoreAliases.adjunct_comparison_identity ar ap ai ab aq ass
      β d e t δ rfl (properOpenAlpha A k r p i h) M f hword hf
  have he := (SemilinearProperOpenCoreAliases.homEquiv_iso_inverse ai
    ((properOpenMate A k r p i h).app M) (comparison.app M) hmain).1
  have hm := congrArg (ai.homEquiv _ _).symm he
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] at hm
  rw [hm]
  have : IsIso (ai.counit.app
      ((ProperOpenShriek A k ⋙ ProperOpenPush A p).obj M)) := hs
  infer_instance

/-- The canonical proper/open mate is invertible on arbitrary unbounded inputs.
Source: Stacks 0F7B
(blueprint: lem-sf-ordinary-proper-open-invertibility).

Proof: factor the source open through the Cartesian pullback of the target open.
The resulting lift is clopen: it is open by cancellation, and proper by cancellation
against the separated proper map. Proper/open support shows that the proper image
of an open extension lies in the essential image of target extension by zero.
For sheaves this follows from the Cartesian proper/open comparison; injective
acyclicity gives it for bounded-below complexes. Exact countable products and
lower Postnikov completeness extend support to arbitrary complexes. The canonical
mate's open adjunct is inverse lambda, where lambda is obtained by restricting
proper image, identifying the clopen extension with direct image, and composing
direct images. The inverse Hom bijection expresses this mate as extension of
inverse lambda followed by the supported open counit. Both factors are invertible.
-/
theorem ordinaryProperOpenMateIsIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    IsIso (properOpenMate A k r p i h) := by
  have hi (M : ProperOpenDerived A U) : IsIso ((properOpenMate A k r p i h).app M) := by
    apply mate_app_isIso_of_support A k r p i h M
    exact ordinary_support A k r p i h M
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.ProEtale
