/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate
import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenSheafComparison
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import Mathlib.Algebra.Ring.Shrink
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful

/-!
# Invertibility of the finite direct-image/open-extension mate

Source: Stacks Tag 0F7B, proper/open support; the finite case is computed termwise
using exactness of finite direct image on the pro-etale site.
(blueprint: lem-trf-finite-horizontal-open-proper-mate-invertible)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

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

private def intrinsic_open_sheaf_comparison
    (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Scheme.sfIntrinsicModuleEquivalence U A).functor ⋙
        Scheme.sfIntrinsicExtensionByZero j A ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        (Scheme.sfIntrinsicModuleEquivalence X A).functor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Scheme.sfIntrinsicModuleEquivalence U A).unitIso.symm _ ≪≫
    Functor.leftUnitor _

private def intrinsic_open_adj
    (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Scheme.sfIntrinsicExtensionByZero j A ⊣ Scheme.sfIntrinsicPullback A j :=
  ((Scheme.sfIntrinsicModuleEquivalence U A).symm.toAdjunction.comp
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)).comp
    (Scheme.sfIntrinsicModuleEquivalence X A).toAdjunction

private def intrinsic_open_comp
    (A : Type u) [CommRing A] [Finite A]
    {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    Scheme.sfIntrinsicExtensionByZero (i ≫ j) A ≅
      Scheme.sfIntrinsicExtensionByZero i A ⋙ Scheme.sfIntrinsicExtensionByZero j A :=
  (((intrinsic_open_adj A i).comp (intrinsic_open_adj A j)).ofNatIsoRight
    (Scheme.sfIntrinsicPullbackComp A i j).symm).leftAdjointUniq
      (intrinsic_open_adj A (i ≫ j)) |>.symm

private theorem intrinsic_sheaf_support
    (A : Type u) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : Scheme.proEtaleRingModules U (Scheme.proEtaleConstantRing U A)) :
    IsIso ((Scheme.sfIntrinsicExtensionByZeroAdjunction i A).counit.app
      ((Scheme.proEtaleConstantModuleDirectImage p A).obj
        ((Scheme.sfIntrinsicExtensionByZero k A).obj M))) := by
  let s := pullback.lift k r h
  have hs : s ≫ pullback.fst p i = k := pullback.lift_fst _ _ _
  have : IsOpenImmersion (s ≫ pullback.fst p i) := by rw [hs]; infer_instance
  have : IsOpenImmersion s := IsOpenImmersion.of_comp s (pullback.fst p i)
  let N := (Scheme.sfIntrinsicExtensionByZero s A).obj M
  let e : (Scheme.sfIntrinsicExtensionByZero k A).obj M ≅
      (Scheme.sfIntrinsicExtensionByZero (pullback.fst p i) A).obj N := by
    simpa only [hs, Functor.comp_obj] using
      (intrinsic_open_comp A s (pullback.fst p i)).app M
  have := Scheme.sfProperOpenCounit_isIso A p i N
  have : (Scheme.sfIntrinsicExtensionByZero i A).Full := by
    unfold Scheme.sfIntrinsicExtensionByZero
    infer_instance
  have : (Scheme.sfIntrinsicExtensionByZero i A).Faithful := by
    unfold Scheme.sfIntrinsicExtensionByZero
    infer_instance
  apply (Scheme.sfIntrinsicExtensionByZeroAdjunction i A).isIso_counit_app_of_iso
  exact (Scheme.proEtaleConstantModuleDirectImage p A).mapIso e ≪≫
    (asIso ((Scheme.sfIntrinsicExtensionByZeroAdjunction i A).counit.app
      ((Scheme.sfIntrinsicExtensionByZero (pullback.fst p i) A ⋙
        Scheme.proEtaleConstantModuleDirectImage p A).obj N))).symm

private theorem ulift_sheaf_support
    (A : Type u) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    IsIso ((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).counit.app
      ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) k).obj M))) := by
  let eU := Scheme.sfIntrinsicModuleEquivalence U A
  let eW := Scheme.sfIntrinsicModuleEquivalence W A
  let eZ := Scheme.sfIntrinsicModuleEquivalence Z A
  let P := Scheme.proEtaleConstantModuleDirectImage p A
  let N := P.obj ((Scheme.sfIntrinsicExtensionByZero k A).obj (eU.functor.obj M))
  have hs := intrinsic_sheaf_support A k r p i h (eU.functor.obj M)
  let d : eZ.functor.obj
      ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) k).obj M)) ≅ N :=
    ((Scheme.sfIntrinsicDirectImageComparison p A).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) k).obj M)).symm ≪≫
      P.mapIso ((intrinsic_open_sheaf_comparison A k).app M).symm
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).unit := inferInstance
  have : IsIso ((Scheme.sfIntrinsicExtensionByZeroAdjunction i A).counit.app N) := hs
  exact supported_of_equivalence
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i)
    eW eZ (Scheme.sfIntrinsicExtensionByZero i A)
    (intrinsic_open_sheaf_comparison A i).symm _
    ((Scheme.sfIntrinsicOpenRestriction i A).obj N)
    (d ≪≫ (asIso ((Scheme.sfIntrinsicExtensionByZeroAdjunction i A).counit.app N)).symm)

private theorem ordinary_sheaf_support
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A)) :
    IsIso ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i).counit.app
      ((lowerStar (ModuleCat.{u + 1} A) p).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).obj M))) := by
  let B := Shrink.{u} A
  let e : ULift.{u + 1, u} B ≃+* A := (ULift.ringEquiv : ULift.{u + 1, u} B ≃+* B).trans
    (Shrink.ringEquiv.{u} A)
  let EU := coefficient_sheaf_equivalence e U
  let EW := coefficient_sheaf_equivalence e W
  let EZ := coefficient_sheaf_equivalence e Z
  let N := (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) p).obj
    ((openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) k).obj
      (EU.functor.obj M))
  have hs := ulift_sheaf_support B k r p i h (EU.functor.obj M)
  let pp : (coefficient_sheaf_equivalence e V).functor ⋙
      lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) p ≅
    lowerStar (ModuleCat.{u + 1} A) p ⋙ EZ.functor := Iso.refl _
  let d : EZ.functor.obj ((lowerStar (ModuleCat.{u + 1} A) p).obj
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).obj M)) ≅ N :=
    (pp.app ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).obj M)).symm ≪≫
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) p).mapIso
        ((coefficient_open_comparison e k).app M).symm
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i).unit :=
    inferInstance
  have : IsIso ((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) i).counit.app N) := hs
  exact supported_of_equivalence
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i) EW EZ
    (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) i)
    (coefficient_open_comparison e i).symm _
    ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) i).obj N)
    (d ≪≫ (asIso ((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) i).counit.app N)).symm)

private theorem ordinary_derived_support
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsFinite p] [LocallyOfFinitePresentation p]
    (h : k ≫ p = r ≫ i)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A))) :
    IsIso ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction
        (ModuleCat.{u + 1} A) i).counit.app
      ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj M))) := by
  let J := openImmersionLowerShriek (ModuleCat.{u + 1} A) i
  let P := upperStar (ModuleCat.{u + 1} A) i
  let B := lowerStar (ModuleCat.{u + 1} A) p
  let K := openImmersionLowerShriek (ModuleCat.{u + 1} A) k
  have : PreservesFiniteColimits B := preservesFiniteColimits_lowerStar_of_isFinite A p
  let L := DerivedCategory.Q.objPreimage M
  let C := (B.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((K.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
  have hc : ∀ n : ℤ, IsIso
      ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i).counit.app
        (C.X n)) := fun n ↦ ordinary_sheaf_support A k r p i h (L.X n)
  have hs := derived_support_of_complex J P
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i) C hc
  let e : B.rightDerivedFunctor.obj (K.mapDerivedCategory.obj M) ≅ DerivedCategory.Q.obj C :=
    B.rightDerivedFunctor.mapIso (K.mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso M).symm) ≪≫
    (B.rightDerivedFunctorIsoMapDerivedCategory.app _ ) ≪≫
    B.mapDerivedCategory.mapIso (K.mapDerivedCategoryFactors.app L) ≪≫
    B.mapDerivedCategoryFactors.app _
  have hd : IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) i).counit.app
      (B.rightDerivedFunctor.obj (K.mapDerivedCategory.obj M))) :=
    (NatTrans.isIso_app_iff_of_iso
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i).counit e).mpr hs
  change IsIso (((derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) i).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) i).symm).counit.app _)
  rw [Adjunction.ofNatIsoRight_counit]
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Iso.symm_hom]
  infer_instance

private theorem open_unit_isIso
    (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).unit := by
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).unit := inferInstance
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  rw [derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction,
    Adjunction.ofNatIsoRight_unit]
  infer_instance

/-- The mate of the specified derived open base-change isomorphism is invertible when
its ambient vertical map is finite and locally of finite presentation.
Source: Stacks Tag 0F7B, proper/open comparison, and exact finite pro-etale direct image.
(blueprint: lem-trf-finite-horizontal-open-proper-mate-invertible)

Proof: proper sheaf direct image of an open extension is supported on the target open.
Factor the source open through the Cartesian pullback of the target open, and use the
proper/open sheaf counit there. Canonical realization equivalences and a shrink of the
finite coefficient ring carry this support to fixed-scalar sheaves. Finite direct image
is exact, so the support holds termwise on every complex and hence after localization.
The two open units are invertible. The generic iterated-mate criterion, applied with
the supported target counit, now makes each component of the specified mate invertible. -/
theorem finiteHorizontalOpenProperMate_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}} {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
    [IsOpenImmersion k] [IsOpenImmersion i] [IsFinite p] [LocallyOfFinitePresentation p]
    (sq : IsPullback r k i p) :
    IsIso ((mateEquiv
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (leftDerivedOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) sq).inv).natTrans) := by
  have : IsIso (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction
      (ModuleCat.{u + 1} A) i).unit := open_unit_isIso A i
  have : IsIso (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction
      (ModuleCat.{u + 1} A) k).unit := open_unit_isIso A k
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro M
  have := ordinary_derived_support A k r p i sq.w.symm M
  exact Adjunction.isIso_mateEquiv_app_of_isIso
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (leftDerivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A) sq).symm
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction (ModuleCat.{u + 1} A) i)
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction (ModuleCat.{u + 1} A) k) M

end AlgebraicGeometry.ProEtale
