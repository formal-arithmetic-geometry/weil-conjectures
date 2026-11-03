/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.SepFinType
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenSheafComparison
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.InverseMateEquivalence
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite

/-!
# Finite-horizontal compact-support exchange and ordinary units

This is the statement node `lem-trf-finite-horizontal-shriek-mate-general`.  The coefficient
ring is used through the ordinary constant pro-etale module categories (the discrete condensed
ring has pullback `A_T = p_T^* A`).  The composition comparison is the normalized
ordinary finite-coefficient compact-support comparison of formula (C); its proof is postponed.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-frobenius-and-rf/sk-i-relative-frob/sk-i-relative-frob.proof.md, item (3),
“Since base change is compatible with these units”; Stacks Tags 0F7L and 0F7J.
Proof steps: expand the compactification into open and proper parts; identify the proper/open
comparison; compute the independent open/proper interchange; compose the proper direct images
with their canonical compositor; transport along finite-ring etale origin; apply naturality and
triangles; conclude by the hom-bijection characterization of the inverse square mate.
(blueprint: lem-trf-finite-horizontal-shriek-mate-general)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

private theorem fh_supported_of_equivalence
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

private def fh_coefficient_sheaf_equivalence
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (e : B ≃+* A) (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ≌
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B) := by
  let E : ModuleCat.{u + 1} A ≌ ModuleCat.{u + 1} B :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  have : (sheafCompose (Scheme.ProEt.topology X) E.functor).IsEquivalence :=
    isEquivalence_sheafCompose_of_isEquivalence _ E.functor
  exact (sheafCompose (Scheme.ProEt.topology X) E.functor).asEquivalence

private instance fh_coefficient_sheaf_equivalence_additive
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (e : B ≃+* A) (X : Scheme.{u}) :
    (fh_coefficient_sheaf_equivalence e X).functor.Additive := by
  change (sheafCompose (Scheme.ProEt.topology X)
    (ModuleCat.restrictScalars.{u + 1} e.toRingHom)).Additive
  infer_instance

private def fh_coefficient_open_comparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (e : B ≃+* A)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (fh_coefficient_sheaf_equivalence e U).functor ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} B) j ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⋙
        (fh_coefficient_sheaf_equivalence e X).functor := by
  let E : ModuleCat.{u + 1} A ≌ ModuleCat.{u + 1} B :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let TU := (fh_coefficient_sheaf_equivalence e U).functor
  let TX := (fh_coefficient_sheaf_equivalence e X).functor
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

private def fh_intrinsic_open_sheaf_comparison
    (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Scheme.sfIntrinsicModuleEquivalence U A).functor ⋙
        Scheme.sfIntrinsicExtensionByZero j A ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        (Scheme.sfIntrinsicModuleEquivalence X A).functor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Scheme.sfIntrinsicModuleEquivalence U A).unitIso.symm _ ≪≫
    Functor.leftUnitor _

private def fh_intrinsic_open_adj
    (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Scheme.sfIntrinsicExtensionByZero j A ⊣ Scheme.sfIntrinsicPullback A j :=
  ((Scheme.sfIntrinsicModuleEquivalence U A).symm.toAdjunction.comp
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)).comp
    (Scheme.sfIntrinsicModuleEquivalence X A).toAdjunction

private def fh_intrinsic_open_comp
    (A : Type u) [CommRing A] [Finite A]
    {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    Scheme.sfIntrinsicExtensionByZero (i ≫ j) A ≅
      Scheme.sfIntrinsicExtensionByZero i A ⋙ Scheme.sfIntrinsicExtensionByZero j A :=
  (((fh_intrinsic_open_adj A i).comp (fh_intrinsic_open_adj A j)).ofNatIsoRight
    (Scheme.sfIntrinsicPullbackComp A i j).symm).leftAdjointUniq
      (fh_intrinsic_open_adj A (i ≫ j)) |>.symm

private theorem fh_intrinsic_sheaf_support
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
      (fh_intrinsic_open_comp A s (pullback.fst p i)).app M
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

private theorem fh_ulift_sheaf_support
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
  have hs := fh_intrinsic_sheaf_support A k r p i h (eU.functor.obj M)
  let d : eZ.functor.obj
      ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) k).obj M)) ≅ N :=
    ((Scheme.sfIntrinsicDirectImageComparison p A).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) k).obj M)).symm ≪≫
      P.mapIso ((fh_intrinsic_open_sheaf_comparison A k).app M).symm
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).unit := inferInstance
  have : IsIso ((Scheme.sfIntrinsicExtensionByZeroAdjunction i A).counit.app N) := hs
  exact fh_supported_of_equivalence
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i)
    eW eZ (Scheme.sfIntrinsicExtensionByZero i A)
    (fh_intrinsic_open_sheaf_comparison A i).symm _
    ((Scheme.sfIntrinsicOpenRestriction i A).obj N)
    (d ≪≫ (asIso ((Scheme.sfIntrinsicExtensionByZeroAdjunction i A).counit.app N)).symm)

private theorem fh_ordinary_sheaf_support
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
  let EU := fh_coefficient_sheaf_equivalence e U
  let EW := fh_coefficient_sheaf_equivalence e W
  let EZ := fh_coefficient_sheaf_equivalence e Z
  let N := (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) p).obj
    ((openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) k).obj
      (EU.functor.obj M))
  have hs := fh_ulift_sheaf_support B k r p i h (EU.functor.obj M)
  let pp : (fh_coefficient_sheaf_equivalence e V).functor ⋙
      lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) p ≅
    lowerStar (ModuleCat.{u + 1} A) p ⋙ EZ.functor := Iso.refl _
  let d : EZ.functor.obj ((lowerStar (ModuleCat.{u + 1} A) p).obj
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).obj M)) ≅ N :=
    (pp.app ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).obj M)).symm ≪≫
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) p).mapIso
        ((fh_coefficient_open_comparison e k).app M).symm
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i).unit :=
    inferInstance
  have : IsIso ((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) i).counit.app N) := hs
  exact fh_supported_of_equivalence
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i) EW EZ
    (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) i)
    (fh_coefficient_open_comparison e i).symm _
    ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) i).obj N)
    (d ≪≫ (asIso ((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) i).counit.app N)).symm)

private theorem fh_derived_support_of_complex
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    (adj : F ⊣ G) [F.Full] [F.Faithful]
    (adjD : F.mapDerivedCategory ⊣ G.mapDerivedCategory)
    (L : CochainComplex D ℤ)
    (hL : ∀ n : ℤ, IsIso (adj.counit.app (L.X n))) :
    IsIso (adjD.counit.app (DerivedCategory.Q.obj L)) := by
  have : IsIso adj.unit := inferInstance
  have ff := adjD.fullyFaithfulLOfCompIsoId
    ((Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso adj.unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso C)
  have := ff.full
  have := ff.faithful
  let C := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let φ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (C.obj L) ⟶ L :=
    { f n := adj.counit.app (L.X n)
      comm' _ _ _ := (adj.counit.naturality _).symm }
  have : ∀ n : ℤ, IsIso (φ.f n) := hL
  have : IsIso φ := HomologicalComplex.Hom.isIso_of_components φ
  apply adjD.isIso_counit_app_of_iso
  exact ((F.mapDerivedCategoryFactors.app (C.obj L)) ≪≫
    DerivedCategory.Q.mapIso (asIso φ)).symm

private theorem fh_ordinary_derived_support
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
        (C.X n)) := fun n ↦ fh_ordinary_sheaf_support A k r p i h (L.X n)
  have hs := fh_derived_support_of_complex J P
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

private theorem fh_open_unit_isIso
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
(blueprint: lem-trf-finite-horizontal-shriek-mate-general)

Proof: proper sheaf direct image of an open extension is supported on the target open.
Factor the source open through the Cartesian pullback of the target open, and use the
proper/open sheaf counit there. Canonical realization equivalences and a shrink of the
finite coefficient ring carry this support to fixed-scalar sheaves. Finite direct image
is exact, so the support holds termwise on every complex and hence after localization.
The two open units are invertible. The generic iterated-mate criterion, applied with
the supported target counit, now makes each component of the specified mate invertible. -/
private theorem fh_finiteHorizontalOpenProperMate_isIso
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
      (ModuleCat.{u + 1} A) i).unit := fh_open_unit_isIso A i
  have : IsIso (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction
      (ModuleCat.{u + 1} A) k).unit := fh_open_unit_isIso A k
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro M
  have := fh_ordinary_derived_support A k r p i sq.w.symm M
  exact Adjunction.isIso_mateEquiv_app_of_isIso
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (leftDerivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A) sq).symm
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction (ModuleCat.{u + 1} A) i)
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction (ModuleCat.{u + 1} A) k) M

/-- The canonical open/proper interchange used by the compact-support composition comparison.
It is the mate of the specified derived open-extension base-change isomorphism, independently
of the compact-support exchange. It is the map `γ` of formula (C) and equation (O) of the
node proof.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-frobenius-and-rf/sk-i-relative-frob/sk-i-relative-frob.proof.md,
item (3), formula (C); Stacks Tags 0F7B (lemma-shriek-proper-and-open) and 0F7J
(identity-open proper normalization).
(blueprint: lem-trf-finite-horizontal-shriek-mate-general) -/
noncomputable def finiteHorizontalOpenProperGamma
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y X' Y' : SepFinType k}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (pmap : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback pmap.hom.left f'.hom.left f.hom.left g.hom.left)
    [AlgebraicGeometry.IsFinite g.hom.left]
    (c : Compactification f.hom.left) :
    let q : (c.ofIsPullback sq).Z ⟶ c.Z := pullback.fst c.g g.hom.left
    R((pmap.hom.left)_*[ModuleCat.{u + 1} A]) ⋙
        D((c.i)_!open[ModuleCat.{u + 1} A]) ⟶
      D(((c.ofIsPullback sq).i)_!open[ModuleCat.{u + 1} A]) ⋙
        R((q)_*[ModuleCat.{u + 1} A]) := by
  let q : (c.ofIsPullback sq).Z ⟶ c.Z := pullback.fst c.g g.hom.left
  let α := TwoSquare.mk _ _ _ _
    ((leftDerivedOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} A) (c.isPullback_i_ofIsPullback sq)).inv)
  exact (mateEquiv
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) pmap.hom.left)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q) α).natTrans

/-- The specified direct-image compositor for a commuting proper-part square. It is the
first direct-image composition isomorphism, the transport along the square equation, and the
inverse of the second composition isomorphism, in that order. No exchange map enters this
construction.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-frobenius-and-rf/sk-i-relative-frob/sk-i-relative-frob.proof.md, item (3), formula (C);
Stacks Tag 0F7J, proper-input composition.
(blueprint: lem-trf-finite-horizontal-shriek-mate-general) -/
noncomputable def finiteHorizontalProperSigma
    (A : Type (u + 1)) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {q : X' ⟶ X} {b' : X' ⟶ Y'} {b : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq q b' b g) :
    R((q)_*[ModuleCat.{u + 1} A]) ⋙ R((b)_*[ModuleCat.{u + 1} A]) ⟶
      R((b')_*[ModuleCat.{u + 1} A]) ⋙ R((g)_*[ModuleCat.{u + 1} A]) :=
  (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) q b).hom ≫
    eqToHom (congrArg (fun a ↦ R((a)_*[ModuleCat.{u + 1} A])) sq.w) ≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) b' g).inv

/-- The canonical finite-horizontal compact-support composition comparison. It is formula (C):
first apply the specified open/proper interchange, then compose the two proper direct images
using `rightDerivedLowerStarComp`; no exchange map is used to define it.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-frobenius-and-rf/sk-i-relative-frob/sk-i-relative-frob.proof.md,
item (3), formula (C); Stacks Tag 0F7J (lemma-shriek-composition), proper-input case.
(blueprint: lem-trf-finite-horizontal-shriek-mate-general) -/
noncomputable def finiteHorizontalShriekCompositionMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y X' Y' : SepFinType k}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (pmap : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback pmap.hom.left f'.hom.left f.hom.left g.hom.left)
    [AlgebraicGeometry.IsFinite g.hom.left]
    (c : Compactification f.hom.left) :
    R((pmap.hom.left)_*[ModuleCat.{u + 1} A]) ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⟶
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) (c.ofIsPullback sq) ⋙
        R((g.hom.left)_*[ModuleCat.{u + 1} A]) := by
  let q : (c.ofIsPullback sq).Z ⟶ c.Z := pullback.fst c.g g.hom.left
  let sp : CommSq q (c.ofIsPullback sq).g c.g g.hom.left :=
    (c.isPullback_g_ofIsPullback sq).flip.toCommSq
  let γ := finiteHorizontalOpenProperGamma A k f f' pmap g sq c
  let σ := finiteHorizontalProperSigma A sp
  exact (TwoSquare.vComp (TwoSquare.mk _ _ _ _ γ) (TwoSquare.mk _ _ _ _ σ)).natTrans

/-- The open/proper comparison and the direct-image compositor in formula (C) are the
normalized compact-support composition isomorphism.  Its invertibility is the finite-level
compact-support composition assertion of `sk-thm-sf-comp-composition`; the proof is postponed.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-frobenius-and-rf/sk-i-relative-frob/sk-i-relative-frob.proof.md,
item (3), formula (C); Stacks Tags 0F7J and 0F7L.
(blueprint: lem-trf-finite-horizontal-shriek-mate-general) -/
theorem finiteHorizontalShriekCompositionMap_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y X' Y' : SepFinType k}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (pmap : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback pmap.hom.left f'.hom.left f.hom.left g.hom.left)
    [AlgebraicGeometry.IsFinite g.hom.left]
    (c : Compactification f.hom.left) :
    IsIso (finiteHorizontalShriekCompositionMap A k f f' pmap g sq c) := by
  have : IsLocallyNoetherian Y.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian Y.obj.hom
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : AlgebraicGeometry.IsFinite (pullback.fst c.g g.hom.left) := inferInstance
  have hγ : IsIso (finiteHorizontalOpenProperGamma A k f f' pmap g sq c) :=
    fh_finiteHorizontalOpenProperMate_isIso A (c.isPullback_i_ofIsPullback sq)
  unfold finiteHorizontalShriekCompositionMap TwoSquare.vComp finiteHorizontalProperSigma
  infer_instance

/-- The canonical finite-horizontal compact-support composition isomorphism.  Its hom is the
open/proper interchange followed by the canonical direct-image compositor of formula (C), and
is defined independently of the compact-support exchange map.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-frobenius-and-rf/sk-i-relative-frob/sk-i-relative-frob.proof.md,
item (3), formula (C); Stacks Tag 0F7J.
(blueprint: lem-trf-finite-horizontal-shriek-mate-general) -/
noncomputable def finiteHorizontalShriekComposition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y X' Y' : SepFinType k}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (pmap : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback pmap.hom.left f'.hom.left f.hom.left g.hom.left)
    [AlgebraicGeometry.IsFinite g.hom.left]
    (c : Compactification f.hom.left) :
    R((pmap.hom.left)_*[ModuleCat.{u + 1} A]) ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) (c.ofIsPullback sq) ⋙
        R((g.hom.left)_*[ModuleCat.{u + 1} A]) := by
  letI := finiteHorizontalShriekCompositionMap_isIso A k f f' pmap g sq c
  exact asIso (finiteHorizontalShriekCompositionMap A k f f' pmap g sq c)

private theorem derived_adj_eq
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f =
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)).ofNatIsoLeft
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm := by
  exact Adjunction.derived_eq_ofNatIsoLeft
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).mapHomotopyCategory (.up ℤ))
    (HomotopyCategory.quasiIso _ _) (HomotopyCategory.quasiIso _ _)
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryFactorsh.hom
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorUnit
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
      (upperStar (ModuleCat.{u + 1} A) f)).symm

private theorem conjugate_transport
    {C D : Type*} [Category C] [Category D]
    {L L' M M' : C ⥤ D} {R S : D ⥤ C}
    (a : L ⊣ R) (b : M ⊣ S) (e : L' ≅ L) (d : M' ≅ M) (α : M' ⟶ L') :
    conjugateEquiv (a.ofNatIsoLeft e.symm) (b.ofNatIsoLeft d.symm) α =
      conjugateEquiv a b (d.inv ≫ α ≫ e.hom) := by
  ext K
  simp only [conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Iso.symm_inv, Functor.map_comp,
    Category.assoc]

private theorem comp_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L L' : C ⥤ D} {M M' : D ⥤ E} {R : D ⥤ C} {S : E ⥤ D}
    (a : L ⊣ R) (b : M ⊣ S) (e : L' ≅ L) (d : M' ≅ M) :
    (a.ofNatIsoLeft e.symm).comp (b.ofNatIsoLeft d.symm) =
      (a.comp b).ofNatIsoLeft
        ((Functor.isoWhiskerRight e M' ≪≫ Functor.isoWhiskerLeft L d).symm) := by
  apply Adjunction.ext_counit
  ext K
  simp only [Adjunction.comp_counit_app, Adjunction.ofNatIsoLeft_counit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_inv,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [← d.hom.naturality_assoc]
  rfl

private theorem push_comp_conjugate
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g).hom =
      conjugateEquiv
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom := by
  let B := ModuleCat.{u + 1} A
  have h := Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction B f) (upperStarLowerStarAdjunction B g)
    (upperStarLowerStarAdjunction B (f ≫ g)) (lowerStarComp B f g)
    (upperStarComp B f g) (conjugateEquiv_upperStarComp_hom B f g).symm
  rw [derived_adj_eq, derived_adj_eq, derived_adj_eq, comp_transport, conjugate_transport]
  rw [rightDerivedLowerStarComp, h]
  congr 1
  ext K
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [← NatTrans.naturality_assoc]
  simp
  rfl

private theorem push_comp_inv_conjugate
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).inv =
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g).inv := by
  have h : conjugateIsoEquiv
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g) =
        rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g := by
    apply Iso.ext
    exact (push_comp_conjugate A f g).symm
  exact congrArg Iso.inv h

private theorem push_congr_conjugate
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (leftDerivedUpperStarCongr (ModuleCat.{u + 1} A) h).hom =
        eqToHom (congrArg (fun a ↦ R((a)_*[ModuleCat.{u + 1} A])) h.symm) := by
  subst g
  simp [leftDerivedUpperStarCongr]

private theorem push_square_conjugate
    (A : Type (u + 1)) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {q : X' ⟶ X} {b' : X' ⟶ Y'} {b : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq q b' b g) :
    conjugateEquiv
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) b).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q))
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) b'))
        (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} A) sq).hom =
      finiteHorizontalProperSigma A sq := by
  unfold finiteHorizontalProperSigma
  rw [leftDerivedUpperStarSquareIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    ← conjugateEquiv_comp _ (derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) (b' ≫ g)),
    ← conjugateEquiv_comp _ (derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) (q ≫ b)),
    ← push_comp_conjugate, push_congr_conjugate, push_comp_inv_conjugate]
  exact Category.assoc _ _ _

private theorem proper_exchange_mate
    (A : Type (u + 1)) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {q : X' ⟶ X} {b' : X' ⟶ Y'} {b : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq q b' b g) :
    mateEquiv
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
      (TwoSquare.mk _ _ _ _ (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq)) =
        finiteHorizontalProperSigma A sq := by
  have h := iterated_mateEquiv_conjugateEquiv
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) b)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) b')
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
    (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} A) sq).hom
  rw [push_square_conjugate] at h
  exact h

private theorem pasted_unit
    {C₁ C₂ C₃ C₄ C₅ C₆ : Type*}
    [Category C₁] [Category C₂] [Category C₃]
    [Category C₄] [Category C₅] [Category C₆]
    {G₁ : C₁ ⥤ C₃} {G₂ : C₃ ⥤ C₅} {H₁ : C₂ ⥤ C₄} {H₂ : C₄ ⥤ C₆}
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    {L₃ : C₅ ⥤ C₆} {R₃ : C₆ ⥤ C₅}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (α : TwoSquare G₁ L₁ L₂ H₁) (β : TwoSquare G₂ L₂ L₃ H₂)
    (γ : TwoSquare R₁ H₁ G₁ R₂) (hα : mateEquiv a₁ a₂ α = γ)
    (δ : TwoSquare R₂ H₂ G₂ R₃) (hβ : mateEquiv a₂ a₃ β = δ)
    (Ex : TwoSquare (G₁ ⋙ G₂) L₁ L₃ (H₁ ⋙ H₂)) (hEx : α.hComp β = Ex)
    (χ : TwoSquare R₁ (H₁ ⋙ H₂) (G₁ ⋙ G₂) R₃)
    (hχ : γ.vComp δ = χ) (M : C₁) :
    a₃.unit.app ((G₁ ⋙ G₂).obj M) ≫ R₃.map (Ex.app M) =
      (G₁ ⋙ G₂).map (a₁.unit.app M) ≫ χ.app (L₁.obj M) := by
  subst Ex
  have h := unit_mateEquiv a₁ a₃ (α.hComp β) M
  rw [mateEquiv_vcomp, hα, hβ, hχ] at h
  exact h.symm

private theorem exchange_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y X' Y' : SepFinType k}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (pmap : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback pmap.hom.left f'.hom.left f.hom.left g.hom.left)
    [AlgebraicGeometry.IsFinite g.hom.left]
    (c : Compactification f.hom.left)
    (M : DerivedCategory (Sheaf (ProEt.topology X.obj.left) (ModuleCat.{u + 1} A))) :
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A) sq c).app M =
      (derivedBaseChangeMap (ModuleCat.{u + 1} A)
        (c.isPullback_g_ofIsPullback sq).flip.toCommSq).app
          (D((c.i)_!open[ModuleCat.{u + 1} A]).obj M) ≫
      R(((c.ofIsPullback sq).g)_*[ModuleCat.{u + 1} A]).map
        ((leftDerivedOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} A) (c.isPullback_i_ofIsPullback sq)).inv.app M) := by
  simp [rightDerivedLowerShriekOfCompactificationBaseChangeMap,
    rightDerivedLowerShriekOfCompactificationBaseChangeIso,
    leftDerivedOpenImmersionLowerShriekBaseChangeIso]

private theorem composition_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y X' Y' : SepFinType k}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (pmap : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback pmap.hom.left f'.hom.left f.hom.left g.hom.left)
    [AlgebraicGeometry.IsFinite g.hom.left]
    (c : Compactification f.hom.left) :
    (finiteHorizontalShriekComposition A k f f' pmap g sq c).hom =
      finiteHorizontalShriekCompositionMap A k f f' pmap g sq c := by
  rfl

private theorem open_exchange_mate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y X' Y' : SepFinType k}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (pmap : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback pmap.hom.left f'.hom.left f.hom.left g.hom.left)
    [AlgebraicGeometry.IsFinite g.hom.left]
    (c : Compactification f.hom.left) :
    mateEquiv
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) pmap.hom.left)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
        (pullback.fst c.g g.hom.left))
      (leftDerivedOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) (c.isPullback_i_ofIsPullback sq)).inv =
      finiteHorizontalOpenProperGamma A k f f' pmap g sq c := by
  rfl

private theorem exchange_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y X' Y' : SepFinType k}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (pmap : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback pmap.hom.left f'.hom.left f.hom.left g.hom.left)
    [AlgebraicGeometry.IsFinite g.hom.left]
    (c : Compactification f.hom.left) :
    (TwoSquare.hComp
      (TwoSquare.mk _ _ _ _ (leftDerivedOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) (c.isPullback_i_ofIsPullback sq)).inv)
      (TwoSquare.mk _ _ _ _ (derivedBaseChangeMap (ModuleCat.{u + 1} A)
        (c.isPullback_g_ofIsPullback sq).flip.toCommSq))).natTrans =
      rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A) sq c := by
  ext N
  simpa only [TwoSquare.hComp_app] using
    (exchange_app A k f f' pmap g sq c N).symm

private theorem composition_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y X' Y' : SepFinType k}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (pmap : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback pmap.hom.left f'.hom.left f.hom.left g.hom.left)
    [AlgebraicGeometry.IsFinite g.hom.left]
    (c : Compactification f.hom.left) :
    (TwoSquare.vComp
      (TwoSquare.mk _ _ _ _ (finiteHorizontalOpenProperGamma A k f f' pmap g sq c))
      (TwoSquare.mk _ _ _ _ (finiteHorizontalProperSigma A
        (c.isPullback_g_ofIsPullback sq).flip.toCommSq))).natTrans =
      finiteHorizontalShriekCompositionMap A k f f' pmap g sq c := by
  rfl

private theorem finite_horizontal_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y X' Y' : SepFinType k}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (pmap : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback pmap.hom.left f'.hom.left f.hom.left g.hom.left)
    [AlgebraicGeometry.IsFinite g.hom.left]
    (c : Compactification f.hom.left)
    (M : DerivedCategory (Sheaf (ProEt.topology X.obj.left) (ModuleCat.{u + 1} A))) :
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g.hom.left).unit.app
        ((rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).obj M)) ≫
      R((g.hom.left)_*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} A) sq c).app M) =
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c).map
        ((derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} A) pmap.hom.left).unit.app M) ≫
      (finiteHorizontalShriekComposition A k f f' pmap g sq c).hom.app
        (L((pmap.hom.left)^*[ModuleCat.{u + 1} A]).obj M) := by
  exact pasted_unit
    (G₁ := D((c.i)_!open[ModuleCat.{u + 1} A]))
    (G₂ := R((c.g)_*[ModuleCat.{u + 1} A]))
    (H₁ := D(((c.ofIsPullback sq).i)_!open[ModuleCat.{u + 1} A]))
    (H₂ := R(((c.ofIsPullback sq).g)_*[ModuleCat.{u + 1} A]))
    (L₁ := L((pmap.hom.left)^*[ModuleCat.{u + 1} A]))
    (R₁ := R((pmap.hom.left)_*[ModuleCat.{u + 1} A]))
    (L₂ := L((pullback.fst c.g g.hom.left)^*[ModuleCat.{u + 1} A]))
    (R₂ := R((pullback.fst c.g g.hom.left)_*[ModuleCat.{u + 1} A]))
    (L₃ := L((g.hom.left)^*[ModuleCat.{u + 1} A]))
    (R₃ := R((g.hom.left)_*[ModuleCat.{u + 1} A]))
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) pmap.hom.left)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (pullback.fst c.g g.hom.left))
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g.hom.left)
    (leftDerivedOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} A) (c.isPullback_i_ofIsPullback sq)).inv
    (derivedBaseChangeMap (ModuleCat.{u + 1} A)
      (c.isPullback_g_ofIsPullback sq).flip.toCommSq)
    (finiteHorizontalOpenProperGamma A k f f' pmap g sq c)
    (open_exchange_mate A k f f' pmap g sq c)
    (finiteHorizontalProperSigma A (c.isPullback_g_ofIsPullback sq).flip.toCommSq)
    (proper_exchange_mate A (c.isPullback_g_ofIsPullback sq).flip.toCommSq)
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A) sq c)
    (exchange_square A k f f' pmap g sq c)
    (finiteHorizontalShriekComposition A k f f' pmap g sq c).hom
    ((composition_square A k f f' pmap g sq c).trans
      (composition_hom A k f f' pmap g sq c).symm) M

/-- **Finite-horizontal compact-support exchange preserves ordinary units.** For a Cartesian
square of separated finite-type `k`-schemes with finite `g`, a compactification `c` of `f` and
`K ∈ Dctf(X, A)`, `Rg_*(Ex_!(K)) ∘ η_g = χ_{p^*K} ∘ Rf_!(η_p)`, with `χ` the canonical
compact-support composition comparison of formula (C).
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-frobenius-and-rf/sk-i-relative-frob/sk-i-relative-frob.proof.md,
proof of (3), "Since base change is compatible with these units"; Stacks Tags 0F7L
(lemma-base-change-shriek) and 0F7J.
(blueprint: lem-trf-finite-horizontal-shriek-mate-general)

Proof (steps of the node):
1. Write `c = (j, b)`, `c' = (j', b')`, `q : Z' ⟶ Z`; the open square `(j, j', q, p)` and the
   proper square `(b, b', g, q)` are Cartesian; `p`, `q` are finite, hence proper; all schemes
   are Noetherian and all arrows qcqs.
2. On `D⁺` of the étale site, `γ : j_! Rp_* ≅ Rq_* j'_!` is the normalized proper/open map of
   Stacks 0F7B (identity of the two proper-support subsheaves).
3. Finite direct image is exact (also on constant-`A` modules), so `γ` is computed termwise.
4. With `β : q^* j_! ≅ j'_! p^*`, sectionwise: `Rq_*(β_F) ∘ η_q = γ_{p^*F} ∘ j_!(η_p)` (O).
5. For the proper square, `E = ε_g ∘ g^*σ ∘ g^*Rb_*(η_q)` by mate pasting, hence
   `Rg_*(E_M) ∘ η_g = σ_{q^*M} ∘ Rb_*(η_q)` (P), `σ` the direct-image compositor.
6. `Ex_!^c = Rb'_*(β) ∘ E j_!` and `χ_N = σ_{j'_!N} ∘ Rb_*(γ_N)` (C), by the proper-input
   composition with identity-open compactifications of `p`, `g`.
7. Apply (P) at `M = j_! K`, naturality of `σ` at `β_K`, then (O) and (C): the identity holds on
   finite étale coefficients.
8. Choose étale origin `a : C_X L ≅ K` (finite `A` is Noetherian; finite-Tor comparison); the
   mate-unit identity transports the units `η_p`, `η_g` to the pro-étale units.
9. The open-site exchange and proper/open coefficient-mate lemmas, and transport-identifies-
   exchange, carry the étale `Ex_!` to the pro-étale `Ex_!^c`.
10. Finite-ring compact-support site coherence and tower pasting carry `χ^e` to `χ^p`, with
    identity-open normalization `e_1 = 1`.
11. Apply `C_Y` to the equality of Step 7; cancel the comparisons; conjugate along `a`.
12. Equivalently, `Ex_!` is the inverse square mate of `χ` (adjunction bijection). -/
theorem finiteHorizontalShriekMateGeneral
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (hℓp : ell ≠ p)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ a : A, (ell ^ n) • a = 0)
    {X Y X' Y' : SepFinType k}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (pmap : X' ⟶ X) (g : Y' ⟶ Y)
    (sq : IsPullback pmap.hom.left f'.hom.left f.hom.left g.hom.left)
    [AlgebraicGeometry.IsFinite g.hom.left]
    (c : Compactification f.hom.left)
    (K : Dctf(X.obj.left, ModuleCat.{u + 1} A)) :
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g.hom.left).unit.app
        ((rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).obj K.obj)) ≫
      R((g.hom.left)_*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} A) sq c).app K.obj) =
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c).map
        ((derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} A) pmap.hom.left).unit.app K.obj) ≫
      (finiteHorizontalShriekComposition A k f f' pmap g sq c).hom.app
        (L((pmap.hom.left)^*[ModuleCat.{u + 1} A]).obj K.obj) := by
  have _ := hℓp
  have _ := hA
  exact finite_horizontal_unit A k f f' pmap g sq c K.obj

end AlgebraicGeometry.ProEtale
