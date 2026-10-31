/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientEndpoints
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullbackEndpoints
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.RootEndpointTranspose.ShiftHelpers.DiagonalRootEndpointTransposeCore
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.KFlatDerivedAdjunctionTransportShifts
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Iso
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Transpose formulas for shifted scalar and geometric endpoints

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
  sk-prop-diagonal-tower/sk-prop-diagonal-tower-coefficients.proof.md,
  paragraph (3), final sentence (blueprint: lem-sfb-scalar-pullback-single-transposes).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
attribute [local instance 100001] sheafMonoidalCategory sheafBraidedCategory
attribute [local implicit_reducible] derivedScalars
attribute [local implicit_reducible] sheafMonoidalCategory
  sheafBraidedCategory sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory
  Localization.Monoidal.instSymmetricCategoryLocalizedMonoidal SymmetricCategory.ofCurried

@[instance_reducible]
private def transpose_sheaf_symmetric (Z : Scheme.{u}) :
    SymmetricCategory (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
  { sheafSymmetricCategory Z with toBraidedCategory := sheafBraidedCategory Ab Z }
attribute [local instance 100002] transpose_sheaf_symmetric

attribute [local irreducible] upperStarFromPoint

private theorem source_symmetric_comm
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (Z : Scheme.{u}) :
    @IsCommMonObj (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) _
      (sheafMonoidalCategory Ab Z) (sheafSymmetricCategory Z).toBraidedCategory
      (condensedRingObj R Z)
      (@Functor.monObjObj _ _ _ _ _ _ (upperStarFromPoint Z)
        (laxBraided_upperStarFromPoint Z).toLaxMonoidal R inferInstance) := by
  exact isCommMonObj_condensedRingObj R Z
attribute [local instance 1000000] source_symmetric_comm
attribute [local instance] isCommMonObj_condensedRingObj
  comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategory
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
  Mod.monoidalClosed Mod.monoidalCategory Mod.monoidalCategoryStruct
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor

private theorem commShift_ext
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} (s t : F.CommShift ℤ)
    (h : ∀ n, F.commShiftIso (self := s) n = F.commShiftIso (self := t) n) : s = t := by
  cases s
  cases t
  congr 1
  funext n
  exact h n

private theorem adjoint_shift_eq
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [s : F.CommShift ℤ] [G.CommShift ℤ] [adj.CommShift ℤ] :
    adj.leftAdjointCommShift ℤ = s := by
  apply commShift_ext
  intro n
  exact Adjunction.CommShift.compatibilityUnit_unique_left adj _ _ _
    (Adjunction.LeftAdjointCommShift.compatibilityUnit_iso adj n)
    (adj.shift_unit_app n)

private theorem homEquiv_shift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {V : D ⥤ C} [F.CommShift ℤ] [V.CommShift ℤ]
    (adj : F ⊣ V) [adj.CommShift ℤ] {M : C} {N : D} (g : F.obj M ⟶ N) (n : ℤ) :
    adj.homEquiv _ _ ((F.commShiftIso n).hom.app M ≫ g⟦n⟧') ≫
        (V.commShiftIso n).hom.app N = (adj.homEquiv _ _ g)⟦n⟧' := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [adj.shift_unit_app]
  simp only [Category.assoc]
  rw [Functor.commShiftIso_hom_naturality]

private theorem mate_transpose
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    {L : C ⥤ D} {V : D ⥤ C} {L' : E ⥤ H} {V' : H ⥤ E}
    (adj : L ⊣ V) (adj' : L' ⊣ V') (F : C ⥤ E) (G : D ⥤ H)
    (b : G ⋙ V' ≅ V ⋙ F) {K : C} {B : D} {B' : H}
    (g : L.obj K ⟶ B) (d : G.obj B ⟶ B') :
    adj'.homEquiv _ _ ((Adjunction.pushHomOfComapIso adj adj' b).app K ≫
        G.map g ≫ d) =
      F.map (adj.homEquiv _ _ g) ≫ b.inv.app B ≫ V'.map d := by
  have hu := unit_mateEquiv_symm adj adj'
    (TwoSquare.mk _ _ _ _ b.inv) K
  change F.map (adj.unit.app K) ≫ b.inv.app (L.obj K) =
    adj'.unit.app (F.obj K) ≫ V'.map
      ((Adjunction.pushHomOfComapIso adj adj' b).app K) at hu
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hu]
  have hn := b.inv.naturality g
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]

private theorem shifted_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (F : A ⥤ B) (G : C ⥤ D) (V : C ⥤ A) (W : D ⥤ B)
    [F.CommShift ℤ] [G.CommShift ℤ] [V.CommShift ℤ] [W.CommShift ℤ]
    (b : G ⋙ W ≅ V ⋙ F) [NatTrans.CommShift b.hom ℤ]
    {N : C} {NS : A} {NT : D} {NX NY : B}
    (zS : V.obj N ⟶ NS) (tR : F.obj NS ⟶ NY)
    (tT : G.obj N ⟶ NT) (zX : W.obj NT ⟶ NX) (e : NX ⟶ NY)
    (h : b.hom.app N ≫ F.map zS ≫ tR = W.map tT ≫ zX ≫ e) (n : ℤ) :
    b.hom.app (N⟦n⟧) ≫
        F.map ((V.commShiftIso n).hom.app N ≫ zS⟦n⟧') ≫
        (F.commShiftIso n).hom.app NS ≫ tR⟦n⟧' =
      W.map ((G.commShiftIso n).hom.app N ≫ tT⟦n⟧') ≫
        (W.commShiftIso n).hom.app NT ≫ zX⟦n⟧' ≫ e⟦n⟧' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc]
  have hb := NatTrans.shift_app_comm b.hom n N
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hb
  rw [← reassoc_of% hb]
  have hh := congrArg (fun k ↦ (shiftFunctor B n).map k) h
  simp only [Functor.map_comp] at hh
  rw [hh]
  rw [← Functor.commShiftIso_hom_naturality_assoc]

private theorem invert_square {C : Type*} [Category C] {A B D E H : C}
    (b : A ≅ B) (z : B ≅ D) (t : D ⟶ H) (u : A ⟶ E) (e : E ≅ H)
    (h : b.hom ≫ z.hom ≫ t = u ≫ e.hom) :
    z.inv ≫ b.inv ≫ u = t ≫ e.inv := by
  apply (cancel_epi z.hom).mp
  apply (cancel_epi b.hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using (congrArg (fun k ↦ k ≫ e.inv) h).symm

section ExactSquare
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]

private theorem exact_square_single
    (F : A ⥤ B) (G : C ⥤ D) (V : C ⥤ A) (W : D ⥤ B)
    [F.Additive] [G.Additive] [V.Additive] [W.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (e : G ⋙ W ≅ V ⋙ F) (N : C) :
    (((Functor.mapDerivedCategoryCompIso G W).symm ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫
        Functor.mapDerivedCategoryCompIso V F).hom.app
          ((DerivedCategory.singleFunctor C 0).obj N)) ≫
      F.mapDerivedCategory.map ((V.mapDerivedCategorySingleFunctor 0).hom.app N) ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app (V.obj N) =
    W.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).hom.app N) ≫
      (W.mapDerivedCategorySingleFunctor 0).hom.app (G.obj N) ≫
      (DerivedCategory.singleFunctor B 0).map (e.hom.app N) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso G W).hom.app
    ((DerivedCategory.singleFunctor C 0).obj N))).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor G W N]
  simp only [Category.assoc]
end ExactSquare

variable {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
  (a : R ⟶ T) [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)

private theorem geometric_shift
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S) :
    NatTrans.CommShift (F₁ := derivedUpper R f)
      (F₂ := (CondensedRing.upperStar R f).mapDerivedCategory)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f).hom ℤ := by
  have hs := (CondensedRing.kflat_derived_adjunction_transport_shifts (Mon.mk R) f).2.2
  have he : derivedUpperCommShift R f =
      CondensedRing.modulePullbackDerivedCommShift R f := by
    exact adjoint_shift_eq
      (F := CondensedRing.moduleObjectDerivedPullback R f)
      (G := CondensedRing.moduleObjectDerivedPushforward R f)
      (CondensedRing.derivedUpperStarLowerStarAdjunction R f)
  change NatTrans.CommShift (F₁ := derivedUpper R f)
    (F₂ := (CondensedRing.upperStar R f).mapDerivedCategory)
    (CondensedRing.modulePullbackExactComparison R f).hom ℤ
  rw [he]
  exact (CondensedRing.module_derived_functors_exact_and_comparison_shifts R f).2.2.1

private def restriction_shift_iso (Z : Scheme.{u}) (N : Modules T Z) :
    (Mod.comap (coefficientMap a Z)).mapDerivedCategory.obj
        (((DerivedCategory.singleFunctor (Modules T Z) 0).obj N)⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules R Z) 0).obj
        ((Mod.comap (coefficientMap a Z)).obj N))⟦(2 : ℤ)⟧ :=
  ((Mod.comap (coefficientMap a Z)).mapDerivedCategory.commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      (((Mod.comap (coefficientMap a Z)).mapDerivedCategorySingleFunctor 0).app N)

private def pullback_shift_iso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S) (M : Modules R S) :
    (derivedUpper R f).obj
        (((DerivedCategory.singleFunctor (Modules R S) 0).obj M)⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules R X) 0).obj
        ((CondensedRing.upperStar R f).obj M))⟦(2 : ℤ)⟧ :=
  ((derivedUpper R f).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso (singlePullback R f M)

private theorem restriction_pullback_shift :
    NatTrans.CommShift (scalarRestrictionPullbackIso a f).hom ℤ := by
  let : (CondensedRing.upperStar R f).leftDerivedFunctor.CommShift ℤ :=
    derivedUpperCommShift R f
  let : (CondensedRing.upperStar T f).leftDerivedFunctor.CommShift ℤ :=
    derivedUpperCommShift T f
  have hR : NatTrans.CommShift
      (F₁ := (CondensedRing.upperStar R f).leftDerivedFunctor)
      (F₂ := (CondensedRing.upperStar R f).mapDerivedCategory)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f).hom ℤ :=
    geometric_shift R f
  have hT : NatTrans.CommShift
      (F₁ := (CondensedRing.upperStar T f).leftDerivedFunctor)
      (F₂ := (CondensedRing.upperStar T f).mapDerivedCategory)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory T f).hom ℤ :=
    geometric_shift T f
  change NatTrans.CommShift
    (Functor.whiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory T f).hom
      (Mod.comap (coefficientMap a X)).mapDerivedCategory ≫
      (CondensedRing.derivedComapUpperStarIso a f).hom ≫
      Functor.whiskerLeft (Mod.comap (coefficientMap a S)).mapDerivedCategory
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f).inv) ℤ
  have : NatTrans.CommShift (CondensedRing.derivedComapUpperStarIso a f).hom ℤ := by
    change NatTrans.CommShift
      ((Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar T f)
        (Mod.comap (coefficientMap a X))).inv ≫
        (Functor.mapDerivedCategoryNatIso (CondensedRing.comapUpperStarIso a f)).hom ≫
        (Functor.mapDerivedCategoryCompIso (Mod.comap (coefficientMap a S))
          (CondensedRing.upperStar R f)).hom) ℤ
    infer_instance
  infer_instance

private theorem restriction_pullback_single (N : Modules T S) :
    (scalarRestrictionPullbackIso a f).hom.app
        ((DerivedCategory.singleFunctor (Modules T S) 0).obj N) ≫
      (derivedUpper R f).map
        (((Mod.comap (coefficientMap a S)).mapDerivedCategorySingleFunctor 0).hom.app N) ≫
      (singlePullback R f ((Mod.comap (coefficientMap a S)).obj N)).hom =
    (Mod.comap (coefficientMap a X)).mapDerivedCategory.map (singlePullback T f N).hom ≫
      (((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).hom.app
        ((CondensedRing.upperStar T f).obj N)) ≫
      (DerivedCategory.singleFunctor (Modules R X) 0).map
        ((CondensedRing.comapUpperStarIso a f).hom.app N) := by
  let hR := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f
  let hT := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory T f
  let V : DerivedCategory (Modules T X) ⥤ DerivedCategory (Modules R X) :=
    (Mod.comap (coefficientMap a X)).mapDerivedCategory
  change (V.map (hT.hom.app _) ≫ (CondensedRing.derivedComapUpperStarIso a f).hom.app _ ≫
      hR.inv.app _) ≫ (derivedUpper R f).map _ ≫
      (hR.hom.app _ ≫ _) = V.map (hT.hom.app _ ≫ _) ≫ _ ≫ _
  simp only [Category.assoc]
  erw [← hR.inv.naturality_assoc]
  erw [Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  erw [exact_square_single (CondensedRing.upperStar R f) (CondensedRing.upperStar T f)
    (Mod.comap (coefficientMap a S)) (Mod.comap (coefficientMap a X))
    (CondensedRing.comapUpperStarIso a f) N]

private theorem restriction_pullback_shifted_single (N : Modules T S) :
    (scalarRestrictionPullbackIso a f).hom.app
        (((DerivedCategory.singleFunctor (Modules T S) 0).obj N)⟦(2 : ℤ)⟧) ≫
      (derivedUpper R f).map (restriction_shift_iso a S N).hom ≫
      (pullback_shift_iso R f ((Mod.comap (coefficientMap a S)).obj N)).hom =
    (Mod.comap (coefficientMap a X)).mapDerivedCategory.map (pullback_shift_iso T f N).hom ≫
      (restriction_shift_iso a X ((CondensedRing.upperStar T f).obj N)).hom ≫
      ((DerivedCategory.singleFunctor (Modules R X) 0).map
        ((CondensedRing.comapUpperStarIso a f).hom.app N))⟦(2 : ℤ)⟧' := by
  have := restriction_pullback_shift a f
  have h := shifted_square (derivedUpper R f) (derivedUpper T f)
    (Mod.comap (coefficientMap a S)).mapDerivedCategory
    (Mod.comap (coefficientMap a X)).mapDerivedCategory
    (scalarRestrictionPullbackIso a f)
    (NS := (DerivedCategory.singleFunctor (Modules R S) 0).obj
      ((Mod.comap (coefficientMap a S)).obj N))
    (NT := (DerivedCategory.singleFunctor (Modules T X) 0).obj
      ((CondensedRing.upperStar T f).obj N))
    (NX := (DerivedCategory.singleFunctor (Modules R X) 0).obj
      ((Mod.comap (coefficientMap a X)).obj ((CondensedRing.upperStar T f).obj N)))
    (NY := (DerivedCategory.singleFunctor (Modules R X) 0).obj
      ((CondensedRing.upperStar R f).obj ((Mod.comap (coefficientMap a S)).obj N)))
    _ _ _ _ _ (restriction_pullback_single a f N) (2 : ℤ)
  simpa only [restriction_shift_iso, pullback_shift_iso, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Category.assoc] using h

private theorem restriction_pullback_shifted_inv (N : Modules T S) :
    (derivedUpper R f).map (restriction_shift_iso a S N).inv ≫
      (scalarRestrictionPullbackIso a f).inv.app
        (((DerivedCategory.singleFunctor (Modules T S) 0).obj N)⟦(2 : ℤ)⟧) ≫
      (Mod.comap (coefficientMap a X)).mapDerivedCategory.map (pullback_shift_iso T f N).hom ≫
      (restriction_shift_iso a X ((CondensedRing.upperStar T f).obj N)).hom =
    (pullback_shift_iso R f ((Mod.comap (coefficientMap a S)).obj N)).hom ≫
      ((DerivedCategory.singleFunctor (Modules R X) 0).map
        ((CondensedRing.comapUpperStarIso a f).inv.app N))⟦(2 : ℤ)⟧' := by
  let b := (scalarRestrictionPullbackIso a f).app
    (((DerivedCategory.singleFunctor (Modules T S) 0).obj N)⟦(2 : ℤ)⟧)
  let z := (derivedUpper R f).mapIso (restriction_shift_iso a S N)
  let e := (shiftFunctor (DerivedCategory (Modules R X)) (2 : ℤ)).mapIso
    ((DerivedCategory.singleFunctor (Modules R X) 0).mapIso
      ((CondensedRing.comapUpperStarIso a f).app N))
  have h := invert_square b z
    (pullback_shift_iso R f ((Mod.comap (coefficientMap a S)).obj N)).hom
    ((Mod.comap (coefficientMap a X)).mapDerivedCategory.map (pullback_shift_iso T f N).hom ≫
      (restriction_shift_iso a X ((CondensedRing.upperStar T f).obj N)).hom) e
    (by simpa only [b, z, e, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
      using restriction_pullback_shifted_single a f N)
  simpa only [b, z, e, Iso.app_inv, Functor.mapIso_inv, Category.assoc] using h

private theorem pullback_shift_naturality
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S)
    {M N : Modules R S} (g : M ⟶ N) :
    (derivedUpper R f).map
        (((DerivedCategory.singleFunctor (Modules R S) 0).map g)⟦(2 : ℤ)⟧') ≫
      (pullback_shift_iso R f N).hom =
    (pullback_shift_iso R f M).hom ≫
      (((DerivedCategory.singleFunctor (Modules R X) 0).map
        ((CondensedRing.upperStar R f).map g))⟦(2 : ℤ)⟧') := by
  simp only [pullback_shift_iso, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc]
  simp only [← Functor.map_comp]
  exact congrArg (fun k ↦ ((derivedUpper R f).commShiftIso (2 : ℤ)).hom.app _ ≫
    k⟦(2 : ℤ)⟧')
    ((Functor.singleFunctorCompLeftDerivedFunctorIso
      (CondensedRing.upperStar R f)).hom.naturality g)

omit [IsCommMonObj R] [IsCommMonObj T] in
private theorem restriction_shift_naturality (Z : Scheme.{u})
    {M N : Modules T Z} (g : M ⟶ N) :
    (Mod.comap (coefficientMap a Z)).mapDerivedCategory.map
        (((DerivedCategory.singleFunctor (Modules T Z) 0).map g)⟦(2 : ℤ)⟧') ≫
      (restriction_shift_iso a Z N).hom =
    (restriction_shift_iso a Z M).hom ≫
      (((DerivedCategory.singleFunctor (Modules R Z) 0).map
        ((Mod.comap (coefficientMap a Z)).map g))⟦(2 : ℤ)⟧') := by
  simp only [restriction_shift_iso, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc]
  simp only [← Functor.map_comp]
  exact congrArg (fun k ↦
    ((Mod.comap (coefficientMap a Z)).mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
    k⟦(2 : ℤ)⟧')
    (((Mod.comap (coefficientMap a Z)).mapDerivedCategorySingleFunctor 0).hom.naturality g)

set_option maxHeartbeats 1600000 in
-- The source adjunction and the named extension functor share large instance arguments.
private theorem endpoint_transpose (Z : Scheme.{u})
    {M : Modules R Z} {N : Modules T Z} {v : M.X ⟶ N.X}
    (e : Endpoint a M N v) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Z)).homEquiv _ _
        (e.shift a) ≫ (restriction_shift_iso a Z N).hom =
      ((DerivedCategory.singleFunctor (Modules R Z) 0).map e.semilinear.hom)⟦(2 : ℤ)⟧' := by
  have hc := RootEndpointTranspose.ShiftHelpers.scalarAdjunction_commShift a Z
  have hshift := homEquiv_shift (F := derivedScalars a Z)
    (V := (Mod.comap (coefficientMap a Z)).mapDerivedCategory)
    (UniformizerSquareData.scalarAdjunction a Z) e.iso.hom (2 : ℤ)
  unfold UniformizerSquareData.scalarAdjunction at hshift
  change (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Z)).homEquiv _ _
      (((derivedScalars a Z).commShiftIso (2 : ℤ)).hom.app _ ≫
        e.iso.hom⟦(2 : ℤ)⟧') ≫
      (((Mod.comap (coefficientMap a Z)).mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
        (((Mod.comap (coefficientMap a Z)).mapDerivedCategorySingleFunctor 0).hom.app N)
          ⟦(2 : ℤ)⟧') = _
  rw [← Category.assoc]
  erw [hshift]
  erw [e.normalization]
  simp only [← Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem pullEndpoint_shift
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} {f : X ⟶ S}
    {M : Modules R S} {N : Modules R X}
    {m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    (e : PullEndpoint R f M N m) :
    e.shift = (pullback_shift_iso R f M).hom ≫
      ((DerivedCategory.singleFunctor (Modules R X) 0).map e.iso.hom)⟦(2 : ℤ)⟧' := by
  simp only [PullEndpoint.shift, PullEndpoint.derived, pullback_shift_iso,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]

set_option maxHeartbeats 1600000 in
-- The adjunction normalizations compare large, fixed derived-functor instances.
/-- The two shifted endpoint maps have the specified ordinary transposes.
Source: latest blueprint, diagonal coefficient changes, paragraph (3), final sentence:
coefficient functors commute with pullback. The following calculation expands this
normalization without equating the two ordinary composites.
(blueprint: lem-sfb-scalar-pullback-single-transposes).

Proof (the seven steps of the node). Write `A_Z` for the scalar adjunction bijection,
`V_Z` for derived restriction, `G_A` for ordinary pullback, and `F_A` for its actual
left derived functor. All compositions below are left to right.

1. For an exact ordinary functor `H`, let `ζ_H` be its canonical single comparison
and put `k_H = s_H ; ζ_H[2]`, using its canonical shift comparison `s_H`. Restriction
is exact and additive by `sk-def-sfb-change-of-scalars`; geometric inverse image is
exact and additive for arbitrary `f` by `det-prop-sfb-module-pullback-exact-main`.
The tensor and colimit hypotheses come from `lem-weil-pbc-sheaf-tensor-closed`.
Write `θ_A` for the canonical geometric single comparison and `t_A = s_F_A ; θ_A[2]`.
Expanding `PullEndpoint.shift` and `PullEndpoint.derived` gives
`dR.shift = t_R,M ; J_X(p)[2]` and `dT.shift = t_T,N ; J_X(q)[2]`.
Thus the displayed `c` is `t_R,M` and `z` is `k_V_X,N'`. These are specified
comparisons, rather than additional choices.

2. Write the scalar adjunction as `A_Z(g) = η_Z ; V_Z(g)`. Its left shift is induced
by adjunction to the exact restriction shift, as in
`lem-diagonal-root-endpoint-transpose-core`. Unit compatibility gives
`η_Z(K[2]) ; V_Z(s_E_Z,K) ; s_V_Z,E_Z(K) = η_Z(K)[2]`. By shift naturality,
`A_Z(s_E_Z,K ; g[2]) ; s_V_Z,B = A_Z(g)[2]` for `g : E_Z(K) ⟶ B`.
Apply this to each endpoint and its normalization from
`def-sfb-diagonal-coefficient-endpoints`. It gives
`A_S(eS.shift) = J_S(v)[2] ; k_V_S,N⁻¹` and
`A_X(eX.shift) = J_X(w)[2] ; z⁻¹`. No exactness of scalar extension is needed.

3. Put `K = J_S(M)[2]`, `B = J_S(N)[2]`, and `B' = J_X(N')[2]`. Let
`b = scalarRestrictionPullbackIso a f`. The comparison `μ` is the inverse mate of
`b⁻¹` by `def-diagonal-scalar-pullback-comparison`. The mate-unit identity of
`def-weil-pbc-adjunction-mate` and `lem-pur-mate-unit-compatibility` gives
`F_R(η_S(K)) ; b⁻¹_E_S(K) = η_X(F_R(K)) ; V_X(μ_K)`. Naturality of `b⁻¹` at
`eS.shift`, followed by functoriality of restriction, gives
`A_X(P) = F_R(A_S(eS.shift)) ; b⁻¹_B ; V_X(dT.shift)`.
Unit naturality independently gives `A_X(Q) = dR.shift ; A_X(eX.shift)`.
These are calculations at the shifted objects; no shift assertion about `μ` is required.

4. Let `h_A : F_A ≅ D(G_A)` be the canonical exact comparison. The geometric shift
in `def-sfb-diagonal-coefficient-exchange` is induced by the actual derived
adjunction and the fixed right-adjoint shift. By
`lem-sfb-kflat-derived-adjunction-transport-shifts`, the unit and counit also
commute with the shift transported along `h_A`. The transported shift is specified
by `def-sfb-module-derived-functor-shifts` and identified with the representative
shift by `lem-sfb-module-derived-functor-compositor-shifts`. Uniqueness for a left
adjoint with fixed right shift, as in
`lem-weil-pbc-adjunction-shift-compatibility-unique`, identifies these shifts.
Consequently `s_F_A ; h_A[2] = h_A ; s_D(G_A)`. Since `θ_A = h_A ; ζ_G_A`, we get
`t_A = h_A ; k_G_A`. If `δ` denotes the derived ordinary comparison induced from
`σ` with the exact-derived composition comparisons, the definition of `b` is
`b_B = V_X(h_T,B) ; δ_B ; h_R,V_S(B)⁻¹`, using
`def-sfb-derived-comap-upper-star-iso` and the canonical geometric comparisons.

5. First compute `b` on unshifted single objects. Naturality moves `h_R⁻¹`
past the restriction single comparison, after which it cancels with `h_R`.
The canonical exact-derived composition and natural-isomorphism comparisons on
singles, as in `def-geo-exact-degree-zero-interface`, identify the remaining
square with `J_X(σ_N)`. Shift this square by two, using shift compatibility of
`b` from step 4 and naturality of the four functor shift comparisons. This gives
`b_B ; F_R(k_V_S,N) ; t_R,V_S(N)` equal to
`V_X(t_T,N) ; k_V_X,G_T(N) ; J_X(σ_N)[2]`.
Precompose by `F_R(k_V_S,N⁻¹) ; b_B⁻¹` and postcompose by `J_X(σ_N⁻¹)[2]`.
Cancelling the isomorphism pairs gives
`F_R(k_V_S,N⁻¹) ; b_B⁻¹ ; V_X(t_T,N) ; k_V_X,G_T(N)` equal to
`t_R,V_S(N) ; J_X(σ_N⁻¹)[2]`.

6. Naturality of the geometric and restriction comparisons gives
`F_R(J_S(v)[2]) ; t_R,V_S(N) = t_R,M ; J_X(G_R(v))[2]` and
`V_X(J_X(q)[2]) ; z = k_V_X,G_T(N) ; J_X(V_X(q))[2]`.
Expand `A_X(P)` using steps 1--3. Substitute the second naturality equation,
then step 5, then the first naturality equation. Functoriality of the single and
shift functors combines the remaining factors into
`c ; J_X(G_R(v) ; σ_N⁻¹ ; V_X(q))[2]`, proving the first equality.

7. For the second equality substitute steps 1--3 into `A_X(Q) ; z`.
The consecutive `z⁻¹ ; z` cancel, leaving
`c ; J_X(p)[2] ; J_X(w)[2] = c ; J_X(p ; w)[2]`.
The two ordinary composites have never been equated. -/
theorem scalarPullbackSingleTransposes
    {M : Modules R S} {M' : Modules R X}
    {N : Modules T S} {N' : Modules T X}
    (v : M.X ⟶ N.X) (w : M'.X ⟶ N'.X)
    (p : (upperStar Ab.{u + 1} f).obj M.X ⟶ M'.X)
    (q : (upperStar Ab.{u + 1} f).obj N.X ⟶ N'.X)
    (eS : Endpoint a M N v) (eX : Endpoint a M' N' w)
    (dR : PullEndpoint R f M M' p)
    (dT : PullEndpoint T f N N' q) :
    (@Mod.derivedExtendMapDerivedCategoryAdjunction
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ _ _
      (condensedRingObj R X) (condensedRingObj T X) _ _
      (isCommMonObj_condensedRingObj R X) (isCommMonObj_condensedRingObj T X)
      (coefficientMap a X) _).homEquiv
        ((derivedUpper R f).obj
          (((DerivedCategory.singleFunctor (Modules R S) 0).obj M)⟦(2 : ℤ)⟧))
        (((DerivedCategory.singleFunctor (Modules T X) 0).obj N')⟦(2 : ℤ)⟧)
        (((scalarPullbackComparison a f).app
          (((DerivedCategory.singleFunctor (Modules R S) 0).obj M)⟦(2 : ℤ)⟧)) ≫
          (derivedUpper T f).map (eS.shift a) ≫ dT.shift) ≫
      (((Mod.comap (coefficientMap a X)).mapDerivedCategory.commShiftIso
          (2 : ℤ)).hom.app
        (((DerivedCategory.singleFunctor (Modules T X) 0).obj N'))) ≫
      (((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).hom.app
        N')⟦(2 : ℤ)⟧' =
      (((derivedUpper R f).commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor (Modules R S) 0).obj M) ≫
        (singlePullback R f M).hom⟦(2 : ℤ)⟧') ≫
      ((DerivedCategory.singleFunctor (Modules R X) 0).map
        ((AlgebraicGeometry.ProEtale.CondensedRing.upperStar R f).map eS.semilinear.hom ≫
          (AlgebraicGeometry.ProEtale.CondensedRing.comapUpperStarIso a f).inv.app N ≫
          (Mod.comap (coefficientMap a X)).map dT.iso.hom))⟦(2 : ℤ)⟧' ∧
    (@Mod.derivedExtendMapDerivedCategoryAdjunction
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ _ _
      (condensedRingObj R X) (condensedRingObj T X) _ _
      (isCommMonObj_condensedRingObj R X) (isCommMonObj_condensedRingObj T X)
      (coefficientMap a X) _).homEquiv
        ((derivedUpper R f).obj
          (((DerivedCategory.singleFunctor (Modules R S) 0).obj M)⟦(2 : ℤ)⟧))
        (((DerivedCategory.singleFunctor (Modules T X) 0).obj N')⟦(2 : ℤ)⟧)
        (((derivedScalars a X).map dR.shift ≫ eX.shift a)) ≫
      (((Mod.comap (coefficientMap a X)).mapDerivedCategory.commShiftIso
          (2 : ℤ)).hom.app
        (((DerivedCategory.singleFunctor (Modules T X) 0).obj N'))) ≫
      (((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).hom.app
        N')⟦(2 : ℤ)⟧' =
      (((derivedUpper R f).commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor (Modules R S) 0).obj M) ≫
        (singlePullback R f M).hom⟦(2 : ℤ)⟧') ≫
      ((DerivedCategory.singleFunctor (Modules R X) 0).map
        (dR.iso.hom ≫ eX.semilinear.hom))⟦(2 : ℤ)⟧' := by
  constructor
  · change _ ≫ (restriction_shift_iso a X N').hom =
      (pullback_shift_iso R f M).hom ≫ _
    change (@Mod.derivedExtendMapDerivedCategoryAdjunction
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ _ _
      (condensedRingObj R X) (condensedRingObj T X) _ _
      (isCommMonObj_condensedRingObj R X) (isCommMonObj_condensedRingObj T X)
      (coefficientMap a X) _).homEquiv
      _ _ ((Adjunction.pushHomOfComapIso
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S))
        (@Mod.derivedExtendMapDerivedCategoryAdjunction
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ _ _
      (condensedRingObj R X) (condensedRingObj T X) _ _
      (isCommMonObj_condensedRingObj R X) (isCommMonObj_condensedRingObj T X)
      (coefficientMap a X) _)
        (scalarRestrictionPullbackIso a f)).app _ ≫
        (derivedUpper T f).map (eS.shift a) ≫ dT.shift) ≫ _ = _
    rw [mate_transpose]
    have hS := (restriction_shift_iso a S N).eq_comp_inv.mpr
      (endpoint_transpose a S eS)
    rw [hS, pullEndpoint_shift dT]
    simp only [Functor.map_comp, Category.assoc]
    rw [restriction_shift_naturality a X dT.iso.hom]
    rw [reassoc_of% restriction_pullback_shifted_inv a f N]
    rw [reassoc_of% pullback_shift_naturality R f eS.semilinear.hom]
  · change _ ≫ (restriction_shift_iso a X N').hom =
      (pullback_shift_iso R f M).hom ≫ _
    erw [Adjunction.homEquiv_naturality_left]
    erw [Category.assoc, endpoint_transpose]
    rw [pullEndpoint_shift dR]
    simp only [Functor.map_comp, Category.assoc]

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
