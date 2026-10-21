/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Sheaf.Paper.EtaleDerivedScalarTensor
public import Sheaf.Paper.FiniteReductionConstructibility
public import Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
public import Sheaf.Paper.EtaleUnboundedRestrictionComparison
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
import Sheaf.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import WeilConjectures.CategoryTheory.Sites.ReductionFlat
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import Sheaf.SixFunctors.EtaleHomComparisonModels
import Sheaf.CategoryTheory.DerivedTensorRightExact
import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek


/-! # Exceptional coefficient comparisons

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, (2)--(3); Stacks 0GL6 and 0F7L
(blueprint: lem-pur-exceptional-coefficient-comparison).

All scalar functors are the published left adjoints to exact scalar restriction.
The scalar/pullback identification and the proper coefficient map are the recorded
`scalarPullbackIso` and `scalarMate` of lem-pur-etale-scalar-mate-projection.
The comparison for compact support is constructed from its open and proper parts.
The auxiliary tensor and pullback identifications are fixed by their ordinary
adjunctions and their computation on cochain representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
namespace ExceptionalCoefficients

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)

/-- Scalar extension and open extension by zero are left adjoint to canonically
identified right adjoints; uniqueness gives the identity/zero comparison.
Source: Stacks 0GL6 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def openIso {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        scalarExtension φ Z ≅
      scalarExtension φ X ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory :=
  (conjugateIsoEquiv
    (((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm).comp
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)))
    ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).comp
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).symm))).symm
    (scalarRestrictionPullbackIso φ j) |>.symm

/-- The canonical compact-support coefficient arrow, on a fixed compactification: the
recorded proper coefficient mate `scalarMate` at the open extension, followed by
proper direct image of the open comparison.
Source: Stacks 0GL6 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def compactSupportMap {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) :
    (scalarExtension φ Y).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((scalarExtension φ X).obj M) :=
  (scalarMate φ c.g).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) ≫
    (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.map
      ((openIso φ c.i).hom.app M)

/-- Inverse of the canonical comparison on its isomorphism domain, extended by zero.
This extension only makes the term total; every theorem use is on the domain where
b is an isomorphism. Source: Stacks 0GL6
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def comparisonInverse {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((scalarExtension φ X).obj M) ⟶
      (scalarExtension φ Y).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) :=
  open Classical in
  if h : IsIso (compactSupportMap φ c M) then
    @inv _ _ _ _ (compactSupportMap φ c M) h
  else 0

/-- A total extension of the counit-transpose construction; its zero fallback is
irrelevant on the stated domain, where the theorem proves invertibility of b.
Source: blueprint compatibilities (2)
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def mateMap [Finite A] [Finite B] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (K : DerivedCategoryModule A Y) :
    (scalarExtension φ X).obj ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K) ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} B) f).obj ((scalarExtension φ Y).obj K) :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f).homEquiv _ _
    (comparisonInverse φ (HasCompactification.compactification f)
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K) ≫
      (scalarExtension φ Y).map
        ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).counit.app K))

/-- The ordinary extension has its actual scalar-restriction adjunction.
Source: Stacks 06YY (blueprint: lem-pur-exceptional-coefficient-comparison). -/
instance ordinaryIsLeftAdjoint (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ T).IsLeftAdjoint :=
  (ProEtale.etaleSheafExtendScalarsAdjunction φ T).isLeftAdjoint

/-- The ordinary tensorator is the sheafified scalar balancing map.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
instance ordinaryOplax (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ T).OplaxMonoidal :=
  composeAndSheafifyOplaxMonoidal T.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)

/-- Representative normalization for a scalar tensor comparison, with monoidal data
kept shared in both categories. Source: Stacks 07A4
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def TensorNormalizationAux
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E ≅
      E.prod E ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory D))) : Prop :=
  ∀ P Q : CochainComplex C ℤ,
    δ.hom.app (_root_.DerivedCategory.Q.obj P, _root_.DerivedCategory.Q.obj Q) ≫
        (rep P ⊗ₘ rep Q) ≫ Functor.LaxMonoidal.μ _root_.DerivedCategory.Q
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) =
      E.map (Functor.LaxMonoidal.μ _root_.DerivedCategory.Q P Q) ≫ rep (P ⊗ Q) ≫
        _root_.DerivedCategory.Q.map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q)

/-- The all-complex normalization with site tensor functors kept as shared constants.
This is exactly `TensorNormalizationAux` on the small etale sheaf categories.
Keeping its monoidal arguments inside this generic body avoids repeated comparison
of the nested sheafification and derived-monoidal proofs in specialized theorem types.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def SiteTensorNormalizationAux
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (D : Type w) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    [Abelian.HasFunctorialFlatResolution D] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology C ⥤ Sheaf T.smallEtaleTopology D)
    [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (S : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology D))
    (r : ∀ P : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ,
      S.obj (_root_.DerivedCategory.Q.obj P) ⟶
        _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : Functor.uncurry.obj (derivedTensor C T) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (derivedTensor D T)) : Prop :=
  TensorNormalizationAux F S r δ

/-- Small-etale specialization of the shared all-complex tensor normalization.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
abbrev TensorNormalization (T : Scheme.{u}) :=
  SiteTensorNormalizationAux (ModuleCat.{u + 1} A) (ModuleCat.{u + 1} B) T
    (ProEtale.etaleSheafExtendScalars φ T)
    (scalarExtension φ T) (scalarExtensionRepresentative φ T)

private theorem mapComplex_unit_formula
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {E : C ⥤ D} {U : D ⥤ C} [E.Additive] [U.Additive] (adj : E ⊣ U)
    (P : CochainComplex C ℤ) :
    (adj.mapHomologicalComplex (.up ℤ)).unit.app P =
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
        (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P := by
  ext i
  simp only [Functor.id_obj, Functor.comp_obj, Adjunction.mapHomologicalComplex_unit_app_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexIdIso_inv_app_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  exact (Category.comp_id _).symm

open AlgebraicGeometry AlgebraicGeometry.Etale
open MonoidalCategory Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ u₂
private def productLaxTensorator
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] :
    F.prod F ⋙ Functor.uncurry.obj (curriedTensor D) ⟶
      Functor.uncurry.obj (curriedTensor C) ⋙ F where
  app X := Functor.LaxMonoidal.μ F X.1 X.2
  naturality X Y f := by
    have h := Functor.LaxMonoidal.μ_natural F f.1 f.2
    rw [MonoidalCategory.tensorHom_def (F.map f.1) (F.map f.2),
      MonoidalCategory.tensorHom_def f.1 f.2] at h
    simpa only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
      Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map] using h

private def productOplaxTensorator
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (F : C ⥤ D)
    (τ : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj U) :
    Functor.uncurry.obj T ⋙ F ⟶ F.prod F ⋙ Functor.uncurry.obj U where
  app X := (τ.app X.1).app X.2
  naturality X Y f := by
    change F.map ((T.map f.1).app X.2 ≫ (T.obj Y.1).map f.2) ≫ _ =
      _ ≫ ((U.map (F.map f.1)).app (F.obj X.2) ≫ (U.obj (F.obj Y.1)).map (F.map f.2))
    rw [F.map_comp, Category.assoc]
    have h₁ := congr_app (τ.naturality f.1) X.2
    have h₂ := (τ.app Y.1).naturality f.2
    change F.map ((T.map f.1).app X.2) ≫ (τ.app Y.1).app X.2 =
      (τ.app X.1).app X.2 ≫ (U.map (F.map f.1)).app (F.obj X.2) at h₁
    change F.map ((T.obj Y.1).map f.2) ≫ (τ.app Y.1).app Y.2 =
      (τ.app Y.1).app X.2 ≫ (U.obj (F.obj Y.1)).map (F.map f.2) at h₂
    rw [h₂, ← Category.assoc, h₁, Category.assoc]

private def productIsoOfFamily
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (F : C ⥤ D)
    (μ : ∀ K L : C, (U.obj (F.obj K)).obj (F.obj L) ≅ F.obj ((T.obj K).obj L))
    (h₁ : ∀ {K K'} (f : K ⟶ K') L,
      (U.map (F.map f)).app (F.obj L) ≫ (μ K' L).hom =
        (μ K L).hom ≫ F.map ((T.map f).app L))
    (h₂ : ∀ K {L L'} (f : L ⟶ L'),
      (U.obj (F.obj K)).map (F.map f) ≫ (μ K L').hom =
        (μ K L).hom ≫ F.map ((T.obj K).map f)) :
    Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj U :=
  (NatIso.ofComponents (fun X ↦ μ X.1 X.2) (by
    intro X Y f
    change ((U.map (F.map f.1)).app (F.obj X.2) ≫
      (U.obj (F.obj Y.1)).map (F.map f.2)) ≫ (μ Y.1 Y.2).hom =
      (μ X.1 X.2).hom ≫ F.map ((T.map f.1).app X.2 ≫ (T.obj Y.1).map f.2)
    rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc, ← F.map_comp])).symm

private theorem productIso_natural₁
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (F : C ⥤ D)
    (δ : Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj U)
    {K K' : C} (f : K ⟶ K') (L : C) :
    (U.map (F.map f)).app (F.obj L) ≫ (δ.app (K', L)).inv =
      (δ.app (K, L)).inv ≫ F.map ((T.map f).app L) := by
  have h := δ.inv.naturality (show (K, L) ⟶ (K', L) from (f, 𝟙 L))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map] at h
  simpa only [_root_.CategoryTheory.Functor.map_id, Functor.comp_obj, Functor.uncurry_obj_obj,
    Functor.prod_obj, Iso.app_inv, Category.comp_id] using h

private theorem productIso_natural₂
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (F : C ⥤ D)
    (δ : Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj U)
    (K : C) {L L' : C} (f : L ⟶ L') :
    (U.obj (F.obj K)).map (F.map f) ≫ (δ.app (K, L')).inv =
      (δ.app (K, L)).inv ≫ F.map ((T.obj K).map f) := by
  have h := δ.inv.naturality (show (K, L) ⟶ (K, L') from (𝟙 K, f))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map] at h
  simpa only [_root_.CategoryTheory.Functor.map_id, Functor.comp_obj, Functor.uncurry_obj_obj,
    Functor.prod_obj, Iso.app_inv, NatTrans.id_app, Category.id_comp] using h

private theorem tensor_normalization_all_of_flat
    {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (r : _root_.DerivedCategory.Q ⋙ E ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q)
    (δ : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E ≅
      E.prod E ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory D)))
    (hflat : Functor.rightExactTensorModelNormalization F E r.app
      (fun K L ↦ (δ.app (K, L)).symm)) :
    AlgebraicGeometry.Etale.ExceptionalCoefficients.TensorNormalizationAux F E r.app δ := by
  let QC := _root_.DerivedCategory.Q (C := C)
  let QD := _root_.DerivedCategory.Q (C := D)
  let FC := F.mapHomologicalComplex (.up ℤ)
  let α : QC.prod QC ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E ⟶
      FC.prod FC ⋙ Functor.uncurry.obj (curriedTensor (CochainComplex D ℤ)) ⋙ QD :=
    Functor.whiskerLeft (QC.prod QC) δ.hom ≫
      Functor.whiskerRight (r.prod r)
        (Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory D))) ≫
      Functor.whiskerLeft (FC.prod FC)
        (productLaxTensorator QD)
  let β : QC.prod QC ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E ⟶
      FC.prod FC ⋙ Functor.uncurry.obj (curriedTensor (CochainComplex D ℤ)) ⋙ QD :=
    Functor.whiskerRight (productLaxTensorator QC) E ≫
      Functor.whiskerLeft (Functor.uncurry.obj (curriedTensor (CochainComplex C ℤ))) r ≫
      Functor.whiskerRight
        (productOplaxTensorator (curriedTensor (CochainComplex C ℤ))
          (curriedTensor (CochainComplex D ℤ)) FC
          (Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F)) QD
  intro P Q
  have hab : α.app (P, Q) = β.app (P, Q) := by
    obtain ⟨P', π, hπ, hPflat, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat P
    obtain ⟨Q', ρ, hρ, hQflat, hQ⟩ := CochainComplex.exists_quasiIso_flat_kFlat Q
    have : IsIso (QC.map π) := by
      exact Localization.inverts QC (HomologicalComplex.quasiIso C (.up ℤ)) π hπ
    have : IsIso (QC.map ρ) := by
      exact Localization.inverts QC (HomologicalComplex.quasiIso C (.up ℤ)) ρ hρ
    have hi : IsIso
        ((QC.prod QC ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E).map
          (show (P', Q') ⟶ (P, Q) from (π, ρ))) := by
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj, Functor.uncurry_obj_map,
        curriedTensor_map_app, curriedTensor_obj_map]
      rw [← MonoidalCategory.tensorHom_def (QC.map π) (QC.map ρ)]
      infer_instance
    apply (cancel_epi
      ((QC.prod QC ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E).map
        (show (P', Q') ⟶ (P, Q) from (π, ρ)))).1
    rw [α.naturality, β.naturality]
    have h : α.app (P', Q') = β.app (P', Q') := by
      simpa only [α, β, QC, QD, FC, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.prod_obj, Functor.uncurry_obj_obj,
        Functor.uncurry_obj_map, NatTrans.prod_app_fst, NatTrans.prod_app_snd, Functor.comp_obj,
        productLaxTensorator,
        productOplaxTensorator, curriedTensor_map_app, curriedTensor_obj_map,
        MonoidalCategory.tensorHom_def, curriedTensor_obj_obj,
        Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, Iso.symm_inv, Iso.app_hom,
        Category.assoc] using (hflat P' Q' hP hQ hPflat hQflat).symm
    rw [h]
  simpa only [α, β, QC, QD, FC, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.prod_obj, Functor.uncurry_obj_obj,
    Functor.uncurry_obj_map, NatTrans.prod_app_fst, NatTrans.prod_app_snd, Functor.comp_obj,
        productLaxTensorator,
    productOplaxTensorator, curriedTensor_map_app, curriedTensor_obj_map,
    MonoidalCategory.tensorHom_def, curriedTensor_obj_obj,
        Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, Iso.symm_inv, Iso.app_hom,
    Category.assoc] using hab


private theorem tensor_normalization_all_onSite
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (D : Type w) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    [Abelian.HasFunctorialFlatResolution D] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology C ⥤ Sheaf T.smallEtaleTopology D)
    [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (S : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology D))
    (r : _root_.DerivedCategory.Q ⋙ S ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q)
    (δ : Functor.uncurry.obj (derivedTensor C T) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (derivedTensor D T))
    (hflat : AlgebraicGeometry.Etale.EtaleHomTensorModelNormalization C D T F S r.app
      (fun K L ↦ (δ.app (K, L)).symm)) :
    AlgebraicGeometry.Etale.ExceptionalCoefficients.SiteTensorNormalizationAux C D T F S
      r.app δ := by
  exact tensor_normalization_all_of_flat F S r δ hflat


private theorem site_normalization_flat
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (D : Type w) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    [Abelian.HasFunctorialFlatResolution D] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology C ⥤ Sheaf T.smallEtaleTopology D)
    [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (S : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology D))
    (r : ∀ P : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ,
      S.obj (_root_.DerivedCategory.Q.obj P) ⟶
        _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : Functor.uncurry.obj (derivedTensor C T) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (derivedTensor D T))
    (hn : AlgebraicGeometry.Etale.ExceptionalCoefficients.SiteTensorNormalizationAux
      C D T F S r δ) :
    EtaleHomTensorModelNormalization C D T F S r
      (fun K L ↦ (δ.app (K, L)).symm) := by
  intro P Q _ _ _ _
  exact (hn P Q).symm

private def adjointRepresentative
    {C D V W : Type*} [Category C] [Category D] [Category V] [Category W]
    (QC : C ⥤ V) (QD : D ⥤ W) (FC : C ⥤ D) (UC : D ⥤ C)
    (E : V ⥤ W) (U : W ⥤ V) (adj : E ⊣ U)
    (a : FC ⊣ UC) (fac : UC ⋙ QC ≅ QD ⋙ U) : QC ⋙ E ⟶ FC ⋙ QD := by
  let t : QC ⟶ FC ⋙ QD ⋙ U :=
    Functor.whiskerRight a.unit QC ≫ Functor.whiskerLeft FC fac.hom
  exact {
    app P := (adj.homEquiv _ _).symm (t.app P)
    naturality P Q f := by
      change E.map (QC.map f) ≫ _ = _ ≫ QD.map (FC.map f)
      calc
        _ = (adj.homEquiv _ _).symm (QC.map f ≫ t.app Q) :=
          (adj.homEquiv_naturality_left_symm (QC.map f) (t.app Q)).symm
        _ = (adj.homEquiv _ _).symm (t.app P ≫ U.map (QD.map (FC.map f))) :=
          congrArg (adj.homEquiv _ _).symm (t.naturality f)
        _ = _ := adj.homEquiv_naturality_right_symm _ _ }


/-- The canonical scalar tensor isomorphism is determined by ordinary balancing.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison).
Proof: on flat-term K-flat pairs the counits and the localization tensorators
are invertible. Ordinary balancing therefore defines δ by the displayed equation.
It commutes with resolutions and differentials. Localize in both variables to obtain
a natural isomorphism. Every pair admits such resolutions, proving uniqueness;
naturality with respect to a resolution proves the equation for all complexes. -/
theorem tensorIso_existsUnique (T : Scheme.{u}) :
    ∃! δ, TensorNormalization φ T δ := by
  let E := ProEtale.etaleSheafExtendScalars φ T
  let U := Sheaf.restrictScalars T.smallEtaleTopology φ
  let ad : scalarExtension φ T ⊣ U.mapDerivedCategory := Adjunction.ofIsRightAdjoint _
  let r := adjointRepresentative _root_.DerivedCategory.Q
    _root_.DerivedCategory.Q (E.mapHomologicalComplex (.up ℤ))
    (U.mapHomologicalComplex (.up ℤ)) (scalarExtension φ T) U.mapDerivedCategory ad
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).mapHomologicalComplex (.up ℤ))
    U.mapDerivedCategoryFactors.symm
  have hr' : r.app = scalarExtensionRepresentative φ T := by
    funext P
    unfold scalarExtensionRepresentative
    rw [← mapComplex_unit_formula]
    rfl
  obtain ⟨μ, hμ, hμuniq⟩ := etaleHomTensorComparison_existsUnique T φ
  let δ := productIsoOfFamily
    (derivedTensor (ModuleCat.{u + 1} A) T) (derivedTensor (ModuleCat.{u + 1} B) T)
    (scalarExtension φ T) μ hμ.1 hμ.2.1
  have hflat : EtaleHomTensorModelNormalization (ModuleCat.{u + 1} A)
      (ModuleCat.{u + 1} B) T E (scalarExtension φ T) r.app
      (fun K L ↦ (δ.app (K, L)).symm) := by
    rw [hr']
    exact hμ.2.2
  have hδ : TensorNormalization φ T δ := by
    have h := tensor_normalization_all_onSite (ModuleCat.{u + 1} A)
      (ModuleCat.{u + 1} B) T E (scalarExtension φ T) r δ hflat
    rw [hr'] at h
    exact h
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  have hεcanonical : IsEtaleHomTensorCanonical T φ
      (fun K L ↦ (ε.app (K, L)).symm) := by
    refine ⟨productIso_natural₁ _ _ _ ε,
      productIso_natural₂ _ _ _ ε, ?_⟩
    exact site_normalization_flat (ModuleCat.{u + 1} A)
      (ModuleCat.{u + 1} B) T E (scalarExtension φ T)
      (scalarExtensionRepresentative φ T) ε hε
  have hεμ := hμuniq _ hεcanonical
  apply Iso.ext
  apply NatTrans.ext
  funext ⟨K, L⟩
  have h := congrFun (congrFun hεμ K) L
  exact congrArg Iso.inv h

/-- The same normalized tensor comparison, expressed using the site's tensor functor.
The heterogeneous equality asserts equality of the very same natural isomorphism,
including its endpoints, rather than choosing an unrelated comparison.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison).
Proof: unfold derivedTensor, which is curriedTensor of the canonical derived
monoidal structure. The normalized isomorphism from tensorIso_existsUnique
therefore has exactly this type. Reflexive heterogeneous equality supplies the
witness, and heterogeneous equality to that fixed witness implies uniqueness.
Keeping the transport opaque prevents expansion of the full monoidal structure. -/
theorem siteTensorIso_existsUnique (T : Scheme.{u}) :
    ∃! e : Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) T) ⋙
        scalarExtension φ T ≅
      (scalarExtension φ T).prod (scalarExtension φ T) ⋙
        Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} B) T),
      HEq e (tensorIso_existsUnique φ T).choose := by
  exact ⟨(tensorIso_existsUnique φ T).choose, HEq.rfl, fun _ h ↦ eq_of_heq h⟩

/-- The site's tensor comparison, uniquely equal to the representative-normalized one.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def tensorIso (T : Scheme.{u}) :
    Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) T) ⋙ scalarExtension φ T ≅
      (scalarExtension φ T).prod (scalarExtension φ T) ⋙
        Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} B) T) :=
  (siteTensorIso_existsUnique φ T).choose

/-- Unit normalization using shared monoidal data for the ordinary scalar functor.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def UnitNormalizationAux
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (e : E.obj (𝟙_ _) ≅ 𝟙_ _) : Prop :=
  E.map (Functor.LaxMonoidal.ε _root_.DerivedCategory.Q) ≫ rep (𝟙_ _) ≫
      _root_.DerivedCategory.Q.map (Functor.OplaxMonoidal.mapHomologicalComplexη (.up ℤ) F) =
    e.hom ≫ Functor.LaxMonoidal.ε _root_.DerivedCategory.Q

/-- Specialization of scalar-unit normalization to the ordinary small-etale site.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
abbrev UnitNormalization (T : Scheme.{u}) :=
  UnitNormalizationAux (ProEtale.etaleSheafExtendScalars φ T)
    (scalarExtension φ T) (scalarExtensionRepresentative φ T)

private theorem extension_preservesKFlatQuasiIso {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) (X : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ X).PreservesKFlatQuasiIso := by
  classical
  let E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤ Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} S) :=
    Sheaf.composeAndSheafify X.smallEtaleTopology (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  let U := Sheaf.restrictScalars X.smallEtaleTopology φ
  let adj : E ⊣ U :=
    Sheaf.adjunction X.smallEtaleTopology (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u +
      1} φ)
  have : E.Additive := adj.left_adjoint_additive
  let B := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of S S)
  let coeff := (Functor.const X.Etaleᵒᵖ).obj B
  let a := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)
  let a' := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)
  let F := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)
  let W := (Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  have : X.smallEtaleTopology.PreservesSheafification (ModuleCat.restrictScalars.{u + 1, u + 1, u
    + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction X.smallEtaleTopology
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let e : E ⋙ U ≅ MonoidalCategory.tensorRight (a.obj coeff) :=
    Functor.associator F (W ⋙ a') U ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W a' U) ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft W
        (sheafComposeNatIso X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)
          (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} S))
          (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} R))).symm) ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W _ a).symm ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerRight
        (Functor.whiskeringRightObjCompIso _ _ ≪≫
          (Functor.whiskeringRight _ _ _).mapIso
            (ModuleCat.extendScalarsCompRestrictScalarsIso.{u + 1} φ) ≪≫
          whiskeringRightTensorRightIso _) a) ≪≫
      Functor.isoWhiskerLeft F (Sheaf.presheafToSheafCompTensorRightIso coeff).symm ≪≫
      (Functor.associator F a (MonoidalCategory.tensorRight (a.obj coeff))).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} R)).counit)
        (MonoidalCategory.tensorRight (a.obj coeff)) ≪≫ Functor.leftUnitor _
  have hU : U.Faithful := inferInstance
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{0, 0} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have : HasCountableCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
    ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩
  have hE : E.PreservesKFlatQuasiIso := by
    apply CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'
    intro K hK hKa
    have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa (a.obj coeff)
    have hEU := ht.of_iso
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app K).symm
    have hUK : ((U.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
      hEU.of_iso ((CategoryTheory.Functor.mapHomologicalComplexCompIso
        (Iso.refl (E ⋙ U)) (.up ℤ)).app K)
    intro n
    exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (hUK n)
  exact hE



private theorem unitNormalizationAux_existsUnique
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    [IsIso (Functor.OplaxMonoidal.η F)]
    (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    [IsIso (rep (𝟙_ _))] : ∃! e, UnitNormalizationAux F E rep e := by
  have hC : IsIso (Functor.LaxMonoidal.ε (_root_.DerivedCategory.Q (C := C))) := by
    have := _root_.DerivedCategory.isIso_ε_Qh C
    change IsIso ((Functor.LaxMonoidal.ε _root_.DerivedCategory.Qh ≫
      _root_.DerivedCategory.Qh.map
        (Functor.LaxMonoidal.ε (HomotopyCategory.quotient _ _))) ≫ _)
    infer_instance
  have hD : IsIso (Functor.LaxMonoidal.ε (_root_.DerivedCategory.Q (C := D))) := by
    have := _root_.DerivedCategory.isIso_ε_Qh D
    change IsIso ((Functor.LaxMonoidal.ε _root_.DerivedCategory.Qh ≫
      _root_.DerivedCategory.Qh.map
        (Functor.LaxMonoidal.ε (HomotopyCategory.quotient _ _))) ≫ _)
    infer_instance
  have hη : IsIso (Functor.OplaxMonoidal.mapHomologicalComplexη (.up ℤ) F) := by
    unfold Functor.OplaxMonoidal.mapHomologicalComplexη
    infer_instance
  let a := E.map (Functor.LaxMonoidal.ε _root_.DerivedCategory.Q) ≫ rep (𝟙_ _) ≫
    _root_.DerivedCategory.Q.map
      (Functor.OplaxMonoidal.mapHomologicalComplexη (.up ℤ) F)
  let b := Functor.LaxMonoidal.ε (_root_.DerivedCategory.Q (C := D))
  have : IsIso a := by dsimp only [a]; infer_instance
  refine ⟨asIso a ≪≫ (asIso b).symm, ?_, ?_⟩
  · change a = (a ≫ inv b) ≫ b
    simp
  · intro e he
    apply Iso.ext
    apply (cancel_mono b).1
    change e.hom ≫ b = (a ≫ inv b) ≫ b
    change a = e.hom ≫ b at he
    rw [← he]
    simp

/-- The scalar unit comparison is uniquely normalized by multiplication B tensor_A A -> B.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison).
Proof: the unit complex is flat and K-flat. Its derived counit, the localization
unit comparison and ordinary scalar unit are invertible. Solve the normalization
equation for e; cancellation gives uniqueness. -/
theorem unitIso_existsUnique (T : Scheme.{u}) :
    ∃! e, UnitNormalization φ T e := by
  have h := extension_preservesKFlatQuasiIso φ T
  have hrep : IsIso (scalarExtensionRepresentative φ T
      (𝟙_ (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ))) := by
    unfold scalarExtensionRepresentative
    rw [← mapComplex_unit_formula]
    exact Adjunction.isIso_cochainTranspose_of_kFlat _ _
      (ProEtale.etaleSheafExtendScalarsAdjunction φ T) (Adjunction.ofIsRightAdjoint _) _
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat.prop_unit
  have hη : IsIso (Functor.OplaxMonoidal.η (ProEtale.etaleSheafExtendScalars φ T)) := by
    exact isIso_η_composeAndSheafify T.smallEtaleTopology
      (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)
  exact unitNormalizationAux_existsUnique (ProEtale.etaleSheafExtendScalars φ T)
    (scalarExtension φ T) (scalarExtensionRepresentative φ T)


/-- Canonical scalar unit identification, selected by its unique normalization.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def unitIso (T : Scheme.{u}) :
    (scalarExtension φ T).obj (𝟙_ (DerivedCategoryModule A T)) ≅
      𝟙_ (DerivedCategoryModule B T) :=
  (unitIso_existsUnique φ T).choose

/-- Invertibility of the specified b on its bounded constructible finite-Tor domain.
Source: Stacks 0GL6 (blueprint: lem-pur-exceptional-coefficient-comparison).
Proof: the proper map c.g has Noetherian source: it is of finite type over the
Noetherian target and is quasi-compact. Apply properFiniteCoefficientExtension
to the quotient homomorphism and the open extension of M; its first conclusion
says that the specified scalarMate component is invertible. The open comparison
is an isomorphism by construction, and proper direct image preserves it. The
definition of compactSupportMap is the composite of these two invertible maps.
This argument works on every input; no flatness of the quotient is used. -/
theorem compactSupportMap_isIso
    (l r m d : ℕ) [Fact l.Prime] (hmr : m ≤ r) (_hm : 1 ≤ m)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (_hInvertible : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (c : Compactification f) (M : DerivedCategoryModule (FiniteReduction.Coeff l r) X)
    (hM : DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) X M) :
    IsIso (compactSupportMap (FiniteReduction.quotient l hmr) c M) := by
  have _ := hM
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have := (properFiniteCoefficientExtension (FiniteReduction.quotient l hmr) c.g).1
    ((openImmersionLowerShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r))
      c.i).mapDerivedCategory.obj M)
  unfold compactSupportMap
  infer_instance

/-- Tensor associator for actual consecutive quotient maps, with scalar-adjunction
normalization. Source: blueprint compatibilities (2)
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def quotientAssociator (T : Scheme.{u}) (l : ℕ) {r m n : ℕ}
    (hmr : m ≤ r) (hnm : n ≤ m) :=
  ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology
    (FiniteReduction.quotient.{u} l hmr) (FiniteReduction.quotient l hnm)
    (FiniteReduction.quotient l (hnm.trans hmr))
    (RingHom.ext (fun x ↦
      congrArg (fun y : ZMod (l ^ n) ↦ (⟨⟨y⟩⟩ : FiniteReduction.Coeff.{u} l n))
        (DFunLike.congr_fun
          (Subsingleton.elim
            (ZMod.castHom (pow_dvd_pow l (hnm.trans hmr)) (ZMod (l ^ n)))
            ((ZMod.castHom (pow_dvd_pow l hnm) (ZMod (l ^ n))).comp
              (ZMod.castHom (pow_dvd_pow l hmr) (ZMod (l ^ m))))) x.down.down)))

/-- The quotient cocycle assumed for b, with both canonical associators displayed.
Source: blueprint compatibilities (2)
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def CompactSupportCocycle (l : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] : Prop :=
  ∀ (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m) (_hn : 1 ≤ n)
    (M : DerivedCategoryModule (FiniteReduction.Coeff l r) X),
    DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) X M →
    (quotientAssociator Y l hmr hnm).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj M) ≫
      compactSupportMap (FiniteReduction.quotient l (hnm.trans hmr))
        (HasCompactification.compactification f) M =
    (scalarExtension (FiniteReduction.quotient l hnm) Y).map
        (compactSupportMap (FiniteReduction.quotient l hmr)
          (HasCompactification.compactification f) M) ≫
      compactSupportMap (FiniteReduction.quotient l hnm)
        (HasCompactification.compactification f)
        ((scalarExtension (FiniteReduction.quotient l hmr) X).obj M) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l n)) f).map
        ((quotientAssociator X l hmr hnm).hom.app M)

/-- Scalar transport of the smooth tensor domain, using the canonical tensorator,
pullback balancing and c at the coefficient unit. Source: blueprint compatibilities (3)
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def tensorDomainMap [Finite A] [Finite B] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (K : DerivedCategoryModule A Y) :
    (scalarExtension φ X).obj
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).obj
          (dualizingComplex (ModuleCat.{u + 1} A) f)) ⟶
    ((derivedTensor (ModuleCat.{u + 1} B) X).obj
      ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.obj
        ((scalarExtension φ Y).obj K))).obj (dualizingComplex (ModuleCat.{u + 1} B) f) :=
  (tensorIso φ X).hom.app
    ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K,
      dualizingComplex (ModuleCat.{u + 1} A) f) ≫
    ((derivedTensor (ModuleCat.{u + 1} B) X).map
      ((scalarPullbackIso φ f).inv.app K)).app
        ((scalarExtension φ X).obj (dualizingComplex (ModuleCat.{u + 1} A) f)) ≫
    ((derivedTensor (ModuleCat.{u + 1} B) X).obj
      ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.obj
        ((scalarExtension φ Y).obj K))).map
      (mateMap φ f (constantComplex A Y) ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} B) f).map ((unitIso φ Y).hom))

/-- The smooth tensor-map equation, including the actual scalar-domain transport.
Source: blueprint compatibilities (3)
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def TensorCompatibility [Finite A] [Finite B] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (K : DerivedCategoryModule A Y) : Prop :=
  (scalarExtension φ X).map
      (smoothTensorDualityMap (ModuleCat.{u + 1} A) f
        (isIso_projectionMap_of_finite A f) K) ≫ mateMap φ f K =
    tensorDomainMap φ f K ≫
      smoothTensorDualityMap (ModuleCat.{u + 1} B) f
        (isIso_projectionMap_of_finite B f) ((scalarExtension φ Y).obj K)

/-- The mixed square on the actual Cartesian pullback. Both paths have source
S_X' g'^* G_A K and target G'_B g^* S_Y K; beta is the recorded counit transpose.
Source: Stacks 0F7L and blueprint compatibilities (2)
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def BaseChangeCompatibility [Finite A] [Finite B] {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] (g : Y' ⟶ Y)
    (K : DerivedCategoryModule A Y) : Prop :=
  (scalarExtension φ (pullback f g)).map (smoothExceptionalBaseChangeMap A f g K) ≫
      mateMap φ (pullback.snd f g)
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) ≫
      (rightDerivedUpperShriek (ModuleCat.{u + 1} B) (pullback.snd f g)).map
        ((scalarPullbackIso φ g).inv.app K) =
    (scalarPullbackIso φ (pullback.fst f g)).inv.app
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K) ≫
      (upperStar (ModuleCat.{u + 1} B) (pullback.fst f g)).leftDerivedFunctor.map
        (mateMap φ f K) ≫
      smoothExceptionalBaseChangeMap B f g ((scalarExtension φ Y).obj K)

private def compactSupportNatTrans {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        scalarExtension φ Y ⟶
      scalarExtension φ X ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c :=
  Functor.whiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
      (scalarMate φ c.g) ≫
    Functor.whiskerRight (openIso φ c.i).hom
      (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor

private theorem compactSupport_isIso [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f) (M : DerivedCategoryModule A X) :
    IsIso (compactSupportMap φ c M) := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have := (properFiniteCoefficientExtension φ c.g).1
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)
  unfold compactSupportMap
  infer_instance

private def compactSupportIso [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        scalarExtension φ Y ≅
      scalarExtension φ X ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c := by
  exact NatIso.ofComponents
    (fun M ↦ @asIso _ _ _ _ (compactSupportMap φ c M) (compactSupport_isIso φ c M))
    (fun a ↦ (compactSupportNatTrans φ c).naturality a)

private theorem comparisonInverse_eq [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f) (M : DerivedCategoryModule A X) :
    comparisonInverse φ c M = (compactSupportIso φ c).inv.app M := by
  have := compactSupport_isIso φ c M
  simp only [comparisonInverse, dif_pos this]
  rfl

private theorem mateMap_eq [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule A Y) :
    mateMap φ f K =
      (mateEquiv (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f)
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f)
        (TwoSquare.mk _ _ _ _
          (compactSupportIso φ (HasCompactification.compactification f)).inv)).app K := by
  apply ((rightDerivedUpperShriekAdjunction
    (ModuleCat.{u + 1} B) f).homEquiv _ _).symm.injective
  rw [mateMap, Equiv.symm_apply_apply, Adjunction.homEquiv_counit, mateEquiv_counit]
  rw [comparisonInverse_eq]

private theorem mate_cocycle_at
    {C₁ D₁ C₂ D₂ C₃ D₃ : Type*}
    [Category C₁] [Category D₁] [Category C₂] [Category D₂]
    [Category C₃] [Category D₃]
    {P₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {P₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
    {P₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
    (a₁ : P₁ ⊣ R₁) (a₂ : P₂ ⊣ R₂) (a₃ : P₃ ⊣ R₃)
    {S : C₁ ⥤ C₂} {T : D₁ ⥤ D₂} {U : C₂ ⥤ C₃} {V : D₂ ⥤ D₃}
    {W : C₁ ⥤ C₃} {Z : D₁ ⥤ D₃}
    (α : TwoSquare S P₁ P₂ T) (β : TwoSquare U P₂ P₃ V)
    (γ : TwoSquare W P₁ P₃ Z) (eX : S ⋙ U ≅ W) (eY : T ⋙ V ≅ Z)
    (K : D₁)
    (hc : P₃.map (eX.hom.app (R₁.obj K)) ≫ γ.app (R₁.obj K) =
      β.app (S.obj (R₁.obj K)) ≫ V.map (α.app (R₁.obj K)) ≫
        eY.hom.app (P₁.obj (R₁.obj K))) :
    U.map ((mateEquiv a₁ a₂ α).app K) ≫
        (mateEquiv a₂ a₃ β).app (T.obj K) ≫ R₃.map (eY.hom.app K) =
      eX.hom.app (R₁.obj K) ≫ (mateEquiv a₁ a₃ γ).app K := by
  apply (a₃.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [show P₃.map (R₃.map (eY.hom.app K)) ≫ a₃.counit.app _ =
    a₃.counit.app _ ≫ eY.hom.app K from a₃.counit.naturality _]
  slice_lhs 2 3 => rw [mateEquiv_counit]
  slice_lhs 1 2 => exact β.naturality _
  simp only [Functor.comp_map, Category.assoc]
  slice_lhs 2 3 => rw [← V.map_comp, mateEquiv_counit, V.map_comp]
  simp only [Category.assoc]
  slice_lhs 3 4 => exact eY.hom.naturality (a₁.counit.app K)
  slice_lhs 1 3 => exact hc.symm
  rw [mateEquiv_counit]
  exact Category.assoc _ _ _

end ExceptionalCoefficients


/-- Domain preservation, invertibility, and the counit equation for exceptional coefficients.
Source: blueprint compatibility steps 1 and 4.
Proof: the domain is obtained from finite-reduction constructibility and smooth tensor
transport; the coefficient map is invertible by proper finite coefficient extension and
its counit equation follows by transposing the defining mate.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
theorem exceptional_domain_and_counit
    (l r m d : ℕ) [Fact l.Prime] (hmr : m ≤ r) (hm : 1 ≤ m)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [SmoothOfRelativeDimension d f]
    (hInvertible : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (hb : ExceptionalCoefficients.CompactSupportCocycle l f) :
    (∀ (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) X
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K)) ∧
    (∀ (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      IsIso (ExceptionalCoefficients.compactSupportMap (FiniteReduction.quotient l hmr)
        (HasCompactification.compactification f)
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K)) ∧
      (rightDerivedLowerShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f).map
          (ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hmr) f K) ≫
        (rightDerivedUpperShriekAdjunction
          (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f).counit.app
            ((scalarExtension (FiniteReduction.quotient l hmr) Y).obj K) =
      ExceptionalCoefficients.comparisonInverse (FiniteReduction.quotient l hmr)
        (HasCompactification.compactification f)
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K) ≫
        (scalarExtension (FiniteReduction.quotient l hmr) Y).map
          ((rightDerivedUpperShriekAdjunction
            (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).counit.app K)) := by
  have _ := hb
  have hUnit : IsUnit (l : Γ(Y, ⊤)) := by
    apply Y.toRingedSpace.isUnit_of_isUnit_germ
    intro y hy
    simpa only [map_natCast] using hInvertible y
  have hCoeff : ((l ^ r : ℕ) : FiniteReduction.Coeff.{u} l r) = 0 := by
    apply ULift.ext
    apply ULift.ext
    exact ZMod.natCast_self (l ^ r)
  have : HasInvertibleExponent (FiniteReduction.Coeff.{u} l r) Y :=
    ⟨l ^ r, pow_pos (Fact.out : l.Prime).pos r, hCoeff, by
      simpa only [Nat.cast_pow] using hUnit.pow r⟩
  have hDomain (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y)
      (hK : DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K) :
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) X
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K) := by
    obtain ⟨a, b, ht⟩ := hK.2
    have h := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension
      (FiniteReduction.Coeff l r) f d a b
      ⟨⟨hK.1, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn ht⟩, ht⟩
    exact ⟨h.1.1, _, _, h.2⟩
  refine ⟨hDomain, ?_⟩
  intro K hK
  refine ⟨ExceptionalCoefficients.compactSupportMap_isIso l r m d hmr hm hInvertible
    (HasCompactification.compactification f) _ (hDomain K hK), ?_⟩
  unfold ExceptionalCoefficients.mateMap
  exact ((rightDerivedUpperShriekAdjunction
    (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f).homEquiv _ _).symm_apply_apply _


/-- Naturality and the successive quotient cocycle for exceptional coefficient mates.
Source: blueprint compatibility steps 4--5.
Proof: transpose both sides under the exceptional adjunction; naturality of the mate
and the counit gives the first equality, and vertical mate pasting plus the assumed
compact-support cocycle gives the successive quotient equality.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
theorem exceptional_naturality_and_cocycle
    (l r m d : ℕ) [Fact l.Prime] (hmr : m ≤ r) (hm : 1 ≤ m)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [SmoothOfRelativeDimension d f]
    (hInvertible : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (hb : ExceptionalCoefficients.CompactSupportCocycle l f) :
    (∀ (K K' : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K' →
      ∀ h : K ⟶ K',
        (scalarExtension (FiniteReduction.quotient l hmr) X).map
            ((rightDerivedUpperShriek
              (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).map h) ≫
          ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hmr) f K' =
        ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hmr) f K ≫
          (rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f).map
            ((scalarExtension (FiniteReduction.quotient l hmr) Y).map h)) ∧
    (∀ (n : ℕ) (hnm : n ≤ m) (_hn : 1 ≤ n)
      (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      (scalarExtension (FiniteReduction.quotient l hnm) X).map
          (ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hmr) f K) ≫
        ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hnm) f
          ((scalarExtension (FiniteReduction.quotient l hmr) Y).obj K) ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l n)) f).map
          ((ExceptionalCoefficients.quotientAssociator Y l hmr hnm).hom.app K) =
      (ExceptionalCoefficients.quotientAssociator X l hmr hnm).hom.app
          ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K) ≫
        ExceptionalCoefficients.mateMap (FiniteReduction.quotient l (hnm.trans hmr)) f K) := by
  constructor
  · intro K K' hK hK' h
    have _ := hK
    have _ := hK'
    simp only [ExceptionalCoefficients.mateMap_eq]
    exact (mateEquiv
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f)
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f)
      (TwoSquare.mk _ _ _ _ (ExceptionalCoefficients.compactSupportIso
        (FiniteReduction.quotient l hmr)
        (HasCompactification.compactification f)).inv)).naturality h
  · intro n hnm hn K hK
    let c := HasCompactification.compactification f
    let S := scalarExtension (FiniteReduction.quotient l hmr) X
    let T := scalarExtension (FiniteReduction.quotient l hmr) Y
    let U := scalarExtension (FiniteReduction.quotient l hnm) X
    let V := scalarExtension (FiniteReduction.quotient l hnm) Y
    let W := scalarExtension (FiniteReduction.quotient l (hnm.trans hmr)) X
    let Z := scalarExtension (FiniteReduction.quotient l (hnm.trans hmr)) Y
    let P₁ := rightDerivedLowerShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f
    let P₂ := rightDerivedLowerShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f
    let P₃ := rightDerivedLowerShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l n)) f
    let R₁ := rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f
    let i₁₂ := ExceptionalCoefficients.compactSupportIso (FiniteReduction.quotient l hmr) c
    let i₂₃ := ExceptionalCoefficients.compactSupportIso (FiniteReduction.quotient l hnm) c
    let i₁₃ := ExceptionalCoefficients.compactSupportIso
      (FiniteReduction.quotient l (hnm.trans hmr)) c
    let eX := ExceptionalCoefficients.quotientAssociator X l hmr hnm
    let eY := ExceptionalCoefficients.quotientAssociator Y l hmr hnm
    let M := R₁.obj K
    have hM := (exceptional_domain_and_counit l r m d hmr hm f hInvertible hb).1 K hK
    have hcomp := hb r m n hmr hnm hn M hM
    change eY.hom.app (P₁.obj M) ≫ i₁₃.hom.app M =
      V.map (i₁₂.hom.app M) ≫ i₂₃.hom.app (S.obj M) ≫ P₃.map (eX.hom.app M) at hcomp
    have hc : P₃.map (eX.hom.app M) ≫ i₁₃.inv.app M =
        i₂₃.inv.app (S.obj M) ≫ V.map (i₁₂.inv.app M) ≫ eY.hom.app (P₁.obj M) := by
      apply (cancel_epi (V.map (i₁₂.hom.app M) ≫ i₂₃.hom.app (S.obj M))).1
      calc
        _ = (eY.hom.app (P₁.obj M) ≫ i₁₃.hom.app M) ≫ i₁₃.inv.app M := by
          rw [hcomp]
          simp only [Category.assoc]
        _ = eY.hom.app (P₁.obj M) := by
          simp only [Category.assoc, Iso.hom_inv_id_app]
          exact Category.comp_id _
        _ = _ := by
          simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
            ← V.map_comp_assoc, Iso.hom_inv_id_app, V.map_id, Category.id_comp]
    have h := ExceptionalCoefficients.mate_cocycle_at
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f)
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f)
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} (FiniteReduction.Coeff l n)) f)
      (TwoSquare.mk S P₁ P₂ T i₁₂.inv) (TwoSquare.mk U P₂ P₃ V i₂₃.inv)
      (TwoSquare.mk W P₁ P₃ Z i₁₃.inv) eX eY K hc
    simpa only [ExceptionalCoefficients.mateMap_eq] using h


/-- Tensor and Cartesian base-change compatibilities for exceptional coefficient mates.
Source: blueprint compatibility steps 6--10.
Proof: compare proper projection maps by ringed exchange, compare open extension by
zero on stalks, and transpose the resulting compact-support square and smooth tensor
square through the exceptional adjunctions.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
theorem exceptional_tensor_and_base_change
    (l r m d : ℕ) [Fact l.Prime] (hmr : m ≤ r) (hm : 1 ≤ m)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [SmoothOfRelativeDimension d f]
    (hInvertible : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (hb : ExceptionalCoefficients.CompactSupportCocycle l f) :
    (∀ (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      ExceptionalCoefficients.TensorCompatibility (FiniteReduction.quotient l hmr) f K) ∧
    (∀ (Y' : Scheme.{u}) [IsNoetherian Y'] (g : Y' ⟶ Y)
      (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      ExceptionalCoefficients.BaseChangeCompatibility (FiniteReduction.quotient l hmr) f g K) := by
  sorry

/-- Exceptional comparison for consecutive finite quotient coefficients, including
its domain, counit identity, naturality, quotient cocycle, tensor and Cartesian
base-change compatibilities. Source: blueprint main-20261015, sec-smooth-purity/
sk-lem-sp-reduction/sk-lem-sp-reduction-compatibilities.proof.md (2)--(3);
Stacks 0GL6 and 0F7L (blueprint: lem-pur-exceptional-coefficient-comparison).

Proof:
1. Use the finite-ring origin equivalence and the Noetherian Tor comparison solely
to check domains. Finite reduction on bounded flat models preserves bounded
constructibility and finite Tor amplitude; quotient maps need not be flat.
2. Smooth tensor duality writes G_A K as f^*K tensor L[2d], with L locally free
of rank one. Pullback preserves flat K-flat models. Thus a model in [a,b]
becomes one in [a-2d,b-2d]; the flat-model Tor criterion applies.
3. Exact inverse image preserves constructible cohomology. Trivialize L on a
finite affine etale cover and descend constructibility along its qcqs surjection.
This proves the domain conclusion and hence invertibility of b at G_A K.
4. Transpose the defining mateMap under P_B adjoint G_B. Its transpose is
b inverse followed by scalar extension of the A-counit. Naturality of b and
of the counits makes the two transposes of the naturality equation equal.
5. For r -> m -> n transpose the two-step c under P_n adjoint G_n. Move c_r,m
past b_m,n by naturality, substitute both counit identities and apply the
assumed b cocycle. The normalized tensor associators give the displayed equation.
6. Proper projection and coefficient change commute by the ringed exchange/tensor
identity. For the open constituent both composites are the same balancing map on
the open and zero outside. Compose these statements on the compactification.
7. At M=omega, transpose the tensor equation. Substitute the c counit identity
at the coefficient unit. The inverse of Step 6's projection identity gives equal
transposes. The normalized unit comparison identifies S(A_Y) with B_Y.
8. In a Cartesian square, proper exchange and coefficient change are mates of
the same pulled-back proper counit. Pullback/scalar balancing agrees in both orders.
9. Open base change and coefficient change commute before deriving: on the
pulled-back open they are identity and balancing; off it both are zero. Combining
with Step 8 yields the mixed compact-support exchange square.
10. Transpose the two paths of BaseChangeCompatibility through P'_B adjoint G'_B.
Naturality and the defining identities of c and beta reduce them to the inverse
of Step 9's square followed by the same scalar/pullback A-counit. Injectivity
of the adjunction bijection proves equality. No inverse of c is used.
-/
theorem exceptional_coefficient_comparison
    (l r m d : ℕ) [Fact l.Prime] (hmr : m ≤ r) (hm : 1 ≤ m)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [SmoothOfRelativeDimension d f]
    (hInvertible : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (hb : ExceptionalCoefficients.CompactSupportCocycle l f) :
    (∀ (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) X
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K)) ∧
    (∀ (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      IsIso (ExceptionalCoefficients.compactSupportMap (FiniteReduction.quotient l hmr)
        (HasCompactification.compactification f)
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K)) ∧
      (rightDerivedLowerShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f).map
          (ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hmr) f K) ≫
        (rightDerivedUpperShriekAdjunction
          (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f).counit.app
            ((scalarExtension (FiniteReduction.quotient l hmr) Y).obj K) =
      ExceptionalCoefficients.comparisonInverse (FiniteReduction.quotient l hmr)
        (HasCompactification.compactification f)
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K) ≫
        (scalarExtension (FiniteReduction.quotient l hmr) Y).map
          ((rightDerivedUpperShriekAdjunction
            (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).counit.app K)) ∧
    (∀ (K K' : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K' →
      ∀ h : K ⟶ K',
        (scalarExtension (FiniteReduction.quotient l hmr) X).map
            ((rightDerivedUpperShriek
              (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).map h) ≫
          ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hmr) f K' =
        ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hmr) f K ≫
          (rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l m)) f).map
            ((scalarExtension (FiniteReduction.quotient l hmr) Y).map h)) ∧
    (∀ (n : ℕ) (hnm : n ≤ m) (_hn : 1 ≤ n)
      (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      (scalarExtension (FiniteReduction.quotient l hnm) X).map
          (ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hmr) f K) ≫
        ExceptionalCoefficients.mateMap (FiniteReduction.quotient l hnm) f
          ((scalarExtension (FiniteReduction.quotient l hmr) Y).obj K) ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l n)) f).map
          ((ExceptionalCoefficients.quotientAssociator Y l hmr hnm).hom.app K) =
      (ExceptionalCoefficients.quotientAssociator X l hmr hnm).hom.app
          ((rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l r)) f).obj K) ≫
        ExceptionalCoefficients.mateMap (FiniteReduction.quotient l (hnm.trans hmr)) f K) ∧
    (∀ (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      ExceptionalCoefficients.TensorCompatibility (FiniteReduction.quotient l hmr) f K) ∧
    (∀ (Y' : Scheme.{u}) [IsNoetherian Y'] (g : Y' ⟶ Y)
      (K : DerivedCategoryModule (FiniteReduction.Coeff l r) Y),
      DerivedCategory.boundedConstructibleFiniteTor (FiniteReduction.Coeff l r) Y K →
      ExceptionalCoefficients.BaseChangeCompatibility (FiniteReduction.quotient l hmr) f g K) := by
  obtain ⟨h₁, h₂⟩ := exceptional_domain_and_counit l r m d hmr hm f hInvertible hb
  obtain ⟨h₃, h₄⟩ := exceptional_naturality_and_cocycle l r m d hmr hm f hInvertible hb
  obtain ⟨h₅, h₆⟩ := exceptional_tensor_and_base_change l r m d hmr hm f hInvertible hb
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩

end AlgebraicGeometry.Etale
