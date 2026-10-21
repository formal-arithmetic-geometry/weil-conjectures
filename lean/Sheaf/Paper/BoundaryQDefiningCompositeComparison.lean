/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q96
-/
module

public import Sheaf.Paper.BoundaryExceptionalComparisonData
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.CategoryTheory.Monoidal.Braided.Adjunction

/-! # Comparison of the untransposed boundary tensor composites

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-pf-proetale,
`thm-sf-pf-proetale.proof.md`, comparison paragraph; expanded calculation in
`lem-weil-boundary-proetale-q-compatibility`, step 1
(blueprint: lem-weil-boundary-q-defining-composite-comparison).

The helpers are the three explicit composites s, r and t_e in the node. The pro-etale
composite is expanded in the conclusion, using the same existing projection and braiding.
All tensor products lie in the ambient unbounded derived categories, including when the four
input objects are bounded below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
variable {C : Type v} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type w} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  (hF : ∀ X Y : C, F.map (β_ X Y).hom ≫ δ F Y X =
    δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)

private theorem comparison_fac (P Q : HomotopyCategory C (.up ℤ)) :
    ((F.leftDerivedTensorComparison.app (DerivedCategory.Qh.obj P)).app
      (DerivedCategory.Qh.obj Q)) ≫
      (F.leftDerivedFunctorCounit.app P ⊗ₘ F.leftDerivedFunctorCounit.app Q) ≫
      μ DerivedCategory.Qh ((F.mapHomotopyCategory (.up ℤ)).obj P)
        ((F.mapHomotopyCategory (.up ℤ)).obj Q) =
    F.leftDerivedFunctor.map (μ DerivedCategory.Qh P Q) ≫
      F.leftDerivedFunctorCounit.app (P ⊗ Q) ≫
      DerivedCategory.Qh.map (δ (F.mapHomotopyCategory (.up ℤ)) P Q) := by
  have h := F.leftDerivedTensorComparison_app_app_comp_counit P Q
  have he : (F.derivedTensorLeftDerivedCounit.app P).app Q =
      (F.leftDerivedFunctorCounit.app P ⊗ₘ F.leftDerivedFunctorCounit.app Q) ≫
        μ DerivedCategory.Qh ((F.mapHomotopyCategory (.up ℤ)).obj P)
          ((F.mapHomotopyCategory (.up ℤ)).obj Q) := by
    rw [MonoidalCategory.tensorHom_def]
    dsimp [CategoryTheory.Functor.derivedTensorLeftDerivedCounit]
    rw [Category.assoc]
    rfl
  rw [he] at h
  have he₂ : (F.leftDerivedDerivedTensorCounit.app P).app Q =
      F.leftDerivedFunctor.map (μ DerivedCategory.Qh P Q) ≫
        F.leftDerivedFunctorCounit.app (P ⊗ Q) := rfl
  rw [he₂] at h
  simpa only [CategoryTheory.Functor.mapHomotopyCategory_δ, Category.assoc] using h

include hF in
private theorem comparison_braiding_Qh (P Q : HomotopyCategory C (.up ℤ))
    (hP : F.kFlatMap P) :
    F.leftDerivedFunctor.map (β_ (DerivedCategory.Qh.obj P)
      (DerivedCategory.Qh.obj Q)).hom ≫
      (F.leftDerivedTensorComparison.app (DerivedCategory.Qh.obj Q)).app
        (DerivedCategory.Qh.obj P) =
    (F.leftDerivedTensorComparison.app (DerivedCategory.Qh.obj P)).app
      (DerivedCategory.Qh.obj Q) ≫
      (β_ (F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P))
        (F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj Q))).hom := by
  have : IsIso (μ DerivedCategory.Qh ((F.mapHomotopyCategory (.up ℤ)).obj Q)
      ((F.mapHomotopyCategory (.up ℤ)).obj P)) :=
    CategoryTheory.Functor.isIso_μNatTrans_Qh_app_app_of_kFlat _ _ hP
  rw [← cancel_mono ((F.leftDerivedFunctorCounit.app Q ⊗ₘ
    F.leftDerivedFunctorCounit.app P) ≫
    μ DerivedCategory.Qh ((F.mapHomotopyCategory (.up ℤ)).obj Q)
      ((F.mapHomotopyCategory (.up ℤ)).obj P))]
  simp only [Category.assoc]
  rw [comparison_fac, ← BraidedCategory.braiding_naturality_assoc]
  have hβ : (β_ (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj P))
      (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj Q))).hom ≫
      μ DerivedCategory.Qh ((F.mapHomotopyCategory (.up ℤ)).obj Q)
        ((F.mapHomotopyCategory (.up ℤ)).obj P) =
      μ DerivedCategory.Qh ((F.mapHomotopyCategory (.up ℤ)).obj P)
        ((F.mapHomotopyCategory (.up ℤ)).obj Q) ≫
        DerivedCategory.Qh.map (β_ ((F.mapHomotopyCategory (.up ℤ)).obj P)
          ((F.mapHomotopyCategory (.up ℤ)).obj Q)).hom :=
    DerivedCategory.braidedCategory_braiding_hom_μ_Qh D _ _
  erw [hβ]
  rw [reassoc_of% comparison_fac F P Q]
  rw [← Functor.map_comp_assoc, DerivedCategory.braidedCategory_braiding_hom_μ_Qh,
    Functor.map_comp_assoc]
  erw [F.leftDerivedFunctorCounit.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_comp,
    CategoryTheory.Functor.mapHomotopyCategory_map_braiding_hom_δ F hF P Q]

include hF in
private theorem comparison_braiding (K M : DerivedCategory C) :
    F.leftDerivedFunctor.map (β_ K M).hom ≫
      (F.leftDerivedTensorComparison.app M).app K =
    (F.leftDerivedTensorComparison.app K).app M ≫
      (β_ (F.leftDerivedFunctor.obj K) (F.leftDerivedFunctor.obj M)).hom := by
  have he : ∀ X : DerivedCategory C, ∃ P, F.kFlatMap P ∧
      Nonempty (DerivedCategory.Qh.obj P ≅ X) := by
    intro X
    have := Localization.essSurj (DerivedCategory.Qh (C := C))
      (HomotopyCategory.quasiIso _ (.up ℤ))
    obtain ⟨R⟩ := LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
      (Φ := HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatMap)
      (DerivedCategory.Qh.objPreimage X)
    have : IsIso (DerivedCategory.Qh.map R.w) :=
      Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _ R.hw
    exact ⟨R.X₁.obj, R.X₁.property,
      ⟨asIso (DerivedCategory.Qh.map R.w) ≪≫ DerivedCategory.Qh.objObjPreimageIso X⟩⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := he K
  obtain ⟨Q, _, ⟨eQ⟩⟩ := he M
  rw [← cancel_epi (F.leftDerivedFunctor.map (eP.hom ⊗ₘ eQ.hom)),
    ← F.leftDerivedFunctor.map_comp_assoc, BraidedCategory.braiding_naturality,
    F.leftDerivedFunctor.map_comp_assoc,
    CategoryTheory.Functor.leftDerivedTensorComparison_naturality_tensorHom,
    reassoc_of% comparison_braiding_Qh F hF P Q hP,
    ← BraidedCategory.braiding_naturality,
    ← CategoryTheory.Functor.leftDerivedTensorComparison_naturality_tensorHom_assoc]

namespace AlgebraicGeometry.ProEtale
open BoundaryComparison
variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  (W : Scheme.{u}) [(comparisonUpperStar A W).PreservesFlat]
private theorem comparisonTensor_hom (K M : DerivedCategory (Sheaf W.smallEtaleTopology A)) :
    ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A K).app M).hom =
    (comparisonUpperStar A W).leftDerivedFunctorIsoMapDerivedCategory.inv.app (K ⊗ M) ≫
      (((comparisonUpperStar A W).leftDerivedTensorComparison.app K).app M) ≫
      ((comparisonUpperStar A W).leftDerivedFunctorIsoMapDerivedCategory.hom.app K ⊗ₘ
        (comparisonUpperStar A W).leftDerivedFunctorIsoMapDerivedCategory.hom.app M) := by
  rw [tensorHom_def']
  rfl

@[reassoc]
private theorem comparisonTensor_naturality
    {K K' M M' : DerivedCategory (Sheaf W.smallEtaleTopology A)}
    (f : K ⟶ K') (g : M ⟶ M') :
    (comparison A W).map (f ⊗ₘ g) ≫
      ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A K').app M').hom =
    ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A K).app M).hom ≫
      ((comparison A W).map f ⊗ₘ (comparison A W).map g) := by
  rw [comparisonTensor_hom, comparisonTensor_hom]
  rw [NatTrans.naturality_assoc,
    CategoryTheory.Functor.leftDerivedTensorComparison_naturality_tensorHom_assoc]
  simp only [Category.assoc]
  congr 2
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  rw [NatTrans.naturality, NatTrans.naturality]

@[reassoc]
private theorem comparisonTensor_braiding
    (K M : DerivedCategory (Sheaf W.smallEtaleTopology A)) :
    (comparison A W).map (β_ K M).hom ≫
      ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A M).app K).hom =
    ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A K).app M).hom ≫
      (β_ ((comparison A W).obj K) ((comparison A W).obj M)).hom := by
  let : (comparisonLowerStar A W).LaxBraided := by
    unfold comparisonLowerStar
    infer_instance
  rw [comparisonTensor_hom, comparisonTensor_hom, NatTrans.naturality_assoc]
  rw [reassoc_of% comparison_braiding (comparisonUpperStar A W)
    (fun X Y ↦ by
      simpa only [Functor.OplaxMonoidal.δ, monoidal_comparisonUpperStar,
        Functor.Monoidal.ofOplaxMonoidal,
        Functor.CoreMonoidal.toMonoidal, Functor.CoreMonoidal.toOplaxMonoidal,
        Functor.CoreMonoidal.ofOplaxMonoidal, oplaxMonoidal_comparisonUpperStar,
        Iso.symm_inv, asIso_hom]
        using ((comparisonAdjunction A W).leftAdjointOplaxMonoidal_δ_braiding X Y).symm) K M]
  rw [← BraidedCategory.braiding_naturality]
  simp only [Category.assoc]
end AlgebraicGeometry.ProEtale

private theorem inverse_square {E : Type*} [Category E]
    {U V W X Y Z : E} (a : U ≅ V) (p : V ⟶ W) [IsIso p]
    (h : W ⟶ Z) (q : Y ⟶ Z) [IsIso q] (k : Y ≅ X) (e : U ⟶ X)
    (hs : a.hom ≫ p ≫ h = e ≫ k.inv ≫ q) :
    h ≫ inv q ≫ k.hom = inv p ≫ a.inv ≫ e := by
  apply (cancel_epi (a.hom ≫ p)).1
  calc
    (a.hom ≫ p) ≫ h ≫ inv q ≫ k.hom =
        (a.hom ≫ p ≫ h) ≫ inv q ≫ k.hom := by simp only [Category.assoc]
    _ = (e ≫ k.inv ≫ q) ≫ inv q ≫ k.hom := by rw [hs]
    _ = e := by simp
    _ = (a.hom ≫ p) ≫ inv p ≫ a.inv ≫ e := by simp

namespace AlgebraicGeometry.ProEtale.BoundaryComparisonOfCoefficients

open BoundaryComparison

section Composites

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [Etale.UpperStarPreservesFlat C] [ProEtale.UpperStarPreservesFlat C]
  [∀ W : Scheme.{u}, (comparisonUpperStar C W).PreservesFlat]

/-- The node's s: tensor comparison, rho inverse in the first factor, and v in the second.
Source: blueprint projection-comparison paragraph, displayed definition of s
(blueprint: lem-weil-boundary-q-defining-composite-comparison). -/
def boundaryDefiningSourceIso {Z T : Scheme.{u}} (i : Z ⟶ T)
    (M : DerivedCategory (Sheaf T.smallEtaleTopology C))
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (B' : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C))
    (v : (comparison C Z).obj B ≅ B') :
    (comparison C Z).obj
      (((Etale.derivedTensor C Z).obj
        ((Etale.upperStar C i).leftDerivedFunctor.obj M)).obj B) ≅
      ((ProEtale.derivedTensor C Z).obj
        ((upperStar C i).leftDerivedFunctor.obj ((comparison C T).obj M))).obj B' :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso C
    ((Etale.upperStar C i).leftDerivedFunctor.obj M)).app B ≪≫
    ((ProEtale.derivedTensor C Z).mapIso ((pullbackSquare C i).symm.app M)).app
      ((comparison C Z).obj B) ≪≫
    ((ProEtale.derivedTensor C Z).obj
      ((upperStar C i).leftDerivedFunctor.obj ((comparison C T).obj M))).mapIso v

/-- The node's r: tensor comparison, v in the first factor, and rho inverse in the second.
Source: blueprint projection-comparison paragraph, displayed definition of r
(blueprint: lem-weil-boundary-q-defining-composite-comparison). -/
def boundaryDefiningTargetIso {Z T : Scheme.{u}} (i : Z ⟶ T)
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (M : DerivedCategory (Sheaf T.smallEtaleTopology C))
    (B' : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C))
    (v : (comparison C Z).obj B ≅ B') :
    (comparison C Z).obj (((Etale.derivedTensor C Z).obj B).obj
        ((Etale.upperStar C i).leftDerivedFunctor.obj M)) ≅
      ((ProEtale.derivedTensor C Z).obj B').obj
        ((upperStar C i).leftDerivedFunctor.obj ((comparison C T).obj M)) :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso C B).app
      ((Etale.upperStar C i).leftDerivedFunctor.obj M) ≪≫
    ((ProEtale.derivedTensor C Z).obj ((comparison C Z).obj B)).mapIso
      ((pullbackSquare C i).symm.app M) ≪≫
    ((ProEtale.derivedTensor C Z).mapIso v).app
      ((upperStar C i).leftDerivedFunctor.obj ((comparison C T).obj M))

/-- The node's t_e, for an arbitrary final arrow a_e, before any exceptional adjunction.
Source: blueprint projection-comparison paragraph, displayed definition of t_e
(blueprint: lem-weil-boundary-q-defining-composite-comparison). -/
def boundaryEtaleDefiningComposite {Z T : Scheme.{u}} (i : Z ⟶ T)
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (M Y : DerivedCategory (Sheaf T.smallEtaleTopology C))
    (a : (etaleImage C i).obj B ⟶ Y)
    [IsIso (((Etale.rightDerivedLowerStarProjectionMap C i).app B).app M)] :
    (etaleImage C i).obj
      (((Etale.derivedTensor C Z).obj
        ((Etale.upperStar C i).leftDerivedFunctor.obj M)).obj B) ⟶
      ((Etale.derivedTensor C T).obj M).obj Y :=
  (etaleImage C i).map
      (β_ ((Etale.upperStar C i).leftDerivedFunctor.obj M) B).hom ≫
    inv (((Etale.rightDerivedLowerStarProjectionMap C i).app B).app M) ≫
    (β_ ((etaleImage C i).obj B) M).hom ≫
    ((Etale.derivedTensor C T).obj M).map a


/-- The displayed comparison assertion as a predicate over the existing coefficient interface.
This only packages the node's quantified input objects, compatible arrows, invertible
projection components, specified square and conclusion; it supplies no assumptions.
Source: blueprint projection-comparison paragraph, all displayed formulas
(blueprint: lem-weil-boundary-q-defining-composite-comparison). -/
def BoundaryDefiningCompositeComparison {Z T : Scheme.{u}} (i : Z ⟶ T) : Prop :=
  ∀ (η : comparison C Z ⋙ proetaleImage C i ≅
      etaleImage C i ⋙ comparison C T)
    (B : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology C))
    (M Y : DerivedCategory.Plus (Sheaf T.smallEtaleTopology C))
    (B' : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Z) C))
    (v : (comparison C Z).obj B.obj ≅ B'.obj)
    (ae : (etaleImage C i).obj B.obj ⟶ Y.obj)
    (ap : (proetaleImage C i).obj B'.obj ⟶
      (comparison C T).obj Y.obj)
    (_ha : (proetaleImage C i).map v.hom ≫ ap =
      η.hom.app B.obj ≫ (comparison C T).map ae)
    [IsIso (((Etale.rightDerivedLowerStarProjectionMap
      C i).app B.obj).app M.obj)]
    [IsIso (((rightDerivedLowerStarProjectionMap C i).app B'.obj).app
      ((comparison C T).obj M.obj))]
    (_hπ :
      ((ProEtale.derivedTensor C T).map
        ((proetaleImage C i).map v.hom)).app
          ((comparison C T).obj M.obj) ≫
        ((rightDerivedLowerStarProjectionMap C i).app B'.obj).app
          ((comparison C T).obj M.obj) ≫
        (proetaleImage C i).map
          (boundaryDefiningTargetIso C i B.obj M.obj B'.obj v).inv ≫
        η.hom.app (((Etale.derivedTensor C Z).obj B.obj).obj
          ((Etale.upperStar C i).leftDerivedFunctor.obj M.obj)) =
      ((ProEtale.derivedTensor C T).map (η.hom.app B.obj)).app
          ((comparison C T).obj M.obj) ≫
        ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso C
          ((etaleImage C i).obj B.obj)).app M.obj).inv ≫
        (comparison C T).map
          (((Etale.rightDerivedLowerStarProjectionMap
            C i).app B.obj).app M.obj)),
    η.hom.app
        (((Etale.derivedTensor C Z).obj
          ((Etale.upperStar C i).leftDerivedFunctor.obj M.obj)).obj B.obj) ≫
      (comparison C T).map
        (boundaryEtaleDefiningComposite C i B.obj M.obj Y.obj ae) ≫
      ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        C M.obj).app Y.obj).hom =
    (proetaleImage C i).map
        (boundaryDefiningSourceIso C i M.obj B.obj B'.obj v).hom ≫
      (proetaleImage C i).map
        (β_ ((upperStar C i).leftDerivedFunctor.obj ((comparison C T).obj M.obj)) B'.obj).hom ≫
      inv (((rightDerivedLowerStarProjectionMap C i).app B'.obj).app
        ((comparison C T).obj M.obj)) ≫
      (β_ ((proetaleImage C i).obj B'.obj) ((comparison C T).obj M.obj)).hom ≫
      ((ProEtale.derivedTensor C T).obj
        ((comparison C T).obj M.obj)).map ap

end Composites

attribute [local irreducible] BoundaryComparison.pullbackSquare
  derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso

set_option maxHeartbeats 800000 in
-- Keep the native tensor comparison opaque while checking the complete diagram.
private theorem boundary_composite_native
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [Etale.UpperStarPreservesFlat C] [ProEtale.UpperStarPreservesFlat C]
    [∀ W : Scheme.{u}, (comparisonUpperStar C W).PreservesFlat]
    {Z T : Scheme.{u}} (i : Z ⟶ T) : BoundaryDefiningCompositeComparison C i := by
  intro η B M Y B' v ae ap ha _ _ hπ
  let CT := comparison C T
  let CZ := comparison C Z
  let FE := etaleImage C i
  let FP := proetaleImage C i
  let L := (Etale.upperStar C i).leftDerivedFunctor.obj M.obj
  let L' := (upperStar C i).leftDerivedFunctor.obj (CT.obj M.obj)
  let s := boundaryDefiningSourceIso C i M.obj B.obj B'.obj v
  let r := boundaryDefiningTargetIso C i B.obj M.obj B'.obj v
  let k := (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso C
    (FE.obj B.obj)).app M.obj
  let qE := ((Etale.rightDerivedLowerStarProjectionMap C i).app B.obj).app M.obj
  let qP := ((rightDerivedLowerStarProjectionMap C i).app B'.obj).app (CT.obj M.obj)
  let V := FP.mapIso v
  let cMY := (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso C M.obj).app Y.obj
  have hs : s.hom ≫ (β_ L' B'.obj).hom = CZ.map (β_ L B.obj).hom ≫ r.hom := by
    change _ ≫ _ = _ ≫ _
    dsimp only [s, r, boundaryDefiningSourceIso, boundaryDefiningTargetIso]
    simp only [Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc]
    change _ ≫ _ ▷ _ ≫ _ ◁ _ ≫ _ = _ ≫ _ ≫ _ ◁ _ ≫ _ ▷ _
    rw [← MonoidalCategory.tensorHom_def_assoc]
    erw [BraidedCategory.braiding_naturality]
    rw [← comparisonTensor_braiding_assoc C Z L B.obj]
    rw [MonoidalCategory.tensorHom_def']
    rfl
  have hin : η.hom.app (L ⊗ B.obj) ≫ CT.map (FE.map (β_ L B.obj).hom) =
      FP.map s.hom ≫ FP.map (β_ L' B'.obj).hom ≫
        FP.map r.inv ≫ η.hom.app (B.obj ⊗ L) := by
    rw [← FP.map_comp_assoc, hs, FP.map_comp_assoc]
    simp only [← FP.map_comp_assoc, r.hom_inv_id]
    erw [Category.comp_id]
    exact (η.hom.naturality (β_ L B.obj).hom).symm
  have hπ' : (V.hom ▷ CT.obj M.obj) ≫ qP ≫ FP.map r.inv ≫
        η.hom.app (B.obj ⊗ L) =
      (η.hom.app B.obj ▷ CT.obj M.obj) ≫ k.inv ≫ CT.map qE := hπ
  have hinv : FP.map r.inv ≫ η.hom.app (B.obj ⊗ L) ≫
        CT.map (inv qE) ≫ k.hom =
      inv qP ≫ (V.inv ▷ CT.obj M.obj) ≫ (η.hom.app B.obj ▷ CT.obj M.obj) := by
    have hh := inverse_square (MonoidalCategory.whiskerRightIso V (CT.obj M.obj)) qP
      (FP.map r.inv ≫ η.hom.app (B.obj ⊗ L)) (CT.map qE) k
      (η.hom.app B.obj ▷ CT.obj M.obj) hπ'
    simpa only [Functor.map_inv, MonoidalCategory.whiskerRightIso_inv, Category.assoc] using hh
  have hout : CT.map (β_ (FE.obj B.obj) M.obj).hom ≫
        CT.map (M.obj ◁ ae) ≫ cMY.hom =
      k.hom ≫ (β_ (CT.obj (FE.obj B.obj)) (CT.obj M.obj)).hom ≫
        (CT.obj M.obj ◁ CT.map ae) := by
    have hn := comparisonTensor_naturality C T (𝟙 M.obj) ae
    simp only [id_tensorHom] at hn
    rw [hn, comparisonTensor_braiding_assoc C T (FE.obj B.obj) M.obj]
    rw [CategoryTheory.Functor.map_id, id_tensorHom]
  have ha' : V.inv ≫ η.hom.app B.obj ≫ CT.map ae = ap := by
    rw [← ha]
    change V.inv ≫ V.hom ≫ ap = ap
    simp only [← Category.assoc, V.inv_hom_id, Category.id_comp]
  change η.hom.app (L ⊗ B.obj) ≫
      CT.map (FE.map (β_ L B.obj).hom ≫ inv qE ≫
        (β_ (FE.obj B.obj) M.obj).hom ≫ (M.obj ◁ ae)) ≫ cMY.hom =
    FP.map s.hom ≫ FP.map (β_ L' B'.obj).hom ≫ inv qP ≫
      (β_ (FP.obj B'.obj) (CT.obj M.obj)).hom ≫ (CT.obj M.obj ◁ ap)
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hin, hout, reassoc_of% hinv]
  rw [BraidedCategory.braiding_naturality_left_assoc,
    BraidedCategory.braiding_naturality_left_assoc]
  simp only [← whiskerLeft_comp, ha']


/-- Canonical comparison identifies the two projection-inverse/symmetry/final-arrow
composites. The symmetry is the actual descended Koszul braiding
`DerivedCategory.braidedCategory`, with no supplied symmetry or coherence assumptions. The ordinary
exact
inverse images are written through their canonical left-derived identifications in
`pullbackSquare` and the two ordinary projection transformations. No exceptional
right adjoint, constructibility or Tor-amplitude hypothesis occurs.

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-pf-proetale,
`thm-sf-pf-proetale.proof.md`, comparison paragraph; expanded calculation in
`lem-weil-boundary-proetale-q-compatibility`, step 1
(blueprint: lem-weil-boundary-q-defining-composite-comparison).

Proof:
1. Compute the native tensor comparison on K-flat representatives using its derived
   counit characterization. The native signed braiding formulas, the ordinary pullback
   braiding identity from doctrinal adjunction, and cancellation of the tensor counit
   prove compatibility with braiding. Naturality extends it to all derived objects.
   Conjugating by the exact/left-derived identification gives the actual comparison
   used here, with naturality in both inputs.
2. Put L = i_e^* M, D = L tensor B, E = B tensor L. Naturality of symmetry gives
   r C_Z(sigma_e) = sigma_p s. Set H = eta_E F_p(r inverse). Apply F_p and
   naturality of eta to obtain H F_p(sigma_p) F_p(s) = C_T(F_e(sigma_e)) eta_D.
3. Write V = F_p(v), d = eta_B V inverse and k = c_(T;F_e B,M). Compose the assumed
   projection square with k C_T(pi_e inverse) on the left and
   (V inverse tensor 1) pi_p inverse on the right. Cancel inverses to get
   k C_T(pi_e inverse) H = (d tensor 1) pi_p inverse.
4. Let g_e = (1 tensor a_e) sigma_e and g_p = (1 tensor a_p) sigma_p. The final-arrow
   hypothesis says a_p = C_T(a_e) d. Tensor-comparison naturality and signed-symmetry
   naturality give c_(T;M,Y) C_T(g_e) = g_p (d inverse tensor 1) k.
5. Expand t_e and t_p. Substitute the input identity from step 2, the output identity
   from step 4, and the inverse-projection identity from step 3. Cancel
   (d inverse tensor 1)(d tensor 1) to obtain the displayed equality. Only the two
   stipulated projection components are inverted; no projection-formula theorem is used.
-/
theorem boundary_q_defining_composite_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsProper i] [CompactSpace T] :
    BoundaryDefiningCompositeComparison (ModuleCat.{u + 1} A) i := by
  exact boundary_composite_native (ModuleCat.{u + 1} A) i

end AlgebraicGeometry.ProEtale.BoundaryComparisonOfCoefficients
