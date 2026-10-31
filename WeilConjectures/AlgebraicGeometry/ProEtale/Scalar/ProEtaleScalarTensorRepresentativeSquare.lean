/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarChainCounitSquare
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorCoefficientResolutionSquare
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # The coefficient-resolution tensor square on a fixed flat K-flat complex

Source: Stacks Project, Tags 03EL, 06YY and 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] SheafOfModules.monoidalCategory

attribute [local irreducible] scalarTensorChainIso scalarExtensionFunctorCounit
  scalarMateDerivedTensorIso proEtaleCanonicalTensorComparison
  scalarMateDerivedCoefficientPullback

attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] proEtaleTensorPullbackTotalIso
  proEtaleRingDerivedPullbackFactors CategoryTheory.Functor.mapDerivedCategory
  HomologicalComplex₂.total CategoryTheory.Functor.leftAdjoint

private def scalarRepresentativeCounit
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules W (proEtaleConstantRing W A)) ℤ) :=
  (scalarMateRestriction φ W).mapDerivedCategory.map
      (scalarExtensionFunctorCounit φ W P) ≫
    (scalarMateRestriction φ W).mapDerivedCategoryFactors.hom.app
      ((reductionChangeComplex W (proEtaleConstantRingMap (T := W) φ)).obj P)

private theorem representativeComplexCounit_eq
    {D E : Type*} [Category D] [Abelian D] [Category E] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : D ⥤ E) [F.Additive] (L : DerivedCategory D ⥤ DerivedCategory E)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : CochainComplex D ℤ) :
    reductionComplexCounit F L ε K =
      ε.app ((HomotopyCategory.quotient D (.up ℤ)).obj K) := by
  have hid : (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K = 𝟙 _ := rfl
  have hi : (DerivedCategory.quotientCompQhIso D).inv.app K = 𝟙 _ := rfl
  have hh : (DerivedCategory.quotientCompQhIso E).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
  simp only [reductionComplexCounit, hi, hh, hid]
  erw [L.map_id, (DerivedCategory.Qh (C := E)).map_id]
  simp only [Category.id_comp]
  erw [Category.comp_id, Category.comp_id]

private theorem scalarRepresentativeCounit_eq
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules W (proEtaleConstantRing W A)) ℤ) :
    scalarRepresentativeCounit φ W P =
      (scalarMateRestriction φ W).mapDerivedCategory.map
        ((proEtaleRingDerivedExtensionCounit (proEtaleConstantRingMap (T := W) φ)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (scalarMateRestriction φ W).mapDerivedCategoryFactorsh.hom.app
        (((proEtaleRingExtension (proEtaleConstantRingMap (T := W) φ)).mapHomotopyCategory
          (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  have he : scalarExtensionFunctorCounit φ W P =
      (proEtaleRingDerivedExtensionCounit (proEtaleConstantRingMap (T := W) φ)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
    unfold scalarExtensionFunctorCounit
    exact representativeComplexCounit_eq _ _ _ P
  unfold scalarRepresentativeCounit
  rw [he]
  congr 1
  let E := (reductionChangeComplex W (proEtaleConstantRingMap (T := W) φ)).obj P
  change (scalarMateRestriction φ W).mapDerivedCategoryFactors.hom.app E =
    (scalarMateRestriction φ W).mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj E)
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  have hi : (DerivedCategory.quotientCompQhIso
      (proEtaleRingModules W (proEtaleConstantRing W B))).hom.app E = 𝟙 _ := rfl
  have hh : (DerivedCategory.quotientCompQhIso
      (proEtaleRingModules W (proEtaleConstantRing W A))).inv.app
        (((scalarMateRestriction φ W).mapHomologicalComplex (.up ℤ)).obj E) = 𝟙 _ := rfl
  have hf : ((scalarMateRestriction φ W).mapHomotopyCategoryFactors (.up ℤ)).inv.app E =
      𝟙 _ := rfl
  simp only [hi, hh, hf]
  erw [(scalarMateRestriction φ W).mapDerivedCategory.map_id,
    (DerivedCategory.Qh (C := proEtaleRingModules W (proEtaleConstantRing W A))).map_id]
  simp only [Category.id_comp]
  erw [Category.comp_id]

private def scalarRepresentativeCoordinates
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u})
    (a : ProEtaleTensorModel W (proEtaleConstantRing W A))
    (P : CochainComplex (proEtaleRingModules W (proEtaleConstantRing W A)) ℤ) :
    a.tensor.obj (DerivedCategory.Q.obj P,
      DerivedCategory.Q.obj (scalarMateCoefficientComplex φ W)) ⟶
      DerivedCategory.Q.obj
        ((proEtaleResolutionTotal W (proEtaleConstantRing W A)).obj
          (P, scalarMateCoefficientComplex φ W)) :=
  (scalarMateDerivedTensorIso φ W a).inv.app (DerivedCategory.Q.obj P) ≫
    scalarRepresentativeCounit φ W P ≫
    DerivedCategory.Q.map (scalarMateOrdinaryComplexIso φ W P).hom

private theorem uncurry_map_id_left {C D E : Type*}
    [Category C] [Category D] [Category E] (F : C ⥤ D ⥤ E)
    (X : C) {Y Y' : D} (v : Y ⟶ Y') :
    (Functor.uncurry.obj F).map (Prod.mkHom (𝟙 X) v) = (F.obj X).map v := by
  change (F.map (𝟙 X)).app Y ≫ (F.obj X).map v = _
  rw [F.map_id, NatTrans.id_app, Category.id_comp]

private theorem scalarRepresentativeCoordinates_normalization
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u})
    (a : ProEtaleTensorModel W (proEtaleConstantRing W A))
    (P H : CochainComplex (proEtaleRingModules W (proEtaleConstantRing W A)) ℤ)
    (hp : proEtaleFlatRepresentatives W (proEtaleConstantRing W A) P)
    (hh : proEtaleFlatRepresentatives W (proEtaleConstantRing W A) H)
    (q : H ⟶ scalarMateCoefficientComplex φ W) (hq : QuasiIso q) :
    a.representative.hom.app (⟨P, hp⟩, ⟨H, hh⟩) ≫
      a.tensor.map (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map q)) ≫
      scalarRepresentativeCoordinates φ W a P =
    DerivedCategory.Q.map
      ((proEtaleResolutionTotal W (proEtaleConstantRing W A)).map
        (Prod.mkHom (𝟙 P) q)) := by
  have hn : IsScalarMateDerivedTensor φ W a (scalarMateDerivedTensorIso φ W a) := by
    unfold scalarMateDerivedTensorIso
    exact Classical.choose_spec (scalarMateDerivedTensorIso_existsUnique φ W a).exists
  have h := hn P H hp hh q hq
  have h' := congrArg
    (fun g ↦ g ≫ DerivedCategory.Q.map (scalarMateOrdinaryComplexIso φ W P).hom) h
  simpa only [scalarRepresentativeCoordinates, scalarRepresentativeCounit_eq, Category.assoc,
    Functor.map_comp, Iso.map_inv_hom_id, Category.comp_id, proEtaleResolutionTotal,
    uncurry_map_id_left, Functor.map₂HomologicalComplex_obj_map,
    Functor.comp_obj, Functor.prod_obj, ObjectProperty.ι_obj] using h'

set_option maxHeartbeats 1600000 in
-- Comparing total-tensor and localization models exceeds the default heartbeat budget.
/-- Resolve only the degree-zero coefficient to compare tensor pullback with the
ordinary chain comparison on a fixed flat-term K-flat first factor. No geometric
scalar mate or derived restriction/pullback comparison occurs in this statement.

Source: Stacks 06YS and 07A4; Step 3 of the parent normalization argument
(blueprint: lem-sp-scalar-tensor-representative-square).

Proof: choose a flat-term K-flat resolution H of B_Y[0]. Apply the existing
coefficient-resolution square to (P,H). The normalized scalar-to-tensor maps
identify its alpha maps with the scalar counits and ordinary complex tensor
identifications. The ordinary balancing-chain total formula identifies its bottom
map, after the coefficient identification c_B, with scalarTensorChainIso.
On X use F(H) with augmentation F(q) followed by the degree-zero coefficient
identification F(B_Y[0]) -> B_X[0]. Its quasi-isomorphism follows from exactness
and the coefficient isomorphism. Tensoring these augmentations with P and FP
gives quasi-isomorphisms by
K-flatness. Pullback is exact and preserves flat K-flat representatives. Cancel
the localized quasi-isomorphisms in the coefficient-resolution square. Naturality
of the tensor identification with respect to the exact pullback factor on P gives
the stated right-hand scalar-counit coordinates. No flatness of B over A is used.
-/
theorem scalarTensorRepresentativeSquare
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aY : ProEtaleTensorModel Y (proEtaleConstantRing Y A))
    (aX : ProEtaleTensorModel X (proEtaleConstantRing X A))
    (t : scalarMateOrdinaryTensor φ Y ⋙ proEtaleConstantRingPullback A f ≅
      proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ X)
    (ht : IsScalarBalancing φ f t)
    (P : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ)
    (hp : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing Y A) P)
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology Y) (R := proEtaleConstantRing Y A) (P.X i)) :
    (proEtaleConstantRingDerivedPullback A f).map
      ((scalarMateDerivedTensorIso φ Y aY).inv.app (DerivedCategory.Q.obj P) ≫
        (scalarMateRestriction φ Y).mapDerivedCategory.map
          (scalarExtensionFunctorCounit φ Y P) ≫
        (scalarMateRestriction φ Y).mapDerivedCategoryFactors.hom.app
          ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≫
      (proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app
        (((scalarMateRestriction φ Y).mapHomologicalComplex (.up ℤ)).obj
          ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≫
      DerivedCategory.Q.map (scalarTensorChainIso φ f t P).hom =
    (proEtaleCanonicalTensorComparison f
      (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
      (proEtaleConstantRingComparison f A) aY aX).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (scalarMateCoefficientComplex φ Y)) ≫
      aX.tensor.map (Prod.mkHom
        (𝟙 ((proEtaleConstantRingDerivedPullback A f).obj (DerivedCategory.Q.obj P)))
        (scalarMateDerivedCoefficientPullback φ f).hom) ≫
      (scalarMateDerivedTensorIso φ X aX).inv.app
        ((proEtaleConstantRingDerivedPullback A f).obj (DerivedCategory.Q.obj P)) ≫
      (scalarMateRestriction φ X).mapDerivedCategory.map
        ((directImageScalarExtension φ X).map
          ((proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app P) ≫
          scalarExtensionFunctorCounit φ X
            (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)) ≫
      (scalarMateRestriction φ X).mapDerivedCategoryFactors.hom.app
        ((reductionChangeComplex X (proEtaleConstantRingMap (T := X) φ)).obj
          (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)) := by
  classical
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let R := proEtaleConstantRing Y A
  let S := proEtaleConstantRing X A
  let F₀ := proEtaleConstantRingPullback A f
  let F := F₀.mapHomologicalComplex (.up ℤ)
  let U := proEtaleConstantRingDerivedPullback A f
  let d := F₀.mapDerivedCategoryFactors
  let TY := proEtaleResolutionTotal Y R
  let TX := proEtaleResolutionTotal X S
  let C := scalarMateCoefficientComplex φ Y
  let k := (HomologicalComplex.singleMapHomologicalComplex F₀ (.up ℤ) 0).app
      (scalarMateCoefficient φ Y) ≪≫
    (CochainComplex.singleFunctor (proEtaleRingModules X S) (0 : ℤ)).mapIso
      (scalarMateCoefficientPullback φ f)
  let eY := scalarMateOrdinaryComplexIso φ Y P
  let eX := scalarMateOrdinaryComplexIso φ X (F.obj P)
  let hY := scalarMateDerivedTensorIso φ Y aY
  let hX := scalarMateDerivedTensorIso φ X aX
  let μ := proEtaleCanonicalTensorComparison f R S
    (proEtaleConstantRingComparison f A) aY aX
  let cY := scalarRepresentativeCoordinates φ Y aY P
  let cX := scalarRepresentativeCoordinates φ X aX (F.obj P)
  let v := scalarMateDerivedCoefficientPullback φ f
  let ordinary := (proEtaleTensorPullbackTotalIso f R S
      (proEtaleConstantRingComparison f A) P C).inv ≫
    TX.map (Prod.mkHom (𝟙 (F.obj P)) k.hom)
  obtain ⟨H, q, hH, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (J := ProEt.topology Y) (R := R) C
  have hP : proEtaleFlatRepresentatives Y R P := ⟨hp, hf⟩
  have hH' : proEtaleFlatRepresentatives Y R H := by
    refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat H).1 hH, ?_⟩
    intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (H.X n)).symm (hflat n)
  have : QuasiIso q := hq
  obtain ⟨hchain, _, _, _, _, hpF, hqF, _, _, _, hsquare, _⟩ :=
    proEtale_tensor_coefficient_resolution_square f R S
      (proEtaleConstantRingComparison f A) aY aX P H (scalarMateCoefficient φ Y) hP hH' q
  let q' : F.obj H ⟶ scalarMateCoefficientComplex φ X := F.map q ≫ k.hom
  have : QuasiIso q' := by dsimp only [q']; infer_instance
  have hYnorm := scalarRepresentativeCoordinates_normalization φ Y aY P H hP hH' q hq
  have hXnorm := scalarRepresentativeCoordinates_normalization φ X aX
    (F.obj P) (F.obj H) hpF hqF q' inferInstance
  let repY := aY.representative.hom.app (⟨P, hP⟩, ⟨H, hH'⟩)
  let repX := aX.representative.hom.app (⟨F.obj P, hpF⟩, ⟨F.obj H, hqF⟩)
  let r := aY.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q))
  have : IsIso (DerivedCategory.Q.map q) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) q hq
  have : IsIso (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q)) :=
    (CategoryTheory.isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso r := by dsimp only [r]; infer_instance
  have : IsIso repY := by dsimp only [repY]; infer_instance
  have hnorm : repY ≫ r ≫ cY =
      DerivedCategory.Q.map (TY.map (Prod.mkHom (𝟙 P) q)) := by
    exact hYnorm
  have hq' : U.map (DerivedCategory.Q.map q) ≫ v.hom =
      d.hom.app H ≫ DerivedCategory.Q.map q' := by
    have hd := d.hom.naturality q
    change U.map (DerivedCategory.Q.map q) ≫ d.hom.app C =
      d.hom.app H ≫ DerivedCategory.Q.map (F.map q) at hd
    have hk : v.hom = d.hom.app C ≫ DerivedCategory.Q.map k.hom := by
      simp only [v, scalarMateDerivedCoefficientPullback, k, Iso.trans_hom,
        Functor.mapIso_hom, Functor.map_comp, proEtaleRingDerivedPullbackFactors]
      rfl
    rw [hk, ← Category.assoc, hd]
    simp only [q', Functor.map_comp, Category.assoc]
  have hprod : aX.tensor.map (Prod.mkHom (𝟙 (U.obj (DerivedCategory.Q.obj P)))
        (U.map (DerivedCategory.Q.map q))) ≫
      aX.tensor.map (Prod.mkHom (d.hom.app P) v.hom) =
    aX.tensor.map (Prod.mkHom (d.hom.app P) (d.hom.app H)) ≫
      aX.tensor.map (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map q')) := by
    rw [← aX.tensor.map_comp, ← aX.tensor.map_comp]
    congr 1
    apply Prod.ext
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact hq'
  have hμ := μ.hom.naturality
    (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q))
  dsimp only [Functor.comp_map, Functor.prod_map] at hμ
  erw [U.map_id] at hμ
  change U.map r ≫ μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj C) =
    μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj H) ≫
      aX.tensor.map (Prod.mkHom (𝟙 _) (U.map (DerivedCategory.Q.map q))) at hμ
  have hdf : proEtaleRingDerivedPullbackFactors f R S
      (proEtaleConstantRingComparison f A) = d := by
    unfold proEtaleRingDerivedPullbackFactors
    rfl
  rw [hdf] at hsquare
  dsimp only [proEtaleResolutionSigma, Iso.symm_hom] at hsquare
  change U.map repY ≫ μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj H) ≫
      aX.tensor.map (Prod.mkHom (d.hom.app P) (d.hom.app H)) =
    d.hom.app (TY.obj (P, H)) ≫
      DerivedCategory.Q.map (proEtaleTensorPullbackTotalIso f R S
        (proEtaleConstantRingComparison f A) P H).inv ≫ repX at hsquare
  have hXnorm' : repX ≫ aX.tensor.map
      (Prod.mkHom (𝟙 (DerivedCategory.Q.obj (F.obj P))) (DerivedCategory.Q.map q')) ≫ cX =
      DerivedCategory.Q.map (TX.map (Prod.mkHom (𝟙 (F.obj P)) q')) := by
    exact hXnorm
  have htotal : F.map (TY.map (Prod.mkHom (𝟙 P) q)) ≫ ordinary =
      (proEtaleTensorPullbackTotalIso f R S (proEtaleConstantRingComparison f A) P H).inv ≫
        TX.map (Prod.mkHom (𝟙 (F.obj P)) q') := by
    change (proEtaleTensorPullbackTotalIso f R S
        (proEtaleConstantRingComparison f A) P H).inv ≫
        TX.map (Prod.mkHom (𝟙 (F.obj P)) (F.map q)) =
      F.map (TY.map (Prod.mkHom (𝟙 P) q)) ≫
        (proEtaleTensorPullbackTotalIso f R S
          (proEtaleConstantRingComparison f A) P C).inv at hchain
    dsimp only [ordinary]
    rw [← Category.assoc, ← hchain, Category.assoc, ← TX.map_comp]
    congr 2
  have hd := d.hom.naturality (TY.map (Prod.mkHom (𝟙 P) q))
  change U.map (DerivedCategory.Q.map (TY.map (Prod.mkHom (𝟙 P) q))) ≫
      d.hom.app (TY.obj (P, C)) =
    d.hom.app (TY.obj (P, H)) ≫
      DerivedCategory.Q.map (F.map (TY.map (Prod.mkHom (𝟙 P) q))) at hd
  have hone : U.map cY ≫ d.hom.app (TY.obj (P, C)) ≫ DerivedCategory.Q.map ordinary =
      μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj C) ≫
        aX.tensor.map (Prod.mkHom (d.hom.app P) v.hom) ≫ cX := by
    apply (cancel_epi (U.map (repY ≫ r))).1
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hμ, reassoc_of% hprod, reassoc_of% hsquare]
    erw [hXnorm']
    rw [← U.map_comp_assoc, ← U.map_comp_assoc, Category.assoc repY r cY,
      hnorm, reassoc_of% hd]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun w ↦ d.hom.app (TY.obj (P, H)) ≫ DerivedCategory.Q.map w) htotal
  obtain ⟨_, _, t₀, _, hu, _, T, hT, _, hbal⟩ := proEtaleScalarBalancingChain φ f
  have htt := hu t ht
  rw [← htt] at hT
  let sY := CochainComplex.mapBifunctorSingle₂Iso
    (proEtaleOrdinaryTensor Y R) (scalarMateCoefficient φ Y) P
  let sX := CochainComplex.mapBifunctorSingle₂Iso
    (proEtaleOrdinaryTensor X S) (scalarMateCoefficient φ X) (F.obj P)
  let bY := (Functor.mapHomologicalComplexCompIso (scalarMateOrdinaryTensorIso φ Y)
    (.up ℤ)).app P
  let bX := (Functor.mapHomologicalComplexCompIso (scalarMateOrdinaryTensorIso φ X)
    (.up ℤ)).app (F.obj P)
  have hT' : T.hom.app P = (NatIso.mapHomologicalComplex t (.up ℤ)).hom.app P := by
    apply HomologicalComplex.hom_ext
    intro i
    exact (hT P i).1
  have hbal' : F.map sY.hom ≫ T.hom.app P = ordinary ≫ sX.hom := by
    simpa only [ordinary, TX, proEtaleResolutionTotal, uncurry_map_id_left,
      Functor.map₂HomologicalComplex_obj_map, Iso.trans_hom, Functor.mapIso_hom,
      sY, sX, F, F₀, R, S, C, k, Category.assoc] using hbal P
  have hchain' : (scalarTensorChainIso φ f t P).hom =
      F.map bY.hom ≫ T.hom.app P ≫ bX.inv := by
    rw [hT']
    unfold scalarTensorChainIso
    rfl
  have hordinary : F.map eY.hom ≫ ordinary =
      (scalarTensorChainIso φ f t P).hom ≫ eX.hom := by
    rw [hchain']
    change F.map (bY.hom ≫ sY.inv) ≫ ordinary =
      (F.map bY.hom ≫ T.hom.app P ≫ bX.inv) ≫ (bX.hom ≫ sX.inv)
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
    apply (cancel_epi (F.map bY.hom)).2
    apply (cancel_mono sX.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hbal', ← Category.assoc, ← F.map_comp, sY.inv_hom_id, F.map_id,
      Category.id_comp]
  have hn := hX.inv.naturality (d.hom.app P)
  change aX.tensor.map (Prod.mkHom (d.hom.app P) (𝟙 _)) ≫
      hX.inv.app (DerivedCategory.Q.obj (F.obj P)) =
    hX.inv.app (U.obj (DerivedCategory.Q.obj P)) ≫
      (scalarMateRestriction φ X).mapDerivedCategory.map
        ((directImageScalarExtension φ X).map (d.hom.app P)) at hn
  have hprod' : aX.tensor.map (Prod.mkHom (𝟙 (U.obj (DerivedCategory.Q.obj P))) v.hom) ≫
      aX.tensor.map (Prod.mkHom (d.hom.app P) (𝟙 _)) =
      aX.tensor.map (Prod.mkHom (d.hom.app P) v.hom) := by
    rw [← aX.tensor.map_comp]
    congr 1
    exact Prod.ext (Category.id_comp _) (Category.comp_id _)
  have he := d.hom.naturality eY.hom
  change U.map (DerivedCategory.Q.map eY.hom) ≫ d.hom.app (TY.obj (P, C)) =
      d.hom.app
        (((scalarMateRestriction φ Y).mapHomologicalComplex (.up ℤ)).obj
          ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≫
        DerivedCategory.Q.map (F.map eY.hom) at he
  apply (cancel_mono (DerivedCategory.Q.map eX.hom)).1
  simp only [Category.assoc]
  change U.map (hY.inv.app (DerivedCategory.Q.obj P) ≫ scalarRepresentativeCounit φ Y P) ≫
      d.hom.app _ ≫ DerivedCategory.Q.map (scalarTensorChainIso φ f t P).hom ≫
        DerivedCategory.Q.map eX.hom =
    μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj C) ≫
      aX.tensor.map (Prod.mkHom (𝟙 (U.obj (DerivedCategory.Q.obj P))) v.hom) ≫
      hX.inv.app (U.obj (DerivedCategory.Q.obj P)) ≫
      (scalarMateRestriction φ X).mapDerivedCategory.map
        ((directImageScalarExtension φ X).map (d.hom.app P) ≫
          scalarExtensionFunctorCounit φ X (F.obj P)) ≫
      (scalarMateRestriction φ X).mapDerivedCategoryFactors.hom.app
        ((reductionChangeComplex X (proEtaleConstantRingMap (T := X) φ)).obj (F.obj P)) ≫
      DerivedCategory.Q.map eX.hom
  rw [← DerivedCategory.Q.map_comp, ← hordinary, DerivedCategory.Q.map_comp,
    ← reassoc_of% he]
  simp only [Functor.map_comp, Category.assoc]
  rw [← U.map_comp_assoc, ← U.map_comp_assoc,
    Category.assoc (hY.inv.app (DerivedCategory.Q.obj P))
      (scalarRepresentativeCounit φ Y P) (DerivedCategory.Q.map eY.hom)]
  change U.map cY ≫ d.hom.app (TY.obj (P, C)) ≫ DerivedCategory.Q.map ordinary = _
  rw [hone]
  rw [← reassoc_of% hn, ← reassoc_of% hprod']
  simp only [cX, scalarRepresentativeCoordinates, scalarRepresentativeCounit, Category.assoc,
    hX, eX, scalarMateCoefficientComplex]

end AlgebraicGeometry.ProEtale
