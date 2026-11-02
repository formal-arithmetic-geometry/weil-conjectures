/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarStages
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarCompletedObjectComplete
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarCoefficientFiniteFree
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarRestrictionComplete
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageCoherence
import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapBiproduct

/-! # Ambient operation comparisons for finite scalar extension

Source: blueprint proper base change, order 1307; Milne, Section 19.
Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.
(blueprint: lem-pbc-scalar-ambient-operation-comparisons)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme
section AmbientOperations

variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarCompletedCoefficientMap_projection {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    completedCoefficientMap g d ≫ pbcAdicProjection X d n =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (pbcAdicProjection Y d n) ≫
        completedFiniteCoefficientMap g d n := by
  exact limit.lift_π _ (op n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarFiniteCoefficientMap_naturality {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dA : AdicCoefficientDatum A) (dB : AdicCoefficientDatum B) (n : ℕ)
    (q : (A ⧸ dA.ideal ^ (n + 1)) →+* (B ⧸ dB.ideal ^ (n + 1))) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (AdicCoefficients.coefficientMap Y q) ≫ completedFiniteCoefficientMap g dB n =
      completedFiniteCoefficientMap g dA n ≫ AdicCoefficients.coefficientMap X q := by
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  have hinv : AdicCoefficients.coefficientMap Y q ≫
      (pbcLevelConstantComparison Y dB n).inv =
    (pbcLevelConstantComparison Y dA n).inv ≫
      (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map (CommRingCat.ofHom q) := by
    apply (Iso.eq_inv_comp _).2
    rw [← Category.assoc]
    apply (Iso.comp_inv_eq _).2
    exact (scalarLevelConstantComparison_naturality Y dA dB n q).symm
  unfold completedFiniteCoefficientMap
  change L.map _ ≫ L.map _ ≫ _ ≫ _ = _
  rw [← L.map_comp_assoc, hinv, L.map_comp, Category.assoc]
  erw [reassoc_of% (proEtaleConstantInverseImageMap_naturality g (CommRingCat.ofHom q))]
  simp only [Category.assoc]
  rw [scalarLevelConstantComparison_naturality]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual completed coefficient inclusion commutes with the ringed structure map.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: apply every finite target projection. Both paths take a continuous residue
function, postcompose with the specified field inclusion and precompose with the
base-change map on connected components. Those operations commute. Joint monicity
of all coefficient limit projections gives the displayed completed equality. -/
theorem pbcScalarCoefficientStructureSquare :
    pbcActualCoefficientRingMap Y (pbcScalarCoefficientMap l E F i Y) ≫
        pbcActualStructureMap g (pbcIntegralDatum l F) =
      pbcActualStructureMap g (pbcIntegralDatum l E) ≫
        (proEtaleSheafDirectImage g RingCat.{u + 1}).map
          (pbcActualCoefficientRingMap X (pbcScalarCoefficientMap l E F i X)) := by
  let dE := pbcIntegralDatum l E
  let dF := pbcIntegralDatum l F
  let c (T : Scheme.{u}) := pbcScalarCoefficientMap l E F i T
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  let R := proEtaleSheafDirectImage g CommRingCat.{u + 1}
  have hc (T : Scheme.{u}) (n : ℕ) :
      c T ≫ pbcAdicProjection T dF n = pbcAdicProjection T dE n ≫
        AdicCoefficients.coefficientMap T (pbcScalarQuotientMap l E F i n) :=
    (pbcScalarCoefficientMap_exists l E F i T).exists.choose_spec n
  have h : L.map (c Y) ≫ completedCoefficientMap g dF =
      completedCoefficientMap g dE ≫ c X := by
    apply limit.hom_ext
    intro n
    change (L.map (c Y) ≫ completedCoefficientMap g dF) ≫
        pbcAdicProjection X dF n.unop =
      (completedCoefficientMap g dE ≫ c X) ≫ pbcAdicProjection X dF n.unop
    simp only [Category.assoc, hc]
    rw [scalarCompletedCoefficientMap_projection]
    rw [← Category.assoc (completedCoefficientMap g dE), scalarCompletedCoefficientMap_projection]
    rw [← L.map_comp_assoc, hc, L.map_comp, Category.assoc]
    simpa only [Category.assoc] using congrArg
      (fun k ↦ L.map (pbcAdicProjection Y dE n.unop) ≫ k)
      (scalarFiniteCoefficientMap_naturality g dE dF n.unop
        (pbcScalarQuotientMap l E F i n.unop))
  have hd : c Y ≫ completedCoefficientDirectImageMap g dF =
      completedCoefficientDirectImageMap g dE ≫ R.map (c X) := by
    unfold completedCoefficientDirectImageMap
    have hn := (proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.naturality (c Y)
    change c Y ≫ (proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app _ =
      (proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app _ ≫ R.map (L.map (c Y)) at hn
    rw [← Category.assoc]
    erw [hn]
    rw [Category.assoc, ← R.map_comp, h, R.map_comp, Category.assoc]
  exact congrArg
    (fun k ↦ (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map k) hd

/-- The ambient ordinary-pullback comparison is the normalized derived tensor comparison.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
@[irreducible] def pbcScalarOrdinaryPullIso :
    pbcEmbeddingAmbientTensor l E F i Y ⋙
        pbcActualDerivedPull g (pbcIntegralDatum l F) ≅
      pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i X :=
  pbcActualScalarDerivedPullIso g (pbcIntegralDatum l E) (pbcIntegralDatum l F)
    (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
    (pbcScalarCoefficientStructureSquare l E F i g)

/-- The direct-image comparison is the actual mate, rather than a selected isomorphism.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
@[irreducible] def pbcScalarDirectImageMap :
    pbcActualDerivedPush g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i Y ⟶
      pbcEmbeddingAmbientTensor l E F i X ⋙
        pbcActualDerivedPush g (pbcIntegralDatum l F) :=
  pbcActualScalarDirectImageMap g (pbcIntegralDatum l E) (pbcIntegralDatum l F)
    (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
    (pbcScalarCoefficientStructureSquare l E F i g)

/-- The actual completed coefficient comparison is the canonical profinite comparison.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: both maps have the same finite projections. -/
theorem pbcCompletedCoefficientMap_eq {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    completedCoefficientMap g d = (d.integralRingIso g).hom := by
  apply limit.hom_ext
  intro n
  change completedCoefficientMap g d ≫ d.projection X n.unop =
    (d.integralRingIso g).hom ≫ d.projection X n.unop
  calc
    _ = completedCoefficientComponent g d n.unop := limit.lift_π _ n
    _ = _ := by
      rw [d.projection_comm]
      rfl

/-- The completed coefficient comparison as an isomorphism, with the actual forward map.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
def pbcCompletedCoefficientIso {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (pbcAdicCompletion Y d) ≅
      pbcAdicCompletion X d where
  hom := completedCoefficientMap g d
  inv := (d.integralRingIso g).inv
  hom_inv_id := by
    rw [pbcCompletedCoefficientMap_eq]
    exact (d.integralRingIso g).hom_inv_id
  inv_hom_id := by
    rw [pbcCompletedCoefficientMap_eq]
    exact (d.integralRingIso g).inv_hom_id

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar inclusion commutes with the inverse-image coefficient comparisons.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: apply every finite target projection, as in the structure-map square. -/
theorem pbcScalarCoefficientInverseSquare :
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l E)).hom ≫
        pbcScalarCoefficientMap l E F i X =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
          (pbcScalarCoefficientMap l E F i Y) ≫
        (pbcCompletedCoefficientIso g (pbcIntegralDatum l F)).hom := by
  let dE := pbcIntegralDatum l E
  let dF := pbcIntegralDatum l F
  let c (T : Scheme.{u}) := pbcScalarCoefficientMap l E F i T
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  have hc (T : Scheme.{u}) (n : ℕ) :
      c T ≫ pbcAdicProjection T dF n = pbcAdicProjection T dE n ≫
        AdicCoefficients.coefficientMap T (pbcScalarQuotientMap l E F i n) :=
    (pbcScalarCoefficientMap_exists l E F i T).exists.choose_spec n
  change completedCoefficientMap g dE ≫ c X = L.map (c Y) ≫ completedCoefficientMap g dF
  symm
  apply limit.hom_ext
  intro n
  change (L.map (c Y) ≫ completedCoefficientMap g dF) ≫
      pbcAdicProjection X dF n.unop =
    (completedCoefficientMap g dE ≫ c X) ≫ pbcAdicProjection X dF n.unop
  simp only [Category.assoc, hc]
  rw [scalarCompletedCoefficientMap_projection]
  rw [← Category.assoc (completedCoefficientMap g dE), scalarCompletedCoefficientMap_projection]
  rw [← L.map_comp_assoc, hc, L.map_comp, Category.assoc]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ L.map (pbcAdicProjection Y dE n.unop) ≫ k)
    (scalarFiniteCoefficientMap_naturality g dE dF n.unop
      (pbcScalarQuotientMap l E F i n.unop))

/-- The canonical derived restriction/direct-image comparison for the scalar inclusion.
Source: Stacks Tag 0D6E (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
abbrev pbcScalarRestrictionDirectImage :=
  proEtaleRingRestrictionDerivedDirectImage g
    (pbcAdicCompletion Y (pbcIntegralDatum l E)) (pbcAdicCompletion Y (pbcIntegralDatum l F))
    (pbcAdicCompletion X (pbcIntegralDatum l E)) (pbcAdicCompletion X (pbcIntegralDatum l F))
    (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))
    (pbcScalarCoefficientInverseSquare l E F i g)

/-- The canonical comparison from termwise pullback to the published derived pullback,
obtained by conjugating the identity of the common derived direct image.
Source: Stacks Tag 0D6D (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
def pbcPullComparison {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    proEtaleRingDerivedPullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (pbcCompletedCoefficientIso g d) ⟶ pbcActualDerivedPull g d :=
  (conjugateEquiv (pbcActualDerivedAdjunction g d)
    (proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
      (pbcCompletedCoefficientIso g d))).symm (𝟙 _)

/-- The canonical termwise restriction/pullback comparison for the scalar inclusion.
Source: Stacks Tag 0D6D (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
abbrev pbcScalarRestrictionPullback :=
  proEtaleRingRestrictionDerivedPullback g
    (pbcAdicCompletion Y (pbcIntegralDatum l E)) (pbcAdicCompletion Y (pbcIntegralDatum l F))
    (pbcAdicCompletion X (pbcIntegralDatum l E)) (pbcAdicCompletion X (pbcIntegralDatum l F))
    (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))
    (pbcScalarCoefficientInverseSquare l E F i g)

/-- Flat-term K-flat complexes over the completed coefficients, the resolving class on
which the derived scalar and pullback functors are computed termwise.
Source: Stacks Tag 06YY (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
def PbcFlatKFlat (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := pbcAdicCompletion T d) K ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pbcAdicCompletion T d) (K.X n)

/-- Every complex has a flat-term K-flat resolution.
Source: Stacks Tag 06YY (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
theorem pbcFlatKFlat_resolution (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (K : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    ∃ (L : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) (s : L ⟶ K),
      QuasiIso s ∧ PbcFlatKFlat T d L := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat.{u + 1} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
      u + 1, u + 2, u + 1} _
  obtain ⟨L, s, hl, hf, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (C := T.ProEt) (J := ProEt.topology T) (R := pbcAdicCompletion T d) K
  refine ⟨L, s, hs, hl, fun n ↦ ?_⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso (pbcAdicCompletion T d) (L.X n)).symm (hf n)

/-- Biproduct powers are exact: they are both `const ⋙ lim` and `const ⋙ colim`. -/
private theorem finBiproductPow_exact {C : Type*} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] (d : ℕ) :
    PreservesFiniteLimits (Functor.finBiproductPow C d) ∧
    PreservesFiniteColimits (Functor.finBiproductPow C d) := by
  let cL (X : C) : Cone ((Functor.const (Discrete (Fin d))).obj X) :=
    ⟨⨁ fun _ : Fin d => X,
      { app := fun j => biproduct.π (fun _ : Fin d => X) j.as
        naturality := by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp }⟩
  let iL (X : C) : (⨁ fun _ : Fin d => X) ≅ limit ((Functor.const (Discrete (Fin d))).obj X) :=
    { hom := limit.lift _ (cL X)
      inv := biproduct.lift fun j => limit.π ((Functor.const (Discrete (Fin d))).obj X) ⟨j⟩
      hom_inv_id := biproduct.hom_ext _ _ fun j => by simp [cL]
      inv_hom_id := limit.hom_ext fun ⟨j⟩ => by simp [cL] }
  let eL : Functor.finBiproductPow C d ≅ (Functor.const (Discrete (Fin d)) : C ⥤ _) ⋙ lim :=
    NatIso.ofComponents iL (by
        intro X Y f
        change (biproduct.map fun _ => f) ≫ limit.lift _ (cL Y) =
          limit.lift _ (cL X) ≫ limMap ((Functor.const (Discrete (Fin d))).map f)
        refine limit.hom_ext fun ⟨j⟩ => ?_
        simp [cL])
  let cC (X : C) : Cocone ((Functor.const (Discrete (Fin d))).obj X) :=
    ⟨⨁ fun _ : Fin d => X,
      { app := fun j => biproduct.ι (fun _ : Fin d => X) j.as
        naturality := by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp }⟩
  let iC (X : C) : (⨁ fun _ : Fin d => X) ≅ colimit ((Functor.const (Discrete (Fin d))).obj X) :=
    { hom := biproduct.desc fun j => colimit.ι ((Functor.const (Discrete (Fin d))).obj X) ⟨j⟩
      inv := colimit.desc _ (cC X)
      hom_inv_id := biproduct.hom_ext' _ _ fun j => by simp [cC]
      inv_hom_id := colimit.hom_ext fun ⟨j⟩ => by simp [cC] }
  let eC : Functor.finBiproductPow C d ≅ (Functor.const (Discrete (Fin d)) : C ⥤ _) ⋙ colim :=
    NatIso.ofComponents iC (by
        intro X Y f
        change (biproduct.map fun _ => f) ≫
            biproduct.desc (fun j => colimit.ι ((Functor.const (Discrete (Fin d))).obj Y) ⟨j⟩) =
          biproduct.desc (fun j => colimit.ι ((Functor.const (Discrete (Fin d))).obj X) ⟨j⟩) ≫
            colimMap ((Functor.const (Discrete (Fin d))).map f)
        refine biproduct.hom_ext' _ _ fun j => ?_
        simp)
  exact ⟨preservesFiniteLimits_of_natIso eL.symm, preservesFiniteColimits_of_natIso eC.symm⟩

open MonoidalCategory in
/-- The completed target integral coefficients are flat over the source ones.
Source: Stacks Tag 03ER (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: by `pbcScalarCoefficient_finiteFree` the restricted unit is a finite product of
copies of the unit. Tensor with the unit is the identity functor, and tensor with a finite
biproduct is the biproduct of the tensor functors, so tensor with it is exact. -/
theorem pbcScalarCoefficient_flat (T : Scheme.{u}) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pbcAdicCompletion T (pbcIntegralDatum l E))
      ((pbcRestrict (pbcScalarCoefficientMap l E F i T)).obj
        (SheafOfModules.unit ((adicLisseForget T).obj
          (pbcAdicCompletion T (pbcIntegralDatum l F))))) := by
  classical
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat.{u + 1} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
      u + 1, u + 2, u + 1} _
  obtain ⟨d, ⟨b⟩⟩ := pbcScalarCoefficient_finiteFree l E F i T
  let R := pbcAdicCompletion T (pbcIntegralDatum l E)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let 𝒜 := SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  have : MonoidalPreadditive 𝒜 := by
    have (M : 𝒜) : (tensorLeft M).Additive := SheafOfModules.tensorLeft_additive_independent R M
    have (M : 𝒜) : (tensorRight M).Additive :=
      Functor.additive_of_iso (F := tensorLeft M) (BraidedCategory.tensorLeftIsoTensorRight M)
    exact
      { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
        zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
        whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
        add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  let M : 𝒜 := (pbcRestrict (pbcScalarCoefficientMap l E F i T)).obj
    (SheafOfModules.unit ((adicLisseForget T).obj
      (pbcAdicCompletion T (pbcIntegralDatum l F))))
  have : HasFiniteBiproducts 𝒜 := HasFiniteBiproducts.of_hasFiniteProducts
  let e : M ≅ ⨁ fun _ : Fin d ↦ 𝟙_ 𝒜 := b ≪≫ (biproduct.isoProduct _).symm
  let e₂ : tensorRight M ≅ Functor.finBiproductPow 𝒜 d :=
    (BraidedCategory.tensorLeftIsoTensorRight M).symm ≪≫
      MonoidalCategory.tensorLeftIsoOfIso e ≪≫ MonoidalCategory.tensorLeftBiproductPowUnitIso d
  obtain ⟨h₁, h₂⟩ := finBiproductPow_exact (C := 𝒜) d
  exact (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R M ≪≫ e₂).symm
    ((exactFunctor_iff _).2 ⟨h₁, h₂⟩)

/-- Restriction along the completed scalar inclusion preserves flat-term K-flat complexes.
Source: Stacks Tags 06YY and 0943 (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: the target coefficients are finite free over the source coefficients
(`pbcScalarCoefficient_finiteFree`). A flat target module is therefore flat over the
source. For K-flatness, the source tensor of the restriction with a complex M is the
target tensor of the complex with the scalar extension of M, which is a finite sum of
copies of M and hence acyclic when M is. -/
theorem pbcScalarRestrict_flatKFlat (T : Scheme.{u})
    (K : CochainComplex (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l F))) ℤ)
    (hK : PbcFlatKFlat T (pbcIntegralDatum l F) K) :
    PbcFlatKFlat T (pbcIntegralDatum l E)
      (((pbcRestrict (pbcScalarCoefficientMap l E F i T)).mapHomologicalComplex
        (.up ℤ)).obj K) := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  have h := SheafOfModules.isKFlat_restrictScalars_of_flat (pbcScalarCoefficientMap l E F i T)
    (pbcScalarCoefficient_flat l E F i T) K hK.1
  exact ⟨h.1, h.2 hK.2⟩

/-- The termwise pullback is the published module pullback.
Source: Stacks Tag 03EK (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: both are inverse image followed by the specified sheafified tensor along the
same completed coefficient map; the scalar-extension witness fixes objects and maps. -/
theorem pbcModulePull_eq {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    proEtaleRingModulePullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (pbcCompletedCoefficientIso g d) = pbcActualModulePull g d := by
  symm
  change completedModulePullback g d = _
  unfold completedModulePullback
  refine CategoryTheory.Functor.ext (fun M ↦
    (completedAdicChangeData X (completedCoefficientMap g d)).choose_spec.choose
      ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).obj M)) ?_
  intro M N f
  exact (completedAdicChangeData X (completedCoefficientMap g d)).choose_spec.choose_spec.choose
    ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).map f)

/-- The ordinary identification of the two module pullbacks.
Source: Stacks Tag 03EK (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
def pbcModulePullIso {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    proEtaleRingModulePullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
        (pbcCompletedCoefficientIso g d) ≅ pbcActualModulePull g d :=
  eqToIso (pbcModulePull_eq g d)

/-- The published pullback counit is invertible on K-flat complexes.
Source: Stacks Tag 06YY (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
theorem pbcActualPullComplexCounit_isIso {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (hp : PbcFlatKFlat Y d P) : IsIso (pbcActualPullComplexCounit g d P) := by
  have : IsIso ((pbcActualPullCounit g d).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
    delta pbcActualPullCounit completedOrdinaryPullbackCounit completedOrdinaryPullback
    exact (completedOrdinaryPullback_exists g d).choose_spec.choose_spec.2 P hp.1
  dsimp only [pbcActualPullComplexCounit]
  infer_instance

/-- The canonical pullback comparison is the localized termwise identification on
flat-term K-flat complexes.
Source: Stacks Tags 06YY and 0D6D (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: both derived adjunctions have units computed on K-flat complexes by the same
ordinary unit after the identification; conjugating the identity of direct image
therefore gives the localized identification. -/
theorem pbcPullComparison_app {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (hp : PbcFlatKFlat Y d P) :
    (pbcPullComparison g d).app (DerivedCategory.Q.obj P) ≫
        pbcActualPullComplexCounit g d P =
      (proEtaleRingModulePullback g (pbcAdicCompletion Y d) (pbcAdicCompletion X d)
          (pbcCompletedCoefficientIso g d)).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (pbcModulePullIso g d).hom (.up ℤ)).app P) := by
  sorry

/-- The ordinary scalar mate of the inverse ordinary pullback comparison.
Source: Stacks Tag 03EL (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
def pbcScalarOrdinaryRestrictionPull :
    pbcRestrict (pbcScalarCoefficientMap l E F i Y) ⋙ pbcActualModulePull g (pbcIntegralDatum l E) ⟶
      pbcActualModulePull g (pbcIntegralDatum l F) ⋙
        pbcRestrict (pbcScalarCoefficientMap l E F i X) :=
  (mateEquiv (pbcScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
    (pbcScalarAdjunction (pbcScalarCoefficientMap l E F i X))
    (TwoSquare.mk _ _ _ _ (pbcActualScalarOrdinaryPullIso g (pbcIntegralDatum l E)
      (pbcIntegralDatum l F) (pbcScalarCoefficientMap l E F i Y)
      (pbcScalarCoefficientMap l E F i X)
      (pbcScalarCoefficientStructureSquare l E F i g)).inv)).natTrans

/-- The ordinary scalar mate is the identity-on-sections restriction/pullback comparison.
Source: Stacks Tags 03EK and 03EL (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: the ordinary pullback comparison is the conjugate of the identity-on-sections
restriction/direct-image comparison; by the ordinary iterated-mates identity its scalar
mate is the conjugate of that comparison under the module pullback adjunctions, which
is the restriction/pullback comparison sending a local tensor to the same tensor. -/
theorem pbcScalarOrdinaryRestrictionPull_eq :
    whiskerLeft (pbcRestrict (pbcScalarCoefficientMap l E F i Y))
        (pbcModulePullIso g (pbcIntegralDatum l E)).hom ≫
      pbcScalarOrdinaryRestrictionPull l E F i g =
    proEtaleRingRestrictionPullbackInv g
        (pbcAdicCompletion Y (pbcIntegralDatum l E)) (pbcAdicCompletion Y (pbcIntegralDatum l F))
        (pbcAdicCompletion X (pbcIntegralDatum l E)) (pbcAdicCompletion X (pbcIntegralDatum l F))
        (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
        (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))
        (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))
        (pbcScalarCoefficientInverseSquare l E F i g) ≫
      whiskerRight (pbcModulePullIso g (pbcIntegralDatum l F)).hom
        (pbcRestrict (pbcScalarCoefficientMap l E F i X)) := by
  sorry

/-- The derived scalar mate is the localized ordinary scalar mate on flat-term K-flat
complexes with flat-term K-flat restriction.
Source: Stacks Tags 03EK, 06YY and 07A6
(blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: write the mate with the derived scalar unit at the pulled-back restriction and
the derived scalar counit. Both arguments are K-flat, so the unit and counit are the
localized ordinary ones, the pullback counits are invertible, and the normalized
pullback comparison is the localized ordinary comparison. The localized ordinary mate
formula gives the displayed equation. -/
theorem pbcScalarPullMate_app
    (K : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l F))) ℤ)
    (hK : PbcFlatKFlat Y (pbcIntegralDatum l F) K)
    (hR : PbcFlatKFlat Y (pbcIntegralDatum l E)
      (((pbcRestrict (pbcScalarCoefficientMap l E F i Y)).mapHomologicalComplex (.up ℤ)).obj K)) :
    (pbcActualDerivedPull g (pbcIntegralDatum l E)).map
        ((pbcRestrict (pbcScalarCoefficientMap l E F i Y)).mapDerivedCategoryFactors.hom.app K) ≫
      pbcActualPullComplexCounit g (pbcIntegralDatum l E)
        (((pbcRestrict (pbcScalarCoefficientMap l E F i Y)).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (pbcScalarOrdinaryRestrictionPull l E F i g) (.up ℤ)).app K) =
    (mateEquiv (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
        (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
        (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E F i g).inv)).natTrans.app
          (DerivedCategory.Q.obj K) ≫
      (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i X)).map
        (pbcActualPullComplexCounit g (pbcIntegralDatum l F) K) ≫
      (pbcRestrict (pbcScalarCoefficientMap l E F i X)).mapDerivedCategoryFactors.hom.app
        (((pbcActualModulePull g (pbcIntegralDatum l F)).mapHomologicalComplex (.up ℤ)).obj K) := by
  sorry

-- The factorization chase for the termwise restriction/pullback comparison.
private theorem scalarRestrictionPullback_chase {C : Type*} [Category C]
    {O1 O2 O3 O4 O5 O6 O7 O8 : C}
    (ci : O1 ⟶ O2) (ch : O2 ⟶ O1) (bi : O2 ⟶ O3) (bh : O3 ⟶ O2) (ah : O3 ⟶ O4)
    (φF : O4 ⟶ O5) (fX : O5 ⟶ O6) (ma : O6 ⟶ O6) (Ffac : O3 ⟶ O6) (fy : O1 ⟶ O7)
    (φE : O7 ⟶ O8) (mc : O8 ⟶ O8) (Gfac : O2 ⟶ O8) (qe : O6 ⟶ O8) (qp : O8 ⟶ O6)
    (hci : ci ≫ ch = 𝟙 _) (hb : bi ≫ bh = 𝟙 _) (hA : ah ≫ φF ≫ fX ≫ ma = Ffac)
    (hma : ma = 𝟙 _) (hC : ch ≫ fy ≫ φE ≫ mc = Gfac) (hmc : mc = 𝟙 _)
    (hB : bh ≫ Gfac = Ffac ≫ qe) (hq : qe ≫ qp = 𝟙 _) :
    ((ci ≫ bi) ≫ ah) ≫ φF ≫ fX = fy ≫ φE ≫ qp := by
  subst hma hmc
  simp only [Category.comp_id] at hA hC
  calc ((ci ≫ bi) ≫ ah) ≫ φF ≫ fX = ci ≫ bi ≫ Ffac := by
        rw [← hA]; simp only [Category.assoc]
    _ = ci ≫ bi ≫ Ffac ≫ qe ≫ qp := by rw [hq, Category.comp_id]
    _ = ci ≫ bi ≫ bh ≫ Gfac ≫ qp := by rw [← Category.assoc Ffac, ← hB, Category.assoc]
    _ = ci ≫ Gfac ≫ qp := by rw [← Category.assoc bi, hb, Category.id_comp]
    _ = ci ≫ ch ≫ fy ≫ φE ≫ qp := by rw [← hC]; simp only [Category.assoc]
    _ = fy ≫ φE ≫ qp := by rw [← Category.assoc ci, hci, Category.id_comp]

/-- The termwise restriction/pullback comparison is the localized ordinary comparison.
Source: Stacks Tag 06YY (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: unfold it into the two composition isomorphisms and the derived image of the
ordinary comparison, and apply their factorization identities on complexes. -/
theorem pbcScalarRestrictionPullback_app
    (K : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l F))) ℤ) :
    (pbcScalarRestrictionPullback l E F i g).inv.app (DerivedCategory.Q.obj K) ≫
        (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i X)).map
          ((proEtaleRingModulePullback g (pbcAdicCompletion Y (pbcIntegralDatum l F))
            (pbcAdicCompletion X (pbcIntegralDatum l F))
            (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))).mapDerivedCategoryFactors.hom.app
              K) ≫
        (pbcRestrict (pbcScalarCoefficientMap l E F i X)).mapDerivedCategoryFactors.hom.app
          (((proEtaleRingModulePullback g (pbcAdicCompletion Y (pbcIntegralDatum l F))
            (pbcAdicCompletion X (pbcIntegralDatum l F))
            (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))).mapHomologicalComplex
              (.up ℤ)).obj K) =
      (proEtaleRingDerivedPullback g (pbcAdicCompletion Y (pbcIntegralDatum l E))
          (pbcAdicCompletion X (pbcIntegralDatum l E))
          (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))).map
          ((pbcRestrict (pbcScalarCoefficientMap l E F i Y)).mapDerivedCategoryFactors.hom.app K) ≫
        (proEtaleRingModulePullback g (pbcAdicCompletion Y (pbcIntegralDatum l E))
          (pbcAdicCompletion X (pbcIntegralDatum l E))
          (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))).mapDerivedCategoryFactors.hom.app
            (((pbcRestrict (pbcScalarCoefficientMap l E F i Y)).mapHomologicalComplex
              (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (proEtaleRingRestrictionPullbackInv g
            (pbcAdicCompletion Y (pbcIntegralDatum l E))
            (pbcAdicCompletion Y (pbcIntegralDatum l F))
            (pbcAdicCompletion X (pbcIntegralDatum l E))
            (pbcAdicCompletion X (pbcIntegralDatum l F))
            (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
            (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))
            (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))
            (pbcScalarCoefficientInverseSquare l E F i g)) (.up ℤ)).app K) := by
  let dE := pbcIntegralDatum l E
  let dF := pbcIntegralDatum l F
  let resY := pbcRestrict (pbcScalarCoefficientMap l E F i Y)
  let resX := pbcRestrict (pbcScalarCoefficientMap l E F i X)
  let PE := proEtaleRingModulePullback g (pbcAdicCompletion Y dE) (pbcAdicCompletion X dE)
    (pbcCompletedCoefficientIso g dE)
  let PF := proEtaleRingModulePullback g (pbcAdicCompletion Y dF) (pbcAdicCompletion X dF)
    (pbcCompletedCoefficientIso g dF)
  let pb := proEtaleRingRestrictionPullbackInv g
    (pbcAdicCompletion Y dE) (pbcAdicCompletion Y dF) (pbcAdicCompletion X dE)
    (pbcAdicCompletion X dF) (pbcScalarCoefficientMap l E F i Y)
    (pbcScalarCoefficientMap l E F i X) (pbcCompletedCoefficientIso g dE)
    (pbcCompletedCoefficientIso g dF) (pbcScalarCoefficientInverseSquare l E F i g)
  have := proEtaleRingRestrictionPullbackInv_isIso g
    (pbcAdicCompletion Y dE) (pbcAdicCompletion Y dF) (pbcAdicCompletion X dE)
    (pbcAdicCompletion X dF) (pbcScalarCoefficientMap l E F i Y)
    (pbcScalarCoefficientMap l E F i X) (pbcCompletedCoefficientIso g dE)
    (pbcCompletedCoefficientIso g dF) (pbcScalarCoefficientInverseSquare l E F i g)
  let a := Functor.mapDerivedCategoryCompIso PF resX
  let b := Functor.mapDerivedCategoryNatIso (asIso pb).symm
  let c := Functor.mapDerivedCategoryCompIso resY PE
  refine scalarRestrictionPullback_chase (c.inv.app _) (c.hom.app _) (b.inv.app _) (b.hom.app _)
    (a.hom.app _) _ _ _ _ _ _ _ _ _ _ (c.inv_hom_id_app _) (b.inv_hom_id_app _)
    (Functor.mapDerivedCategoryCompIso_fac PF resX K) ?_
    (Functor.mapDerivedCategoryCompIso_fac resY PE K) ?_
    (Functor.mapDerivedCategoryNatIso_fac (asIso pb).symm K) ?_
  all_goals first
    | (refine (DerivedCategory.Q.map_comp _ _).symm.trans ?_
       rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp]
       simp)
    | (rw [← CategoryTheory.Functor.map_id]
       congr 1
       ext n : 1
       simp [Functor.mapHomologicalComplexCompIso])
    | (rw [← CategoryTheory.Functor.map_id]
       congr 1)
  all_goals rfl

-- The final diagram chase, over an abstract category.
private theorem scalarPullMate_chase {C : Type*} [Category C]
    {O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 O12 : C}
    (a : O1 ⟶ O2) (t : O2 ⟶ O3) (r : O1 ⟶ O4) (b : O4 ⟶ O3)
    (fy1 : O1 ⟶ O6) (fy2 : O2 ⟶ O7) (eEP : O6 ⟶ O7) (cPE : O7 ⟶ O8)
    (ΦE : O6 ⟶ O9) (ιE : O9 ⟶ O8) (θ0 : O8 ⟶ O5) (pb : O9 ⟶ O10) (rι : O10 ⟶ O5)
    (ΦF : O4 ⟶ O11) (fXh2 : O11 ⟶ O10) (ιF : O11 ⟶ O12) (fXh1 : O12 ⟶ O5)
    (cPF : O3 ⟶ O12) (hZ : Mono (cPF ≫ fXh1))
    (hΘ : fy2 ≫ cPE ≫ θ0 = t ≫ cPF ≫ fXh1)
    (hn : fy1 ≫ eEP = a ≫ fy2)
    (hE : eEP ≫ cPE = ΦE ≫ ιE)
    (hF : b ≫ cPF = ΦF ≫ ιF)
    (hfX : ιF ≫ fXh1 = fXh2 ≫ rι)
    (hρ : r ≫ ΦF ≫ fXh2 = fy1 ≫ ΦE ≫ pb)
    (hord : ιE ≫ θ0 = pb ≫ rι) :
    a ≫ t = r ≫ b := by
  apply (cancel_mono (cPF ≫ fXh1)).1
  calc (a ≫ t) ≫ cPF ≫ fXh1 = a ≫ fy2 ≫ cPE ≫ θ0 := by rw [Category.assoc, hΘ]
    _ = fy1 ≫ eEP ≫ cPE ≫ θ0 := by rw [← Category.assoc a, ← hn, Category.assoc]
    _ = fy1 ≫ ΦE ≫ ιE ≫ θ0 := by rw [← Category.assoc eEP, hE, Category.assoc]
    _ = fy1 ≫ ΦE ≫ pb ≫ rι := by rw [hord]
    _ = r ≫ ΦF ≫ fXh2 ≫ rι := by
      simpa only [Category.assoc] using (congrArg (· ≫ rι) hρ).symm
    _ = r ≫ ΦF ≫ ιF ≫ fXh1 := by rw [hfX]
    _ = (r ≫ b) ≫ cPF ≫ fXh1 := by
      rw [Category.assoc, ← Category.assoc b, hF, Category.assoc]

/-- The restriction/pullback mate identity on a flat-term K-flat representative whose
restriction is again flat-term K-flat.
Source: Stacks Tags 03EK, 06YY, 0D6D and 07A6
(blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: on such a representative the scalar unit and counit, both pullback counits and
both pullback comparisons are localizations of the ordinary maps, and the normalized
pullback comparison is the localized balanced ordinary comparison. The ordinary scalar
mate of that comparison is the identity-on-sections restriction/pullback comparison by
the ordinary iterated-mates identity, which is the termwise comparison localized. -/
theorem pbcScalarPullMate_restriction_app
    (K : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l F))) ℤ)
    (hK : PbcFlatKFlat Y (pbcIntegralDatum l F) K)
    (hR : PbcFlatKFlat Y (pbcIntegralDatum l E)
      (((pbcRestrict (pbcScalarCoefficientMap l E F i Y)).mapHomologicalComplex (.up ℤ)).obj K)) :
    (whiskerLeft (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i Y))
        (pbcPullComparison g (pbcIntegralDatum l E)) ≫
      (mateEquiv (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
        (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
        (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E F i g).inv)).natTrans).app
        (DerivedCategory.Q.obj K) =
    ((pbcScalarRestrictionPullback l E F i g).inv ≫
      whiskerRight (pbcPullComparison g (pbcIntegralDatum l F))
        (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i X))).app
        (DerivedCategory.Q.obj K) := by
  let resY := pbcRestrict (pbcScalarCoefficientMap l E F i Y)
  let resX := pbcRestrict (pbcScalarCoefficientMap l E F i X)
  let dE := pbcIntegralDatum l E
  let dF := pbcIntegralDatum l F
  have := pbcActualPullComplexCounit_isIso g dF K hK
  have hΘ := pbcScalarPullMate_app l E F i g K hK hR
  have hE := pbcPullComparison_app g dE _ hR
  have hF := congrArg resX.mapDerivedCategory.map (pbcPullComparison_app g dF K hK)
  rw [Functor.map_comp, Functor.map_comp] at hF
  have hρ := pbcScalarRestrictionPullback_app l E F i g K
  have hn := (pbcPullComparison g dE).naturality (resY.mapDerivedCategoryFactors.hom.app K)
  have hfX := resX.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex (pbcModulePullIso g dF).hom (.up ℤ)).app K)
  have hord : DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (pbcModulePullIso g dE).hom (.up ℤ)).app ((resY.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (pbcScalarOrdinaryRestrictionPull l E F i g) (.up ℤ)).app K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (proEtaleRingRestrictionPullbackInv g
            (pbcAdicCompletion Y dE) (pbcAdicCompletion Y dF)
            (pbcAdicCompletion X dE) (pbcAdicCompletion X dF)
            (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
            (pbcCompletedCoefficientIso g dE) (pbcCompletedCoefficientIso g dF)
            (pbcScalarCoefficientInverseSquare l E F i g)) (.up ℤ)).app K) ≫
        DerivedCategory.Q.map ((resX.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (pbcModulePullIso g dF).hom (.up ℤ)).app K)) := by
    have hc : (NatTrans.mapHomologicalComplex
        (pbcModulePullIso g dE).hom (.up ℤ)).app ((resY.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (NatTrans.mapHomologicalComplex (pbcScalarOrdinaryRestrictionPull l E F i g)
          (.up ℤ)).app K =
        (NatTrans.mapHomologicalComplex (proEtaleRingRestrictionPullbackInv g
            (pbcAdicCompletion Y dE) (pbcAdicCompletion Y dF)
            (pbcAdicCompletion X dE) (pbcAdicCompletion X dF)
            (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
            (pbcCompletedCoefficientIso g dE) (pbcCompletedCoefficientIso g dF)
            (pbcScalarCoefficientInverseSquare l E F i g)) (.up ℤ)).app K ≫
          (resX.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (pbcModulePullIso g dF).hom (.up ℤ)).app K) := by
      apply HomologicalComplex.hom_ext
      intro n
      exact NatTrans.congr_app (pbcScalarOrdinaryRestrictionPull_eq l E F i g) (K.X n)
    have hq := congrArg DerivedCategory.Q.map hc
    exact (DerivedCategory.Q.map_comp _ _).symm.trans (hq.trans (DerivedCategory.Q.map_comp _ _))
  exact scalarPullMate_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by
      have h1 := Functor.map_isIso (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i X))
        (pbcActualPullComplexCounit g (pbcIntegralDatum l F) K)
      let rX := pbcRestrict (pbcScalarCoefficientMap l E F i X)
      let PK := ((pbcActualModulePull g (pbcIntegralDatum l F)).mapHomologicalComplex
        (.up ℤ)).obj K
      have h2 : Mono (rX.mapDerivedCategoryFactors.hom.app PK) :=
        inferInstanceAs (Mono (rX.mapDerivedCategoryFactors.app PK).hom)
      refine @mono_comp _ _ _ _ _ _ ?_ _ ?_
      · infer_instance
      · exact h2) hΘ hn hE hF hfX hρ hord

-- Natural transformations out of a derived category agree once they agree on a
-- resolving class of complexes.
private theorem scalarNatTrans_ext_of_resolutions {C D : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [Category D]
    {G H : DerivedCategory C ⥤ D} (f f' : G ⟶ H) (P : CochainComplex C ℤ → Prop)
    (hres : ∀ K, ∃ (L : CochainComplex C ℤ) (s : L ⟶ K), QuasiIso s ∧ P L)
    (h : ∀ K, P K → f.app (DerivedCategory.Q.obj K) = f'.app (DerivedCategory.Q.obj K)) :
    f = f' := by
  ext N
  obtain ⟨K, ⟨e⟩⟩ : ∃ K, Nonempty (DerivedCategory.Q.obj K ≅ N) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso N⟩⟩
  obtain ⟨L, s, hs, hL⟩ := hres K
  have hK : f.app (DerivedCategory.Q.obj K) = f'.app (DerivedCategory.Q.obj K) := by
    rw [← cancel_epi (G.map (DerivedCategory.Q.map s)), f.naturality, f'.naturality, h L hL]
  rw [← cancel_epi (G.map e.hom), f.naturality, f'.naturality, hK]

/-- The scalar mate of the inverse normalized pullback comparison is the termwise
restriction/pullback comparison, after the canonical pullback comparisons.
Source: Stacks Tags 03EK, 06YY, 0D6D and 07A6
(blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: every derived object is represented by a flat-term K-flat complex. Since the
target coefficients are finite free over the source ones, its restriction is again
flat-term K-flat. On such representatives the scalar units, the scalar counits, the
pullback counits and both pullback comparisons are localizations of the ordinary
maps, and the normalized pullback comparison is the localized balanced ordinary
comparison. The ordinary scalar mate of that comparison is the identity-on-sections
restriction/pullback comparison, by the ordinary iterated-mates identity. -/
theorem pbcScalarPullMate_restriction :
    whiskerLeft (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i Y))
        (pbcPullComparison g (pbcIntegralDatum l E)) ≫
      (mateEquiv (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
        (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
        (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E F i g).inv)).natTrans =
    (pbcScalarRestrictionPullback l E F i g).inv ≫
      whiskerRight (pbcPullComparison g (pbcIntegralDatum l F))
        (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i X)) := by
  apply scalarNatTrans_ext_of_resolutions _ _
    (fun K ↦ PbcFlatKFlat Y (pbcIntegralDatum l F) K) (pbcFlatKFlat_resolution Y _)
  intro K hK
  exact pbcScalarPullMate_restriction_app l E F i g K hK
    (pbcScalarRestrict_flatKFlat l E F i Y K hK)

-- Mates are unchanged when the left adjoints are replaced through conjugates of identities.
private theorem scalarMate_change_left
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {R₁ : B ⥤ A} {L₂ L₂' : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a₁ : L₁ ⊣ R₁) (b₁ : L₁' ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₂ : L₂' ⊣ R₂)
    (β : TwoSquare G L₁ L₂ H) (γ : TwoSquare G L₁' L₂' H)
    (h : whiskerLeft G ((conjugateEquiv a₂ b₂).symm (𝟙 R₂)) ≫ β.natTrans =
      γ.natTrans ≫ whiskerRight ((conjugateEquiv a₁ b₁).symm (𝟙 R₁)) H) :
    (mateEquiv a₁ a₂ β).natTrans = (mateEquiv b₁ b₂ γ).natTrans := by
  have h₁ := mateEquiv_conjugateEquiv_vcomp a₁ a₂ b₂ β ((conjugateEquiv a₂ b₂).symm (𝟙 R₂))
  have h₂ := conjugateEquiv_mateEquiv_vcomp a₁ b₁ b₂ ((conjugateEquiv a₁ b₁).symm (𝟙 R₁)) γ
  have hw : β.whiskerRight ((conjugateEquiv a₂ b₂).symm (𝟙 R₂)) =
      γ.whiskerLeft ((conjugateEquiv a₁ b₁).symm (𝟙 R₁)) := by
    ext K
    exact NatTrans.congr_app h K
  rw [hw, h₂, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h₁
  ext K
  have hk := NatTrans.congr_app (congrArg TwoSquare.natTrans h₁) K
  simpa [TwoSquare.whiskerTop, TwoSquare.whiskerBottom] using hk.symm

private theorem scalarMate_adjunct
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : TwoSquare G L L' H)
    (M : A) (N : B) (t : L.obj M ⟶ N) :
    adj'.homEquiv _ _ (s.app M ≫ H.map t) =
      G.map (adj.homEquiv M N t) ≫ (mateEquiv adj adj' s).app N := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := unit_mateEquiv adj adj' s M
  dsimp only [Functor.id_obj] at hu
  rw [← Category.assoc, ← hu, Category.assoc]
  have hn := (mateEquiv adj adj' s).natTrans.naturality t
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← G.map_comp]

/-- The canonical restriction/direct-image comparison is the pullback mate of the
inverse termwise restriction/pullback comparison.
Source: Stacks Tags 0D6D and 0D6E (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: specialize the adjunct identity of the ring-sheaf change adjunction to the
counit, and compare with the adjunct formula for mates. -/
theorem pbcScalarRestrictionDirectImage_mate :
    (mateEquiv (proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y (pbcIntegralDatum l F))
        (pbcAdicCompletion X (pbcIntegralDatum l F))
        (pbcCompletedCoefficientIso g (pbcIntegralDatum l F)))
      (proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y (pbcIntegralDatum l E))
        (pbcAdicCompletion X (pbcIntegralDatum l E))
        (pbcCompletedCoefficientIso g (pbcIntegralDatum l E)))
      (TwoSquare.mk _ _ _ _ (pbcScalarRestrictionPullback l E F i g).inv)).natTrans =
    (pbcScalarRestrictionDirectImage l E F i g).hom := by
  let aS := proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y (pbcIntegralDatum l F))
    (pbcAdicCompletion X (pbcIntegralDatum l F))
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))
  let aR := proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y (pbcIntegralDatum l E))
    (pbcAdicCompletion X (pbcIntegralDatum l E))
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))
  ext N
  have hcl := (proEtaleRingSheafChangeAdjunction g
    (pbcAdicCompletion Y (pbcIntegralDatum l E)) (pbcAdicCompletion Y (pbcIntegralDatum l F))
    (pbcAdicCompletion X (pbcIntegralDatum l E)) (pbcAdicCompletion X (pbcIntegralDatum l F))
    (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))
    (pbcScalarCoefficientInverseSquare l E F i g)).2.2 _ N (aS.counit.app N)
  have hma := scalarMate_adjunct aS aR
    (TwoSquare.mk _ _ _ _ (pbcScalarRestrictionPullback l E F i g).inv) _ N (aS.counit.app N)
  have h1 : aS.homEquiv _ N (aS.counit.app N) = 𝟙 _ := by
    simp [Adjunction.homEquiv_unit]
  rw [h1, CategoryTheory.Functor.map_id, Category.id_comp] at hma hcl
  exact hma.symm.trans hcl

/-- The normalized derived pullback comparison is the conjugate of the canonical
inverse restriction/direct-image comparison.
Source: Stacks Tags 03EL, 0D6D, 0D6E and 07A6
(blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: the derived scalar adjunctions have the tensor-unit normalization on flat-term
K-flat complexes. Hence the scalar mate of the inverse pullback comparison is
computed on such representatives by the ordinary scalar mate of the balanced ordinary
comparison, which is the termwise restriction/pullback comparison. Its pullback mate
is the canonical restriction/direct-image comparison by its unit normalization. -/
theorem pbcScalarOrdinaryPullIso_conjugate :
    conjugateEquiv ((pbcActualDerivedAdjunction g (pbcIntegralDatum l E)).comp
        (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X)))
      ((pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y)).comp
        (pbcActualDerivedAdjunction g (pbcIntegralDatum l F)))
      (pbcScalarOrdinaryPullIso l E F i g).hom =
    (pbcScalarRestrictionDirectImage l E F i g).inv := by
  let aPE := pbcActualDerivedAdjunction g (pbcIntegralDatum l E)
  let aPF := pbcActualDerivedAdjunction g (pbcIntegralDatum l F)
  let aY := pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y)
  let aX := pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X)
  let aQE := proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y (pbcIntegralDatum l E))
    (pbcAdicCompletion X (pbcIntegralDatum l E))
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l E))
  let aQF := proEtaleRingDerivedAdjunction g (pbcAdicCompletion Y (pbcIntegralDatum l F))
    (pbcAdicCompletion X (pbcIntegralDatum l F))
    (pbcCompletedCoefficientIso g (pbcIntegralDatum l F))
  let α := pbcScalarOrdinaryPullIso l E F i g
  let δ := pbcScalarRestrictionDirectImage l E F i g
  have hi := iterated_mateEquiv_conjugateEquiv aY aX aPE aPF (TwoSquare.mk _ _ _ _ α.inv)
  have hm := scalarMate_change_left aPF aQF aPE aQE
    (mateEquiv aY aX (TwoSquare.mk _ _ _ _ α.inv))
    (TwoSquare.mk _ _ _ _ (pbcScalarRestrictionPullback l E F i g).inv)
    (pbcScalarPullMate_restriction l E F i g)
  have hc' : conjugateEquiv (aY.comp aPF) (aPE.comp aX) α.inv = δ.hom :=
    hi.symm.trans (hm.trans (pbcScalarRestrictionDirectImage_mate l E F i g))
  have hcomp : conjugateEquiv (aPE.comp aX) (aY.comp aPF) α.hom ≫ δ.hom = 𝟙 _ := by
    rw [← hc']
    refine (conjugateEquiv_comp (aPE.comp aX) (aY.comp aPF) (aPE.comp aX) α.hom α.inv).trans ?_
    rw [α.inv_hom_id]
    exact conjugateEquiv_id (aPE.comp aX)
  apply (cancel_mono δ.hom).1
  exact hcomp.trans δ.inv_hom_id.symm

/-- The scalar mate of the direct-image comparison is the canonical inverse
restriction/direct-image comparison.
Source: Stacks Tags 03EL, 0D6D, 0D6E and 07A6
(blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: by the iterated-mates identity the left side is the conjugate of the
normalized derived pullback comparison, which is computed above. -/
theorem pbcScalarDirectImageMap_scalarMate :
    (mateEquiv (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
        (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
        (TwoSquare.mk _ _ _ _ (pbcScalarDirectImageMap l E F i g))).natTrans =
      (pbcScalarRestrictionDirectImage l E F i g).inv := by
  have h := iterated_mateEquiv_conjugateEquiv
    (pbcActualDerivedAdjunction g (pbcIntegralDatum l E))
    (pbcActualDerivedAdjunction g (pbcIntegralDatum l F))
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
    (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E F i g).hom)
  rw [← pbcScalarOrdinaryPullIso_conjugate]
  refine Eq.trans ?_ (congrArg TwoSquare.natTrans h)
  simp only [pbcScalarDirectImageMap, pbcActualScalarDirectImageMap, pbcScalarOrdinaryPullIso]

private theorem scalarInverseMate_isIso_of_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {R₁ : B ⥤ A} {L₂ L₂' : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₁ : L₁' ⊣ R₁) (b₂ : L₂' ⊣ R₂)
    (β : TwoSquare R₁ H G R₂)
    (hb : IsIso (((mateEquiv b₁ b₂).symm β).natTrans)) :
    IsIso (((mateEquiv a₁ a₂).symm β).natTrans) := by
  let e₁ : L₁' ≅ L₁ := (conjugateIsoEquiv a₁ b₁).symm (Iso.refl R₁)
  let e₂ : L₂' ≅ L₂ := (conjugateIsoEquiv a₂ b₂).symm (Iso.refl R₂)
  have h₁ : conjugateEquiv a₁ b₁ e₁.hom = 𝟙 R₁ :=
    (conjugateEquiv a₁ b₁).apply_symm_apply (𝟙 R₁)
  have h₂ : conjugateEquiv a₂ b₂ e₂.hom = 𝟙 R₂ :=
    (conjugateEquiv a₂ b₂).apply_symm_apply (𝟙 R₂)
  let w := (mateEquiv a₁ a₂).symm β
  let w' := (mateEquiv b₁ b₂).symm β
  have h : w'.whiskerLeft e₁.hom = w.whiskerRight e₂.hom := by
    apply (mateEquiv a₁ b₂).injective
    rw [conjugateEquiv_mateEquiv_vcomp a₁ b₁ b₂ e₁.hom w',
      mateEquiv_conjugateEquiv_vcomp a₁ a₂ b₂ w e₂.hom]
    simp only [w, w', Equiv.apply_symm_apply, h₁, h₂]
    ext X
    simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom]
  let : ∀ X, IsIso (w.natTrans.app X) := fun X ↦ by
    have hc := congrArg (fun t ↦ t.natTrans.app X) h
    change w'.app X ≫ H.map (e₁.hom.app X) = e₂.hom.app (G.obj X) ≫ w.app X at hc
    have : IsIso (w'.app X) := NatIso.isIso_app_of_isIso _ X
    have : IsIso (e₂.hom.app (G.obj X) ≫ w.app X) := by
      rw [← hc]
      infer_instance
    exact IsIso.of_isIso_comp_left (e₂.hom.app (G.obj X)) (w.app X)
  exact NatIso.isIso_of_isIso_app _

/-- The canonical scalar/direct-image mate is invertible for finite coefficient extensions.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: the target valuation ring is finite free over the source. Locally choose a
finite free basis. Scalar extension is then a finite sum, and derived direct image
commutes with finite sums. The resulting identification has the same ordinary
tensor formula as the mate, so descends independently of that basis. Equivalently
use the finite perfect projection formula and the tensor-unit normalization. -/
@[instance] theorem pbcScalarDirectImageMap_isIso :
    IsIso (pbcScalarDirectImageMap l E F i g) := by
  classical
  obtain ⟨d, ⟨b⟩⟩ := pbcScalarCoefficient_finiteFree l E F i Y
  let RE := (adicLisseForget Y).obj (pbcAdicCompletion Y (pbcIntegralDatum l E))
  let N := SheafOfModules.unit RE
  let : HasBiproduct (fun _ : Fin d ↦ N) := HasBiproduct.of_hasProduct _
  let e : (∏ᶜ fun _ : Fin d ↦ N) ≅
      SheafOfModules.free (R := RE) (ULift.{u + 1} (Fin d)) :=
    (biproduct.isoProduct (fun _ : Fin d ↦ N)).symm ≪≫
      biproduct.isoCoproduct (fun _ : Fin d ↦ N) ≪≫
        Sigma.whiskerEquiv (Equiv.ulift.{u + 1, 0}).symm (fun _ ↦ Iso.refl N)
  let R' : FiniteFreeDirectImage.Coefficients g :=
    ⟨pbcAdicCompletion Y (pbcIntegralDatum l E), pbcAdicCompletion X (pbcIntegralDatum l E),
      pbcCompletedCoefficientIso g (pbcIntegralDatum l E)⟩
  let S' : FiniteFreeDirectImage.Coefficients g :=
    ⟨pbcAdicCompletion Y (pbcIntegralDatum l F), pbcAdicCompletion X (pbcIntegralDatum l F),
      pbcCompletedCoefficientIso g (pbcIntegralDatum l F)⟩
  let a' : FiniteFreeDirectImage.CoefficientMap R' S' :=
    ⟨pbcScalarCoefficientMap l E F i Y, pbcScalarCoefficientMap l E F i X,
      pbcScalarCoefficientInverseSquare l E F i g⟩
  obtain ⟨sY, sX, _, _, hi, _⟩ := FiniteFreeDirectImage.finiteFreeDirectImageCoherence g
  have : IsIso (FiniteFreeDirectImage.comparison sY sX a') := (hi R' S' a' d ⟨b ≪≫ e⟩).1
  let δ := pbcScalarRestrictionDirectImage l E F i g
  have hm : (mateEquiv (sX.adjunction a'.source) (sY.adjunction a'.target)
      (TwoSquare.mk _ _ _ _ (FiniteFreeDirectImage.comparison sY sX a'))).natTrans =
      δ.inv := by
    rw [FiniteFreeDirectImage.comparison, iterated_mateEquiv_conjugateEquiv]
    exact (conjugateEquiv _ _).apply_symm_apply δ.inv
  have he : ((mateEquiv (sX.adjunction a'.source) (sY.adjunction a'.target)).symm
      (TwoSquare.mk _ _ _ _ δ.inv)).natTrans =
        FiniteFreeDirectImage.comparison sY sX a' := by
    apply congrArg TwoSquare.natTrans
    apply (mateEquiv (sX.adjunction a'.source) (sY.adjunction a'.target)).injective
    rw [Equiv.apply_symm_apply]
    ext K
    exact (NatTrans.congr_app hm K).symm
  have : IsIso (((mateEquiv (sX.adjunction a'.source)
      (sY.adjunction a'.target)).symm (TwoSquare.mk _ _ _ _ δ.inv)).natTrans) := by
    rw [he]
    infer_instance
  have hiso := scalarInverseMate_isIso_of_isIso
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
    (sX.adjunction a'.source) (sY.adjunction a'.target) (TwoSquare.mk _ _ _ _ δ.inv) this
  have hs : mateEquiv (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
      (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
      (TwoSquare.mk _ _ _ _ (pbcScalarDirectImageMap l E F i g)) =
        TwoSquare.mk _ _ _ _ δ.inv := by
    ext K
    exact NatTrans.congr_app (pbcScalarDirectImageMap_scalarMate l E F i g) K
  have hμ := congrArg TwoSquare.natTrans (((mateEquiv
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))).eq_symm_apply).2 hs)
  change IsIso (TwoSquare.mk _ _ _ _ (pbcScalarDirectImageMap l E F i g)).natTrans
  rw [hμ]
  exact hiso

/-- The canonical invertible direct-image comparison, with its mate definition retained.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
@[irreducible] def pbcScalarDirectImageIso :
    pbcActualDerivedPush g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i Y ≅
      pbcEmbeddingAmbientTensor l E F i X ⋙
        pbcActualDerivedPush g (pbcIntegralDatum l F) :=
  asIso (pbcScalarDirectImageMap l E F i g)

private theorem pbcScalarDirectImageIso_hom :
    (pbcScalarDirectImageIso l E F i g).hom = pbcScalarDirectImageMap l E F i g := by
  unfold pbcScalarDirectImageIso
  rfl

-- Construct both arrows from the two reflection Hom bijections. Scalar restriction
-- lets the source reflection compute maps into complete target-coefficient objects.
private theorem scalar_reflector_transport
    {V Z : Type*} [Category V] [Category Z]
    (F : V ⥤ Z) (U : Z ⥤ V) (adj : F ⊣ U)
    (L : V ⥤ V) (M : Z ⥤ Z) (η : 𝟭 V ⟶ L) (ε : 𝟭 Z ⟶ M)
    (P : V → Prop) (Q : Z → Prop)
    (hd : ∀ X, Q (M.obj X))
    (hb : ∀ X Y, P Y → Function.Bijective (fun f : L.obj X ⟶ Y ↦ η.app X ≫ f))
    (he : ∀ X Y, Q Y → Function.Bijective (fun f : M.obj X ⟶ Y ↦ ε.app X ≫ f))
    (hF : ∀ X, Q (F.obj (L.obj X))) (hU : ∀ Y, Q Y → P (U.obj Y)) :
    ∃! e : F ⋙ M ≅ L ⋙ F,
      ∀ X, ε.app (F.obj X) ≫ e.hom.app X = F.map (η.app X) := by
  classical
  have hj (X : V) (Y : Z) (hY : Q Y) :
      Function.Bijective (fun f : F.obj (L.obj X) ⟶ Y ↦ F.map (η.app X) ≫ f) := by
    constructor
    · intro f g h
      apply (adj.homEquiv _ _).injective
      apply (hb X (U.obj Y) (hU Y hY)).1
      simpa only [← adj.homEquiv_naturality_left, Functor.id_obj] using
        congrArg (adj.homEquiv X Y) h
    · intro f
      obtain ⟨g, hg⟩ := (hb X (U.obj Y) (hU Y hY)).2 ((adj.homEquiv X Y) f)
      refine ⟨(adj.homEquiv (L.obj X) Y).symm g, ?_⟩
      apply (adj.homEquiv X Y).injective
      rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
      exact hg
  let f (X : V) := (he (F.obj X) (F.obj (L.obj X)) (hF X)).2
    (F.map (η.app X)) |>.choose
  have hf (X : V) : ε.app (F.obj X) ≫ f X = F.map (η.app X) :=
    (he (F.obj X) (F.obj (L.obj X)) (hF X)).2 (F.map (η.app X)) |>.choose_spec
  let g (X : V) := (hj X (M.obj (F.obj X)) (hd _)).2 (ε.app (F.obj X)) |>.choose
  have hg (X : V) : F.map (η.app X) ≫ g X = ε.app (F.obj X) :=
    (hj X (M.obj (F.obj X)) (hd _)).2 (ε.app (F.obj X)) |>.choose_spec
  let eX (X : V) : M.obj (F.obj X) ≅ F.obj (L.obj X) :=
    { hom := f X
      inv := g X
      hom_inv_id := by
        apply (he _ _ (hd (F.obj X))).1
        change ε.app (F.obj X) ≫ (f X ≫ g X) = ε.app (F.obj X) ≫ 𝟙 _
        rw [← Category.assoc, hf, hg, Category.comp_id]
      inv_hom_id := by
        apply (hj X _ (hF X)).1
        change F.map (η.app X) ≫ (g X ≫ f X) = F.map (η.app X) ≫ 𝟙 _
        rw [← Category.assoc, hg, hf, Category.comp_id] }
  let e : F ⋙ M ≅ L ⋙ F := NatIso.ofComponents eX (fun {X Y} h ↦ by
    apply (he _ _ (hF Y)).1
    change ε.app (F.obj X) ≫ (M.map (F.map h) ≫ f Y) =
      ε.app (F.obj X) ≫ (f X ≫ F.map (L.map h))
    rw [← Category.assoc, ← ε.naturality, Category.assoc, hf]
    rw [← Category.assoc, hf]
    simp only [Functor.id_map]
    rw [← F.map_comp, ← F.map_comp]
    simpa only [Functor.id_map] using congrArg F.map (η.naturality h))
  refine ⟨e, hf, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (he _ _ (hF X)).1
  exact (he' X).trans (hf X).symm

private theorem scalar_completion_reflection
    (W : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K L : PbcCompletedDerived W d) (hL : PbcIsIntrinsicallyComplete W d L) :
    Function.Bijective (fun f : (pbcActualCompletion d W).obj K ⟶ L ↦
      (pbcActualCompletionUnit d W).app K ≫ f) := by
  let P : ObjectProperty (PbcCompletedDerived W d) := PbcIsIntrinsicallyComplete W d
  let adj := Adjunction.ofIsRightAdjoint P.ι
  exact ((ObjectProperty.fullyFaithfulι P).homEquiv.symm.trans
    (adj.homEquiv K ⟨L, hL⟩)).bijective

/-- Scalar extension commutes with completion through the actual quotient augmentation.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: scalar tensor of a source completion output is target-complete, and scalar
restriction preserves completeness. Transfer the source reflection Hom bijection
through the specified scalar adjunction. Together with the target reflection Hom
bijection, this constructs arrows in both directions. Cancel the respective units
to prove their inverse identities, naturality, and uniqueness. The forward arrow
is defined by its displayed unit equation, retaining the actual quotient unit. -/
theorem pbcScalarCompletionIso_exists (W : Scheme.{u}) :
    ∃! e : pbcEmbeddingAmbientTensor l E F i W ⋙
        pbcActualCompletion (pbcIntegralDatum l F) W ≅
      pbcActualCompletion (pbcIntegralDatum l E) W ⋙
        pbcEmbeddingAmbientTensor l E F i W,
      ∀ K : PbcCompletedDerived W (pbcIntegralDatum l E),
        (pbcActualCompletionUnit (pbcIntegralDatum l F) W).app
            ((pbcEmbeddingAmbientTensor l E F i W).obj K) ≫ e.hom.app K =
          (pbcEmbeddingAmbientTensor l E F i W).map
            ((pbcActualCompletionUnit (pbcIntegralDatum l E) W).app K) := by
  exact scalar_reflector_transport
    (pbcEmbeddingAmbientTensor l E F i W)
    (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i W))
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i W))
    (pbcActualCompletion (pbcIntegralDatum l E) W)
    (pbcActualCompletion (pbcIntegralDatum l F) W)
    (pbcActualCompletionUnit (pbcIntegralDatum l E) W)
    (pbcActualCompletionUnit (pbcIntegralDatum l F) W)
    (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E))
    (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F))
    (fun K ↦ ((ObjectProperty.ι
      (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F))).leftAdjoint.obj K).property)
    (scalar_completion_reflection W (pbcIntegralDatum l E))
    (scalar_completion_reflection W (pbcIntegralDatum l F))
    (pbcScalarCompletedObjectComplete l E F i W)
    (pbcScalarRestrictionComplete l E F i W)

/-- The unique completion comparison preserving the specified quotient unit.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
@[irreducible] def pbcScalarCompletionIso (W : Scheme.{u}) :
    pbcEmbeddingAmbientTensor l E F i W ⋙
        pbcActualCompletion (pbcIntegralDatum l F) W ≅
      pbcActualCompletion (pbcIntegralDatum l E) W ⋙
        pbcEmbeddingAmbientTensor l E F i W :=
  (pbcScalarCompletionIso_exists l E F i W).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcComplete_iso (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    ObjectProperty.IsClosedUnderIsomorphisms (PbcIsIntrinsicallyComplete W d) := by
  constructor
  intro K L e hK
  obtain ⟨r, f, hf, C, eC, hC⟩ := hK
  refine ⟨r, f, hf, C,
    eC ≪≫ (pbcDerivedExtend (pbcCompletedComparison W d).inv).mapIso e, ?_⟩
  change IsIso (eC.inv ≫ _) at hC
  have hu := (isIso_comp_left_iff eC.inv _).mp hC
  change IsIso ((_ ≫ eC.inv) ≫ _)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite-free coefficient extension preserves ambient intrinsic completeness.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: use the unit-normalized scalar/completion comparison. The completion unit
of the complete input is invertible, and tensor carries it to an invertible map.
The comparison's unit equation therefore makes the target completion unit
invertible. Its target is a reflected, intrinsically complete object; invariance
of intrinsic completeness under isomorphism gives the claim. -/
theorem pbcScalarPreservesComplete (W : Scheme.{u})
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E))) :
    PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F)
      ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj) := by
  let dE := pbcIntegralDatum l E
  let dF := pbcIntegralDatum l F
  let I := ObjectProperty.ι (PbcIsIntrinsicallyComplete W dE)
  let adj := Adjunction.ofIsRightAdjoint I
  have hη : IsIso ((pbcActualCompletionUnit dE W).app K.obj) := by
    change IsIso (adj.unit.app (I.obj K))
    infer_instance
  obtain ⟨e, he, _⟩ := pbcScalarCompletionIso_exists l E F i W
  have hmap : IsIso ((pbcEmbeddingAmbientTensor l E F i W).map
      ((pbcActualCompletionUnit dE W).app K.obj)) := inferInstance
  have hcomp : IsIso ((pbcActualCompletionUnit dF W).app
      ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj) ≫ e.hom.app K.obj) := by
    rw [he K.obj]
    exact hmap
  have hunit : IsIso ((pbcActualCompletionUnit dF W).app
      ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj)) :=
    (isIso_comp_right_iff _ (e.hom.app K.obj)).mp hcomp
  have := pbcComplete_iso W dF
  exact ObjectProperty.prop_of_iso (PbcIsIntrinsicallyComplete W dF)
    (asIso ((pbcActualCompletionUnit dF W).app
      ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj))).symm
    ((ObjectProperty.ι (PbcIsIntrinsicallyComplete W dF)).leftAdjoint.obj
      ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj)).property

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Completed scalar/pullback is the ordinary comparison followed by the canonical
completion comparisons. Source: blueprint order 1307
(blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
@[irreducible] def pbcScalarCompletedPullIso :
    pbcEmbeddingAmbientTensor l E F i Y ⋙
        pbcActualCompletedPull g (pbcIntegralDatum l F) ≅
      pbcActualCompletedPull g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i X :=
  NatIso.ofComponents
    (F := pbcEmbeddingAmbientTensor l E F i Y ⋙
      pbcActualCompletedPull g (pbcIntegralDatum l F))
    (G := pbcActualCompletedPull g (pbcIntegralDatum l E) ⋙
      pbcEmbeddingAmbientTensor l E F i X) (fun K ↦
    (pbcActualCompletion (pbcIntegralDatum l F) X).mapIso
        ((pbcScalarOrdinaryPullIso l E F i g).app K) ≪≫
      (pbcScalarCompletionIso l E F i X).app
        ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K)) (fun {K L} f ↦ by
    have he := (pbcScalarOrdinaryPullIso l E F i g).hom.naturality f
    have hc := (pbcScalarCompletionIso l E F i X).hom.naturality
      ((pbcActualDerivedPull g (pbcIntegralDatum l E)).map f)
    dsimp only [CategoryTheory.Functor.comp_map] at he hc
    dsimp only [pbcActualCompletedPull, CategoryTheory.Functor.comp_map, Iso.trans_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.app_hom]
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, he,
      CategoryTheory.Functor.map_comp, Category.assoc, hc, Category.assoc])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcScalarCompletedPullIso_hom
    (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    (pbcScalarCompletedPullIso l E F i g).hom.app K =
      (pbcActualCompletion (pbcIntegralDatum l F) X).map
          ((pbcScalarOrdinaryPullIso l E F i g).hom.app K) ≫
        (pbcScalarCompletionIso l E F i X).hom.app
          ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K) := by
  unfold pbcScalarCompletedPullIso
  rfl

variable {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {a : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcCompletion_hom_ext (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K L : PbcCompletedDerived W d) (hL : PbcIsIntrinsicallyComplete W d L)
    (f g : (pbcActualCompletion d W).obj K ⟶ L)
    (h : (pbcActualCompletionUnit d W).app K ≫ f =
      (pbcActualCompletionUnit d W).app K ≫ g) : f = g := by
  let I := ObjectProperty.ι (PbcIsIntrinsicallyComplete W d)
  let adj := Adjunction.ofIsRightAdjoint I
  let N : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete W d) := ⟨L, hL⟩
  let a : I.leftAdjoint.obj K ⟶ N := ObjectProperty.homMk f
  let b : I.leftAdjoint.obj K ⟶ N := ObjectProperty.homMk g
  have hab : adj.homEquiv K N a = adj.homEquiv K N b := by
    change adj.unit.app K ≫ I.map a = adj.unit.app K ≫ I.map b at h
    simpa only [Adjunction.homEquiv_unit] using h
  exact congrArg (fun z ↦ z.hom) ((adj.homEquiv K N).injective hab)

end AmbientOperations
end AlgebraicGeometry.Scheme
