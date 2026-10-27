/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.Paper.ProEtaleScalarMateNormalization
public import Sheaf.Paper.IntegralCompactSupportCoefficientData
import Sheaf.Algebra.Homology.KFlatResolutionGeneral
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules

/-! # Supported scalar tensors and their cohomology interval

Source: Stacks Project, sites-cohomology.tex, Tags 08FZ, 0GL1 and 06YY;
proetale.tex, Tag 099T (blueprint: lem-sp-supported-scalar-tor-interval).

Tensor models are presentations of the ordinary uncompleted K-flat tensor. The maps
below specialize existing normalized comparisons; they are not arbitrary endpoint maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SupportedScalarTorInterval

/-- The constant coefficient family with its constant-section inverse-image comparison.
Source: Stacks 0H7J and 0GL1 (blueprint: lem-sp-supported-scalar-tor-interval). -/
def coefficients (A : Type u) [CommRing A] : WeilConjectures.PurCompactSupport.Coefficients where
  ring W := proEtaleConstantRing W A
  pull f := proEtaleConstantRingComparison f A

/-- The constant coefficient map, with its existing naturality square.
Source: Stacks 03EL (blueprint: lem-sp-supported-scalar-tor-interval). -/
def change {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    WeilConjectures.PurCompactSupport.Change (coefficients A) (coefficients B) where
  map W := proEtaleConstantRingMap (T := W) φ
  square f := (proEtaleConstantInverseImageMap_naturality f
    (CommRingCat.ofHom (RingHom.ulift φ))).symm

/-- Tensor with the constant B-module in degree zero, retaining only its A-action.
Source: Stacks 06YY and 08FZ (blueprint: lem-sp-supported-scalar-tor-interval). -/
abbrev tensor {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u})
    (a : ProEtaleTensorModel W (proEtaleConstantRing W A))
    (M : proEtaleDerivedCategory W A) : proEtaleDerivedCategory W A :=
  a.tensor.obj (M, DerivedCategory.Q.obj (scalarMateCoefficientComplex φ W))

/-- The canonical forward open projection followed by j inverse B_Z = B_U.
Its first factor is the inverse of the existing open-unit adjunct, and its second
factor uses the normalized constant-coefficient pullback, with no choice of maps.
Source: Stacks 0GL1 and 03EL (blueprint: lem-sp-supported-scalar-tor-interval). -/
def projection {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (aU : ProEtaleTensorModel U (proEtaleConstantRing U A))
    (aZ : ProEtaleTensorModel Z (proEtaleConstantRing Z A))
    (M : proEtaleDerivedCategory U A) :
    tensor φ Z aZ ((openExtension (A := A) j).obj M) ⟶
      (openExtension (A := A) j).obj (tensor φ U aU M) :=
  (WeilConjectures.PurCompactSupport.openProjectionIso (coefficients A) j aU aZ M
      (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ Z))).hom ≫
    (openExtension (A := A) j).map
      (aU.tensor.map (Prod.mkHom (𝟙 M) (scalarMateDerivedCoefficientPullback φ j).hom))

/-- The identity of the K-flat tensor complex, then the open scalar-restriction map.
The scalar/tensor isomorphism is already uniquely characterized on K-flat
representatives; the open restriction comparison is the existing adjunction mate.
Source: Stacks 06YY, 03DJ and 0E8I (blueprint: lem-sp-supported-scalar-tor-interval). -/
def restrictionComparison {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (aU : ProEtaleTensorModel U (proEtaleConstantRing U A))
    (M : proEtaleDerivedCategory U A) :
    (openExtension (A := A) j).obj (tensor φ U aU M) ⟶
      (scalarRestriction φ Z).obj
        ((openExtension (A := B) j).obj ((scalarExtensionFunctor φ U).obj M)) :=
  (openExtension (A := A) j).map ((scalarMateDerivedTensorIso φ U aU).inv.app M) ≫
    (WeilConjectures.PurCompactSupport.openRestriction (change φ) j).hom.app
      ((scalarExtensionFunctor φ U).obj M)

/-- The supported tensor comparisons are invertible, all three displayed ambient
A-objects and the tensor on U have cohomology in [a,b], and that same interval
holds for every etale origin E of the first ambient tensor.
Source: Stacks 08FZ, 0GL1, 06YY, 03DJ, 04JC and 099T
(blueprint: lem-sp-supported-scalar-tor-interval).

Proof:
1. Test HasProEtaleTorAmplitude against the constant B_U-module in degree zero.
   This bounds Q without any flatness or finite projective dimension of B/A.
2. Specialize def-sp-open-coefficient-adjunction-data to the constant A family.
   lem-sp-intrinsic-open-projection-invertible inverts its open-unit adjunct.
   prop-weil-pbc-proetale-constant-ring-map identifies j inverse B_Z with B_U.
   The resulting canonical forward map is exactly projection.
3. On a common K-flat representative P, both Q and the restriction of M_B have
   underlying complex P tensor_A B. The normalized scalarMateDerivedTensorIso
   identifies them by this tensor complex. The coefficient-restriction comparison
   of lem-cbc-proetale-extension-zero gives exactly restrictionComparison.
4. Exact degreewise extension by zero commutes with cohomology, so j_!Q has
   zero cohomology off [a,b]. The two displayed isomorphisms transfer this bound
   to the ambient tensor and to the restricted B-extension.
5. For any E and r, these bounds give zero cohomology for nu*E off [a,b].
   lem-sf-comparison-pullback-exact identifies it with nu*H^q(E) on arbitrary
   unbounded representatives. det-pe-classical-sheaves-modules makes nu* faithful
   on module sheaves, hence reflects zero objects. Therefore H^q(E)=0 there.
   No full faithfulness on the unbounded derived category is used.
-/
theorem supported_scalar_tor_interval
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (_hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (φ : A →+* B) {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (a b : ℤ) (_hab : a ≤ b)
    (aU : ProEtaleTensorModel U (proEtaleConstantRing U A))
    (aZ : ProEtaleTensorModel Z (proEtaleConstantRing Z A))
    (M : proEtaleDerivedCategory U A) (_hTor : HasProEtaleTorAmplitude U A M a b) :
    IsIso (projection φ j aU aZ M) ∧
    IsIso (restrictionComparison φ j aU M) ∧
    (∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (tensor φ U aU M)) ∧
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (tensor φ Z aZ ((openExtension (A := A) j).obj M))) ∧
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((openExtension (A := A) j).obj (tensor φ U aU M))) ∧
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((scalarRestriction φ Z).obj
          ((openExtension (A := B) j).obj ((scalarExtensionFunctor φ U).obj M))))) ∧
    (∀ E : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Z,
      ∀ _r : (finiteCoefficientIntrinsicDerivedComparison Z A).obj E ≅
        tensor φ Z aZ ((openExtension (A := A) j).obj M),
      ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj E)) := by
  classical
  have hproj : IsIso (projection φ j aU aZ M) := by
    have : IsIso (aU.tensor.map
        (Prod.mkHom (𝟙 M) (scalarMateDerivedCoefficientPullback φ j).hom)) := by
      change IsIso (aU.tensor.map
        (Iso.prod (Iso.refl M) (scalarMateDerivedCoefficientPullback φ j)).hom)
      infer_instance
    dsimp only [projection]
    infer_instance
  have hres : IsIso (restrictionComparison φ j aU M) := by
    dsimp only [restrictionComparison]
    infer_instance
  have hU (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (tensor φ U aU M)) := by
    let L := DerivedCategory.Q.objPreimage M
    let eL := DerivedCategory.Q.objObjPreimageIso M
    obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral L
    have := hf
    let eP : DerivedCategory.Q.obj P ≅ M := asIso (DerivedCategory.Q.map f) ≪≫ eL
    let e := (scalarMateDerivedTensorIso φ U aU).app (DerivedCategory.Q.obj P)
    let eS := scalarExtensionFunctorKFlatIso φ U P hP
    let eR := (scalarMateRestriction φ U).mapDerivedCategory.mapIso eS ≪≫
      (scalarMateRestriction φ U).mapDerivedCategoryFactors.app
        ((reductionChangeComplex U (proEtaleConstantRingMap (T := U) φ)).obj P) ≪≫
      DerivedCategory.Q.mapIso (scalarMateOrdinaryComplexIso φ U P)
    have hz := _hTor.2 L P ⟨eL⟩ f hf hP (scalarMateCoefficient φ U) q hq
    exact hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
      (aU.tensor.mapIso (Iso.prod eP.symm (Iso.refl _)) ≪≫ e.symm ≪≫ eR))
  have hJ (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((openExtension (A := A) j).obj (tensor φ U aU M))) := by
    exact Functor.isZero_homologyFunctor_mapDerivedCategory_obj
      (WeilConjectures.PurCompactSupport.openExtension (coefficients A) j) (hU q hq)
  have hZ (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (tensor φ Z aZ ((openExtension (A := A) j).obj M))) := by
    exact (hJ q hq).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso (asIso (projection φ j aU aZ M)))
  refine ⟨hproj, hres, ?_, ?_⟩
  · intro q hq
    refine ⟨hU q hq, hZ q hq, hJ q hq, ?_⟩
    exact (hJ q hq).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso
        (asIso (restrictionComparison φ j aU M)).symm)
  · intro E r q hq
    have := (finiteCoefficientIntrinsicRealization_exact Z A).1
    obtain ⟨_, _, _, hfaith, _⟩ := proEtaleClassicalSheavesModules Z (ULift.{u + 1, u} A)
    have : (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z).Faithful :=
      ⟨fun {X Y} ↦ (hfaith X Y).injective⟩
    have : (finiteCoefficientIntrinsicComparison Z A).Faithful :=
      inferInstanceAs (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z ⋙
        finiteCoefficientIntrinsicRealization Z A).Faithful
    apply Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      (finiteCoefficientIntrinsicComparison Z A)
    exact (hZ q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso r)

end AlgebraicGeometry.ProEtale.SupportedScalarTorInterval
