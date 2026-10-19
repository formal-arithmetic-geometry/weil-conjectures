/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP, SHEAF group Q145
-/
module

public import Sheaf.Paper.DualityPairing
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import Sheaf.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import WeilConjectures.Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Sites.PullbackFlat
public import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
import Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.Paper.KFlatRingedToposPullback
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

public import Mathlib.AlgebraicGeometry.Morphisms.Proper

public import Sheaf.AlgebraicGeometry.DerivedCategories

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses

public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory

import Sheaf.Algebra.Homology.KFlat

import Mathlib.Algebra.Homology.BifunctorShift

import Sheaf.Algebra.Homology.HomComplex

import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses

import Mathlib.AlgebraicGeometry.Morphisms.Flat

import Mathlib.AlgebraicGeometry.OpenImmersion

import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction

import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

import WeilConjectures.Compactification.NagataCompactification
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose
import Sheaf.AlgebraicGeometry.EtaleComparison
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-! # Restriction of the evaluation-transpose double-dual morphism

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-biduality-general,
order 2124; Stacks Project, Tags 08J9 and 08JB
(blueprint: lem-weil-delta-restriction).

The comparisons below are normalized by evaluation and by the compact-support counit.
All categories are ordinary unbounded categories of constant-ring module sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true

universe u v w z z'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

/-- Evaluation with the factors in the order DK tensor K.
Source: blueprint order 2124, evaluation of lem-weil-duality-pairing; Stacks 08J9
(blueprint: lem-weil-delta-restriction). -/
def restrictionDualEvaluation {C : Type z} [Category.{v} C]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (adj : ∀ K : C, T.obj K ⊣ H.obj (op K))
    (b : ∀ K L : C, (T.obj K).obj L ≅ (T.obj L).obj K) (Ω K : C) :
    (T.obj ((H.obj (op K)).obj Ω)).obj K ⟶ Ω :=
  (b _ _).hom ≫ (adj K).counit.app Ω

/-- The double-dual arrow is the actual transpose of evaluation.
Source: blueprint order 2124, lem-weil-duality-pairing; Stacks 08J9
(blueprint: lem-weil-delta-restriction). -/
def restrictionDualDelta {C : Type z} [Category.{v} C]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (adj : ∀ K : C, T.obj K ⊣ H.obj (op K))
    (b : ∀ K L : C, (T.obj K).obj L ≅ (T.obj L).obj K) (Ω K : C) :
    K ⟶ (dualityDoubleFunctor H Ω).obj K :=
  (adj ((H.obj (op K)).obj Ω)).homEquiv K Ω
    (restrictionDualEvaluation T H adj b Ω K)

/-- The canonical natural restriction isomorphism, its evaluation normalization, the
contravariant double-dual identity, and its transported form.
Source: blueprint order 2124, displayed identity and following sentence; Stacks 08JB
(blueprint: lem-weil-delta-restriction). -/
def DualDeltaRestriction {C : Type z} [Category.{v} C]
    {D : Type z'} [Category.{w} D] (r : C ⥤ D)
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (T' : D ⥤ D ⥤ D) (H' : Dᵒᵖ ⥤ D ⥤ D)
    (adj : ∀ K : C, T.obj K ⊣ H.obj (op K))
    (adj' : ∀ K : D, T'.obj K ⊣ H'.obj (op K))
    (b : ∀ K L : C, (T.obj K).obj L ≅ (T.obj L).obj K)
    (b' : ∀ K L : D, (T'.obj K).obj L ≅ (T'.obj L).obj K)
    (μ : ∀ K L : C, (T'.obj (r.obj K)).obj (r.obj L) ≅ r.obj ((T.obj K).obj L))
    (Ω : C) (Ω' : D) (θ : r.obj Ω ≅ Ω') : Prop :=
  ∃ α : H.flip.obj Ω ⋙ r ≅ r.op ⋙ H'.flip.obj Ω',
    (∀ K : C, α.hom.app (op K) =
      (adj' (r.obj K)).homEquiv (r.obj ((H.obj (op K)).obj Ω)) Ω'
        ((μ K ((H.obj (op K)).obj Ω)).hom ≫ r.map ((adj K).counit.app Ω) ≫ θ.hom)) ∧
    (∀ K : C,
      r.map (restrictionDualDelta T H adj b Ω K) ≫
          α.hom.app (op ((H.obj (op K)).obj Ω)) =
        restrictionDualDelta T' H' adj' b' Ω' (r.obj K) ≫
          (H'.map (α.hom.app (op K)).op).app Ω') ∧
    (∀ K : C,
      r.map (restrictionDualDelta T H adj b Ω K) ≫
          (α.app (op ((H.obj (op K)).obj Ω)) ≪≫
            ((H'.mapIso (α.app (op K)).op).app Ω').symm).hom =
        restrictionDualDelta T' H' adj' b' Ω' (r.obj K))

end CategoryTheory

namespace AlgebraicGeometry

namespace Etale

/-- Extract the Koszul braiding whose components the existing pairing assertion fixes.
The componentwise equality in that assertion determines the entire natural isomorphism.
Source: blueprint order 2124, evaluation restriction; Stacks 08J9
(blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionPairingBraiding
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u})
    (Ω : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (h : AmbientDualityPairing A Y Ω) :
    derivedTensor A Y ≅ (derivedTensor A Y).flip :=
  Classical.choose h

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The unique Koszul braiding specified componentwise by the pairing theorem.
The witness is determined by its equality with the descended braiding, so this selection
contains no arbitrary monoidal structure or pairing.
Source: blueprint order 2124, lem-weil-duality-pairing; Stacks 06YU and 0FPT
(blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionBraiding {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    derivedTensor (ModuleCat.{u + 1} Λ) Y ≅ (derivedTensor (ModuleCat.{u + 1} Λ) Y).flip :=
  deltaRestrictionPairingBraiding (ModuleCat.{u + 1} Λ) Y
    (dualizingComplex (ModuleCat.{u + 1} Λ) aY) ((ambient_duality_pairing Λ aY).1)

/-- The canonical tensor comparison for exact restriction; it transports the existing
K-flat-derived pullback comparison through L j* = D j*.
Source: blueprint order 2124, proof step 4; Stacks 08JB
(blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionTensorIso {W Y : Scheme.{u}} (j : W ⟶ Y)
    (K L : DerivedCategoryModule Λ Y) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) W).obj
        ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj K)).obj
          ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj L) ≅
      (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj K).obj L) :=
  ((derivedTensor (ModuleCat.{u + 1} Λ) W).mapIso
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app K).symm).app
      ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj L) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) W).obj _).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app L).symm ≪≫
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) j K L).symm ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app _

/-- The canonical evaluation-transpose map into the double dual for any ambient object.
Source: blueprint order 2124, lem-weil-duality-pairing; Stacks 08J9
(blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionMap {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (Ω K : DerivedCategoryModule Λ Y) :
    K ⟶ (dualityDoubleFunctor (derivedHom (ModuleCat.{u + 1} Λ) Y) Ω).obj K :=
  restrictionDualDelta (derivedTensor (ModuleCat.{u + 1} Λ) Y)
    (derivedHom (ModuleCat.{u + 1} Λ) Y)
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ))
    (fun K L ↦ ((deltaRestrictionBraiding Λ aY).app K).app L) Ω K

/-- The dualizing comparison is the unique, counit-normalized adjoint-locality isomorphism
at the constant coefficient object. The Noetherian and compactification conditions are
consequences of the stated finite-type hypotheses, rather than additional assumptions.
Source: blueprint order 2124, proof step 1, lem-amb-etale-adjoint-locality
(blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionDualizingIso {k : Type u} [Field k]
    {W Y : Scheme.{u}} (j : W ⟶ Y) (aY : Y ⟶ Spec (.of k)) [Etale j]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated (j ≫ aY)] [LocallyOfFiniteType (j ≫ aY)] [QuasiCompact (j ≫ aY)] :
    (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
        (dualizingComplex (ModuleCat.{u + 1} Λ) aY) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) (j ≫ aY) :=
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  letI : IsNoetherian Y := ⟨⟩
  letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (j ≫ aY)
  letI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (j ≫ aY)
  letI : IsNoetherian W := ⟨⟩
  letI : IsSeparated j := IsSeparated.of_comp j aY
  (Classical.choose (existsUnique_etaleAmbientAdjointLocalityIso Λ j aY
    (HasCompactification.compactification aY)
    (HasCompactification.compactification (j ≫ aY))
    (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) aY)
    (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) (j ≫ aY))
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) aY)
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (j ≫ aY)))).app
      (constantComplex Λ (Spec (.of k)))

/-- Etale restriction commutes with the evaluation-transpose double-dual morphism,
including the canonical natural comparison and its variance.
Source: blueprint order 2124; Stacks 08J9 and 08JB
(blueprint: lem-weil-delta-restriction).

Proof:
1. Spec k is Noetherian and quasi-compact quasi-separated. Finite type makes Y and W
   Noetherian. Nagata compactifies their structure morphisms, and
   thm-amb-etale-exceptional-adjoint supplies their ordinary ambient right adjoints.
   Separated cancellation and Noetherian quasi-compactness give the hypotheses of
   lem-amb-etale-adjoint-locality, whose unique normalized comparison gives theta.
2. The etale slice is W_et by lem-weil-pbc-etale-site-localization-open; inverse image
   is restriction by lem-weil-pbc-etale-inverse-image-restriction. This identification
   respects the constant coefficient ring. Restriction and its sum-extension left
   adjoint are exact by lem-pur-site-restriction-module-adjunction-exact.
3. Apply lem-weil-pbc-ringed-internal-hom-exact-restriction and postcompose by theta.
   This supplies alpha naturally for every unbounded K, without perfectness assumptions.
4. Choose a K-flat flat-term P for K (lem-pc-kflat-resolution) and a K-injective I for
   omega (prop-pur-kinjective-resolutions-exist). Restriction preserves these properties
   by lem-weil-pbc-ringed-pullback-preserves-kflat and lem-pur-kinjective-restrict-localized.
   Both restricted Hom complexes have differential df=d_I f-(-1)^deg(f) f d_P.
   Slice tensor and direct-sum totalization commute with restriction, and both evaluations
   send h tensor p to h(p). This is exactly the normalization asserted for alpha.
5. Transpose evaluation using lem-weil-duality-pairing. On homogeneous p,h the double-dual
   map is p maps to (h maps to (-1)^(deg(p)deg(h)) h(p)). Restriction preserves this sign,
   application, and tensor symmetry. Both sides of the displayed identity have transpose
   theta composed with restricted evaluation and symmetry, so adjunction injectivity
   proves equality. Invert the contravariant alpha comparison for the transported form.
-/
theorem delta_restriction {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {W Y : Scheme.{u}} (j : W ⟶ Y) (aY : Y ⟶ Spec (.of k)) [Etale j]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated (j ≫ aY)] [LocallyOfFiniteType (j ≫ aY)] [QuasiCompact (j ≫ aY)] :
    DualDeltaRestriction (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory
      (derivedTensor (ModuleCat.{u + 1} Λ) Y) (derivedHom (ModuleCat.{u + 1} Λ) Y)
      (derivedTensor (ModuleCat.{u + 1} Λ) W) (derivedHom (ModuleCat.{u + 1} Λ) W)
      (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ))
      (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ))
      (fun K L ↦ ((deltaRestrictionBraiding Λ aY).app K).app L)
      (fun K L ↦ ((deltaRestrictionBraiding Λ (j ≫ aY)).app K).app L)
      (deltaRestrictionTensorIso Λ j)
      (dualizingComplex (ModuleCat.{u + 1} Λ) aY)
      (dualizingComplex (ModuleCat.{u + 1} Λ) (j ≫ aY))
      (deltaRestrictionDualizingIso Λ j aY) := by
  sorry

/-- The double-dual map is an isomorphism precisely when the corresponding double-dual
maps on a jointly surjective etale covering are isomorphisms, including an empty covering.
Source: blueprint order 2124, locality assertion
(blueprint: lem-weil-delta-restriction).

Proof:
1. Exact restriction commutes with cohomology sheaves in every integer degree.
2. Use lem-weil-pbc-etale-cover-detects-iso on the underlying abelian sheaves. The inverse
   of an invertible A-linear map is A-linear, so forgetting coefficients reflects isomorphisms.
3. The unbounded criterion lem-weil-pbc-unbounded-derived-iso-cohomology detects derived
   isomorphisms. Apply it to delta and use delta_restriction to identify its restrictions.
4. For an empty covering joint surjectivity forces Y to be empty; its module category is
   zero, so the criterion still holds. No boundedness hypothesis occurs.
-/
theorem isIso_delta_iff_etale_cover {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    {I : Type w} (W : I → Scheme.{u}) (j : ∀ i : I, W i ⟶ Y) [∀ i : I, Etale (j i)]
    [∀ i : I, IsSeparated (j i ≫ aY)] [∀ i : I, LocallyOfFiniteType (j i ≫ aY)]
    [∀ i : I, QuasiCompact (j i ≫ aY)]
    (hj : ∀ y : Y, ∃ (i : I) (x : W i), (j i).base x = y)
    (K : DerivedCategoryModule Λ Y) :
    IsIso (deltaRestrictionMap Λ aY (dualizingComplex (ModuleCat.{u + 1} Λ) aY) K) ↔
      ∀ i : I, IsIso (deltaRestrictionMap Λ (j i ≫ aY)
        (dualizingComplex (ModuleCat.{u + 1} Λ) (j i ≫ aY))
        ((upperStar (ModuleCat.{u + 1} Λ) (j i)).mapDerivedCategory.obj K)) := by
  sorry

end Etale

namespace ProEtale

/-- The existing native derived tensor, with its plain bifunctor signature exposed.
Source: blueprint order 2124, proof step 4 (blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionNativeTensor
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u}) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) :=
  MonoidalCategory.curriedTensor _

/-- The existing native derived internal Hom, with its plain bifunctor signature exposed.
Source: blueprint order 2124, proof step 4 (blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionNativeHom
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u}) :
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))ᵒᵖ ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) :=
  MonoidalClosed.internalHom

/-- The adjunction of the native tensor and internal Hom, without changing its unit or counit.
Source: blueprint order 2124, proof step 4 (blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionNativeAdjunction
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u}) (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (deltaRestrictionNativeTensor A Y).obj K ⊣
      (deltaRestrictionNativeHom A Y).obj (op K) :=
  MonoidalClosed.internalHomAdjunction₂.adj K


/-- Extract the Koszul braiding whose components the existing pairing assertion fixes.
The componentwise equality in that assertion determines the entire natural isomorphism.
Source: blueprint order 2124, evaluation restriction; Stacks 08J9
(blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionPairingBraiding
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u})
    (Ω : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (h : AmbientDualityPairing A Y Ω) :
    deltaRestrictionNativeTensor A Y ≅
      (deltaRestrictionNativeTensor A Y).flip :=
  Classical.choose h

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The unique descended Koszul braiding specified by the pro-etale pairing theorem.
Its componentwise normalization determines the selected natural isomorphism, independently
of Omega; it is not a choice of an arbitrary braiding.
Source: blueprint order 2124, lem-weil-duality-pairing; Stacks 06YU and 0FPT
(blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionBraiding {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (Ω : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    deltaRestrictionNativeTensor (ModuleCat.{u + 1} Λ) Y ≅
      (deltaRestrictionNativeTensor (ModuleCat.{u + 1} Λ) Y).flip :=
  deltaRestrictionPairingBraiding (ModuleCat.{u + 1} Λ) Y Ω
    ((Etale.ambient_duality_pairing Λ aY).2 Ω)

/-- The type of derived tensor comparisons for ordinary pro-etale inverse image.
Source: blueprint order 2124, proof step 4; Stacks 08JB
(blueprint: lem-weil-delta-restriction). -/
abbrev DeltaRestrictionTensorComparison
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {W Y : Scheme.{u}} (j : W ⟶ Y) :=
  Functor.curry.obj
      ((upperStar A j).mapDerivedCategory.prod
        (upperStar A j).mapDerivedCategory ⋙
          Functor.uncurry.obj (deltaRestrictionNativeTensor A W)) ≅
      Functor.curry.obj (Functor.uncurry.obj
        (deltaRestrictionNativeTensor A Y) ⋙
          (upperStar A j).mapDerivedCategory)

/-- The comparison square with the ordinary homotopy tensor map and localization.
It fixes the derived comparison on every K-flat model and hence everywhere.
Source: blueprint order 2124, proof step 4; Stacks 08JB
(blueprint: lem-weil-delta-restriction). -/
def IsNormalizedDeltaRestrictionTensor
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {W Y : Scheme.{u}} (j : W ⟶ Y)
    (e : DeltaRestrictionTensorComparison A j) : Prop :=
  ∀ P Q : HomotopyCategory
      (Sheaf (Scheme.ProEt.topology Y) A) (.up ℤ),
      (upperStar A j).mapDerivedCategory.map
          (Functor.LaxMonoidal.μ
            (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology Y) A)) P Q) ≫
        (upperStar A j).mapDerivedCategoryFactorsh.hom.app (P ⊗ Q) ≫
        (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology W) A)).map
          (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
            (upperStar A j)).app P).app Q) =
      (e.inv.app
        ((DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology Y)
          A)).obj P)).app
          ((DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology Y)
            A)).obj Q) ≫
        ((upperStar A j).mapDerivedCategoryFactorsh.hom.app P ⊗ₘ
          (upperStar A j).mapDerivedCategoryFactorsh.hom.app Q) ≫
        Functor.LaxMonoidal.μ
          (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology W) A))
          (((upperStar A j).mapHomotopyCategory (.up ℤ)).obj P)
          (((upperStar A j).mapHomotopyCategory (.up ℤ)).obj Q)

/-- The derived tensor comparison is fixed by the ordinary oplax tensor comparison
on every homotopy complex. This normalization determines the natural isomorphism uniquely.
Source: blueprint order 2124, final clause, proof step 4; Stacks 08JB
(blueprint: lem-weil-delta-restriction).

Proof: The exact inverse image is strong monoidal and preserves flat sheaves and
coproducts. Apply it to K-flat resolutions in both variables. The ordinary tensor
comparison is an isomorphism there and descends through the quasi-isomorphism
localizations. The ordinary comparison first descends to homotopy categories.
Its square with the localization lax tensor maps is the displayed
identity. Naturality and the essential surjectivity of K-flat localization determine
all its components, so the chosen data are uniquely normalized.
-/
theorem deltaRestrictionTensorComparison_normalized {W Y : Scheme.{u}} (j : W ⟶ Y) :
    ∃ e : DeltaRestrictionTensorComparison (ModuleCat.{u + 1} Λ) j,
      IsNormalizedDeltaRestrictionTensor (ModuleCat.{u + 1} Λ) j e := by
  sorry

/-- Canonical derived tensor comparison for ordinary constant-coefficient pro-etale sheaves.
The representative normalization above determines the selected data.
Source: blueprint order 2124, final clause; Stacks 08JB
(blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionTensorIso {W Y : Scheme.{u}} (j : W ⟶ Y)
    (K L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    ((deltaRestrictionNativeTensor (ModuleCat.{u + 1} Λ) W).obj
        ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj K)).obj
          ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj L) ≅
      (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
        (((deltaRestrictionNativeTensor (ModuleCat.{u + 1} Λ) Y).obj K).obj L) :=
  ((deltaRestrictionTensorComparison_normalized Λ j).choose.app K).app L

/-- The same restriction identity on the small pro-etale sites, for an arbitrary specified
ambient object Omega and its inverse image. This concerns ordinary module sheaves, with no
pro-etale exceptional-adjoint or condensed-coefficient assertion.
Source: blueprint order 2124, final clause; Stacks 08J9 and 08JB
(blueprint: lem-weil-delta-restriction).

Proof:
1. Etale j is weakly etale. Apply lem-weil-proetale-weakly-etale-localization to identify
   W_proet with the slice over W, including the constant coefficient ring.
2. Exact restriction and exact sum-extension are lem-pur-site-restriction-module-adjunction-exact.
   Apply lem-weil-pbc-ringed-internal-hom-exact-restriction with Omega_W = j*Omega_Y.
3. Repeat the K-flat/K-injective calculation in steps 4 and 5 of delta_restriction on
   this ringed slice. Evaluation still sends h tensor p to h(p) and transposition uses
   the same Koszul sign. Both transposes coincide, proving the identity and its transported
   form. It therefore applies to the specified compatible finite realization, without
   applying the etale ambient-adjoint theorem to a pro-etale category.
-/
theorem delta_restriction {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {W Y : Scheme.{u}} (j : W ⟶ Y) (aY : Y ⟶ Spec (.of k)) [Etale j]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated (j ≫ aY)] [LocallyOfFiniteType (j ≫ aY)] [QuasiCompact (j ≫ aY)]
    (Ω : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    DualDeltaRestriction (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory
      (deltaRestrictionNativeTensor (ModuleCat.{u + 1} Λ) Y)
      (deltaRestrictionNativeHom (ModuleCat.{u + 1} Λ) Y)
      (deltaRestrictionNativeTensor (ModuleCat.{u + 1} Λ) W)
      (deltaRestrictionNativeHom (ModuleCat.{u + 1} Λ) W)
      (deltaRestrictionNativeAdjunction (ModuleCat.{u + 1} Λ) Y)
      (deltaRestrictionNativeAdjunction (ModuleCat.{u + 1} Λ) W)
      (fun K L ↦ ((deltaRestrictionBraiding Λ aY Ω).app K).app L)
      (fun K L ↦ ((deltaRestrictionBraiding Λ (j ≫ aY)
        ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj Ω)).app K).app L)
      (deltaRestrictionTensorIso Λ j) Ω
      ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj Ω) (Iso.refl _) := by
  sorry

end ProEtale

end AlgebraicGeometry
