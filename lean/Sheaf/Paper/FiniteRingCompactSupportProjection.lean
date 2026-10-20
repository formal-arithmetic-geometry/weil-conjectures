/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.Paper.FiniteRingCompactSupportProjectionMap

public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.SixFunctors.IntrinsicDerivedTensor
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula
import Mathlib.GroupTheory.Torsion
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat

/-!
# Compact-support projection with arbitrary finite primary coefficients

Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-compatibilities.proof.md`, Proof (3); Stacks Project, Tag 0F0G
(blueprint: lem-sp-finite-ring-compact-support-projection).

The canonical coefficient realization changes only the presentation of module sheaves.
The projection arrow below is the published counit-defined compactification projection
transported by that realization, on the ordinary unbounded intrinsic derived categories.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

-- Use one ring structure in abstract coefficients and in their ULift specialization.
attribute [local instance 100001] CommRing.toRing

open scoped CategoryTheory.Functor


/-- Exact inverse image gives the same adjunction under either derived presentation.
The derived-unit factorization characterizes both units on the localization. -/
private theorem exactDerivedAdjunction
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D] [IsGrothendieckAbelian.{u + 1} C]
    [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G) :
    adj.derivedAdjunction.ofNatIsoLeft F.leftDerivedFunctorIsoMapDerivedCategory =
      adj.mapDerivedCategoryRightDerivedAdjunction := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ))
  intro K
  have h₁ := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ))
    F.leftDerivedFunctorCounit G.rightDerivedFunctorUnit K
  have h₂ := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ))
    F.mapDerivedCategoryFactorsh.hom G.rightDerivedFunctorUnit K
  simp only [Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app]
  apply (cancel_mono (G.rightDerivedFunctor.map
    (F.mapDerivedCategoryFactorsh.hom.app K))).1
  rw [Category.assoc, ← Functor.map_comp,
    Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac]
  exact h₁.trans h₂.symm

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unbounded comparison is the mate used by projection-formula transport,
conjugated by the canonical identifications of exact and left derived inverse images. -/
private theorem unboundedMateIdentification
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).leftDerivedFunctorIsoMapDerivedCategory.hom.app
          ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj E) ≫
      unboundedDirectImageComparisonMap A g E =
    (mateEquiv (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
      (leftDerivedComparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g).hom).app E ≫
      (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).leftDerivedFunctorIsoMapDerivedCategory
          |>.hom.app E) := by
  let C := ModuleCat.{u + 1} A
  let adjP := derivedUpperStarLowerStarAdjunction C g
  unfold unboundedDirectImageComparisonMap
  rw [← exactDerivedAdjunction (upperStarLowerStarAdjunction C g),
    ← exactDerivedAdjunction (Etale.upperStarLowerStarAdjunction C g),
    Adjunction.homEquiv_ofNatIsoLeft_apply]
  apply (adjP.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm]
  dsimp only [adjP, derivedUpperStarLowerStarAdjunction]
  rw [Equiv.symm_apply_apply]
  rw [Adjunction.homEquiv_counit, mateEquiv_counit]
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  simp only [leftDerivedComparisonUpperStarCompUpperStarIso,
    Functor.leftDerivedFunctorCompNatIso, Functor.leftDerivedFunctorCompIso,
    Functor.leftDerivedFunctorNatIso, unboundedDirectImagePullbackIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  simp only [Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [← NatTrans.naturality_assoc
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).leftDerivedFunctorIsoMapDerivedCategory.inv]
  simp only [Functor.id_obj, Iso.inv_hom_id_app, Category.comp_id, Iso.symm_inv]
  rw [(upperStar C g).leftDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Invertibility of the canonical unbounded comparison implies invertibility of its mate. -/
private theorem unboundedMateIsIso
    (A : Type (u + 1)) [CommRing A] {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (V : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    [IsIso (unboundedDirectImageComparisonMap A g V)] :
    IsIso ((mateEquiv (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
      (leftDerivedComparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g).hom).app V) := by
  have h := unboundedMateIdentification A g V
  have hi : IsIso
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj V) ≫
        unboundedDirectImageComparisonMap A g V) := inferInstance
  have hj := Eq.mp (congrArg IsIso h) hi
  exact IsIso.of_isIso_comp_right
    ((mateEquiv (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
      (leftDerivedComparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g).hom).app V)
    ((lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).leftDerivedFunctorIsoMapDerivedCategory
        |>.hom.app V))

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

open Scheme

/-- The proper projection on etale origins, keeping the source coefficient category abstract.
This named proposition stores the native derived-category models of the source interfaces. -/
private noncomputable def properProjectionOnOrigins
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] [ProEtale.UpperStarPreservesFlat C]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (E : DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology C)) : Prop :=
  IsIso (((ProEtale.rightDerivedLowerStarProjectionMap C g).app
    ((ProEtale.comparisonUpperStar C Z).leftDerivedFunctor.obj E)).app
    ((ProEtale.comparisonUpperStar C Y).leftDerivedFunctor.obj K))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical proper projection is invertible on objects of etale origin.
The unbounded comparison is needed at both E and E tensor p*K. -/
private theorem properProjection_of_origin
    (k : Type u) [Field k] [IsAlgClosed k]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    {Z Y : Scheme.{u}}
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (g : Z ⟶ Y) [IsProper g]
    (E : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    properProjectionOnOrigins (ModuleCat.{u + 1} A) g E K := by
  unfold properProjectionOnOrigins
  have hb (V : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))) :
      IsIso ((mateEquiv (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
        (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
        (ProEtale.leftDerivedComparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} A) g).hom).app V) := by
    have := ProEtale.unboundedDirectImageComparison k (Or.inr inferInstance) hℓ A hA g V
    exact ProEtale.unboundedMateIsIso A g V
  have : ProEtale.UpperStarPreservesFlat (ModuleCat.{u + 1} A) :=
    ProEtale.upperStarPreservesFlat_moduleCat A
  have : Etale.UpperStarPreservesFlat (ModuleCat.{u + 1} A) :=
    Etale.upperStarPreservesFlat_moduleCat (Λ := A)
  have : ∀ T : Scheme.{u}, (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).PreservesFlat :=
    fun T ↦ ProEtale.preservesFlat_comparisonUpperStar (X := T) (Λ := A)
  have hPF := Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion
    A isAddTorsion_of_finite g E K
  dsimp only [Etale.rightDerivedLowerStarProjectionMap] at hPF
  have := hb E
  have := hb (((Etale.derivedTensor (ModuleCat.{u + 1} A) Z).obj E).obj
    ((Etale.upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))
  exact Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
    (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
    (ProEtale.comparisonCompatible_leftDerivedComparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} A) g)
    E K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The finite-field and primary-torsion assumptions give the proper projection formula
in lifted fixed scalar coefficients. This packages only the coefficient arithmetic. -/
private theorem finiteFieldProperProjection_of_origin
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) (hl : l.Prime) (hlp : l ≠ D.p)
    (R : Type u) [CommRing R] [Finite R]
    (n : ℕ) (hR : ∀ r : R, (l ^ n) • r = 0)
    {Z Y : Scheme.{u}}
    [Z.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (g : Z ⟶ Y) [IsProper g]
    (E : DerivedCategory
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R))))
    (K : DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R)))) :
    properProjectionOnOrigins
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) g E K := by
  classical
  let : Fact l.Prime := ⟨hl⟩
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : Fintype D.k₀ := Fintype.ofFinite _
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have hlunit : IsUnit (algebraMap ℤ D.k (l : ℤ)) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime D.k hl hlp.symm))
  have hA : ∃ m : ℕ, (l : ULift.{u + 1, u} R) ^ m = 0 := by
    refine ⟨n, ?_⟩
    apply (ULift.ringEquiv : ULift.{u + 1, u} R ≃+* R).injective
    simpa only [map_pow, map_natCast, map_zero, nsmul_eq_mul, mul_one,
      Nat.cast_pow] using hR 1
  exact properProjection_of_origin D.k hlunit (ULift.{u + 1, u} R) hA g E K

/-- Etale origins suffice for the fixed-coefficient compactification projection. -/
private theorem fixedProjection_of_origins
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    [Etale.UpperStarPreservesFlat C] [ProEtale.UpperStarPreservesFlat C]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    (E₀ : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (Q₀ : DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (Mf : DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (Kf : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C))
    (eM₀ : (ProEtale.comparisonUpperStar C X).mapDerivedCategory.obj E₀ ≅ Mf)
    (eK₀ : (ProEtale.comparisonUpperStar C Y).mapDerivedCategory.obj Q₀ ≅ Kf)
    [IsIso (((ProEtale.rightDerivedLowerStarProjectionMap C c.g).app
      ((ProEtale.comparisonUpperStar C c.Z).leftDerivedFunctor.obj
        ((Etale.openImmersionLowerShriek C c.i).mapDerivedCategory.obj E₀))).app
      ((ProEtale.comparisonUpperStar C Y).leftDerivedFunctor.obj Q₀))] :
    IsIso (((ProEtale.projectionMapOfCompactification C c).app Mf).app Kf) := by
  let E := (Etale.openImmersionLowerShriek C c.i).mapDerivedCategory.obj E₀
  let eE : (ProEtale.openImmersionLowerShriek C c.i).mapDerivedCategory.obj Mf ≅
      (ProEtale.comparisonUpperStar C c.Z).leftDerivedFunctor.obj E :=
    (ProEtale.openImmersionLowerShriek C c.i).mapDerivedCategory.mapIso eM₀.symm ≪≫
      ((Functor.mapDerivedCategoryCompIso (ProEtale.comparisonUpperStar C X)
        (ProEtale.openImmersionLowerShriek C c.i)).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (ProEtale.openImmersionLowerShriekComparisonUpperStarIso C c.i).symm ≪≫
        Functor.mapDerivedCategoryCompIso (Etale.openImmersionLowerShriek C c.i)
          (ProEtale.comparisonUpperStar C c.Z)).app E₀ ≪≫
      ((ProEtale.comparisonUpperStar C c.Z).leftDerivedFunctorIsoMapDerivedCategory.app E).symm
  let eK := eK₀.symm ≪≫
    ((ProEtale.comparisonUpperStar C Y).leftDerivedFunctorIsoMapDerivedCategory.app Q₀).symm
  have := NatTrans.isIso_app_app_of_iso
    (ProEtale.rightDerivedLowerStarProjectionMap C c.g) eE.symm eK.symm
  rw [ProEtale.projectionMapOfCompactification_app_app]
  infer_instance

attribute [local instance 100000] AlgebraicGeometry.Scheme.sfFixedSheafAbelian
attribute [local instance 100000] AlgebraicGeometry.Scheme.sfFixedDerivedCategoryModel

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Specialize categorical assembly while keeping the scalar ring abstract. -/
private theorem moduleProjection_of_origins
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    (E₀ : ProEtale.FiniteCoefficientEtaleDerivedCategory X A)
    (Q₀ : ProEtale.FiniteCoefficientEtaleDerivedCategory Y A)
    (Mf : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (Kf : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (eM₀ : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj E₀ ≅ Mf)
    (eK₀ : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj Q₀ ≅ Kf)
    (hPF : properProjectionOnOrigins (ModuleCat.{u + 1} A) c.g
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj E₀)
      Q₀) :
    IsIso (((Scheme.sfFixedCompactificationProjection A c).app Mf).app Kf) := by
  unfold properProjectionOnOrigins at hPF
  have := hPF
  have he : Scheme.sfFixedCompactificationProjection A c =
      ProEtale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c := rfl
  have h := fixedProjection_of_origins (ModuleCat.{u + 1} A) f c E₀ Q₀ Mf Kf eM₀ eK₀
  exact (congrArg (fun τ ↦ IsIso ((τ.app Mf).app Kf)) he).mpr h

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance 100000] AlgebraicGeometry.Scheme.sfFixedSheafAbelian
attribute [local instance 100000] AlgebraicGeometry.Scheme.sfFixedDerivedCategoryModel

/-- Transfer an intrinsic etale-origin isomorphism to fixed scalar coefficients. -/
@[irreducible] private noncomputable def fixedOriginIso
    (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R]
    (E : ProEtale.FiniteCoefficientEtaleDerivedCategory T (ULift.{u + 1, u} R))
    (M : proEtaleDerivedCategory T R)
    (e : (ProEtale.finiteCoefficientIntrinsicDerivedComparison T R).obj E ≅ M) :
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) T).mapDerivedCategory.obj E ≅
        (sfIntrinsicDerivedModuleEquivalence T R).inverse.obj M :=
  (sfIntrinsicDerivedModuleEquivalence T R).functor.preimageIso
    (((Functor.mapDerivedCategoryCompIso
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) T)
      (ProEtale.finiteCoefficientIntrinsicRealization T R)).app E).symm ≪≫ e ≪≫
        ((sfIntrinsicDerivedModuleEquivalence T R).counitIso.app M).symm)

/-- Constructible intrinsic complexes have etale origins in the fixed-scalar presentation.
This is the essential-image assertion of the existing origin theorem, followed by the
canonical realization equivalence. -/
private theorem fixedCoefficientOrigin
    (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R]
    (M : proEtaleDerivedCategory T R)
    (hc : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T R
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T R)) i).obj M))
    (hb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T R)) i).obj M)) :
    ∃ E : ProEtale.FiniteCoefficientEtaleDerivedCategory T (ULift.{u + 1, u} R),
      Nonempty ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) T).mapDerivedCategory.obj E ≅
          (sfIntrinsicDerivedModuleEquivalence T R).inverse.obj M) := by
  obtain ⟨E, ⟨e⟩⟩ := ((finiteRing_constructibleDerived_origin T R).2.2.1 M).2 ⟨hc, hb⟩
  exact ⟨E.obj, ⟨fixedOriginIso T R E.obj M e⟩⟩

/-- The specified intrinsic arrow is the image of the fixed-coefficient arrow. -/
private theorem intrinsicProjection_of_fixed
    (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : proEtaleDerivedCategory X R) (K : proEtaleDerivedCategory Y R)
    (hPF : IsIso (((sfFixedCompactificationProjection (ULift.{u + 1, u} R) c).app
      ((sfIntrinsicDerivedModuleEquivalence X R).inverse.obj M)).app
      ((sfIntrinsicDerivedModuleEquivalence Y R).inverse.obj K))) :
    IsIso (((finiteRingCompactSupportProjection R c).app M).app K) := by
  have he : finiteRingCompactSupportProjection R c =
      sfRealizeCompactificationProjection
        (sfIntrinsicDerivedModuleEquivalence X R).inverse
        (sfIntrinsicDerivedModuleEquivalence Y R).inverse
        (sfIntrinsicDerivedModuleEquivalence Y R).functor
        (sfFixedCompactificationProjection (ULift.{u + 1, u} R) c) := rfl
  have h := isIso_sfRealizeCompactificationProjection_app_app
    (sfIntrinsicDerivedModuleEquivalence X R).inverse
    (sfIntrinsicDerivedModuleEquivalence Y R).inverse
    (sfIntrinsicDerivedModuleEquivalence Y R).functor
    (sfFixedCompactificationProjection (ULift.{u + 1, u} R) c) M K
  exact (congrArg (fun τ ↦ IsIso ((τ.app M).app K)) he).mpr h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical compact-support projection is invertible for bounded intrinsically
constructible complexes over every finite primary commutative ring. A compactification
records exactly `j = c.i`, `p = c.g`, `Xbar = c.Z`, and `f = j ≫ p` by `c.comm`.
The coefficient realization is the canonical extension of fixed scalar actions to
locally constant scalar sections; it changes no objects or morphisms mathematically.
Naturality in `M,K` comes from `projectionMapOfCompactification`, a transformation of
bifunctors, and the functors used to transport it.
Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-compatibilities.proof.md`, Proof (3); Stacks Tag 0F0G
(blueprint: lem-sp-finite-ring-compact-support-projection).

Proof (the node's six steps):
1. By lem-weil-pbc-finite-ring-constructible-derived-origin, choose bounded
   constructible etale origins M0,K0 for M,K, using intrinsic constructibility over
   the given finite ring. No finite Tor amplitude or DVR presentation is required.
2. Put E = j! M0. The exact etale and pro-etale extensions by zero act degreewise
   (lem-weil-pbc-extension-by-zero-exact, lem-cbc-proetale-extension-zero).
   Apply lem-cbc-proetale-extension-zero-comparison in each degree; exactness
   descends it and its inverse to identify the pro-etale realization of E with j! M.
3. Work in the fixed-scalar presentation used by the specified projection map.
   The source-library comparisonCompatible_leftDerivedComparisonUpperStarCompUpperStarIso
   identifies the canonical tensor comparisons through the etale/pro-etale pullback square,
   on all unbounded complexes. Put H = E tensor-derived p* K0.
4. Stacks 0F0G (lem-kun-0f0g) makes the etale proper projection invertible; the finite
   coefficient ring is torsion. Apply lem-sfb-unbounded-direct-image-comparison to E and H.
   The hypotheses follow from the finite-field datum and properness of p. The comparison
   therefore applies even if H is unbounded below.
5. The private helper unboundedMateIdentification identifies these comparisons with the
   mates used by Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv. Apply that theorem
   with the tensor compatibility in Step 3. Naturality and the isomorphisms in Steps 1 and 2
   give invertibility of the actual proper projection at (j!M,K).
6. lem-cbc-extension-zero-projection-formula makes the canonical open factor
   invertible on unbounded categories. Proper pushforward preserves its inverse.
   Compose with step 5 and the pullback-composition isomorphism. Every factor
   is natural in both inputs, so the specified composite is natural as well. -/
theorem isIso_finiteRingCompactSupportProjection
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) (_hl : l.Prime) (_hlp : l ≠ D.p)
    (R : Type u) [CommRing R] [Finite R]
    (n : ℕ) (_hn : 1 ≤ n) (_hR : ∀ r : R, (l ^ n) • r = 0)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) (c : Compactification f)
    [c.Z.Over (Spec (.of D.k))]
    [IsSeparated (c.Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of D.k))]
    [QuasiCompact (c.Z ↘ Spec (.of D.k))]
    [c.i.IsOver (Spec (.of D.k))] [c.g.IsOver (Spec (.of D.k))]
    (M : proEtaleDerivedCategory X R) (K : proEtaleDerivedCategory Y R)
    (_hMc : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X R
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X R)) i).obj M))
    (_hMb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X R)) i).obj M))
    (_hKc : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y R
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y R)) i).obj K))
    (_hKb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y R)) i).obj K)) :
    IsIso (((finiteRingCompactSupportProjection R c).app M).app K) := by
  classical
  have hM := fixedCoefficientOrigin X R M _hMc _hMb
  have hK := fixedCoefficientOrigin Y R K _hKc _hKb
  -- Keep these arguments explicit: aliases make conversion unfold derived constructions.
  have hp := finiteFieldProperProjection_of_origin D l _hl _hlp R n _hR c.g
    ((Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c.i).mapDerivedCategory.obj hM.choose) hK.choose
  have hc : IsIso (((sfFixedCompactificationProjection (ULift.{u + 1, u} R) c).app
      ((sfIntrinsicDerivedModuleEquivalence X R).inverse.obj M)).app
      ((sfIntrinsicDerivedModuleEquivalence Y R).inverse.obj K)) :=
    moduleProjection_of_origins (ULift.{u + 1, u} R) f c hM.choose hK.choose
      ((sfIntrinsicDerivedModuleEquivalence X R).inverse.obj M)
      ((sfIntrinsicDerivedModuleEquivalence Y R).inverse.obj K)
      (Classical.choice hM.choose_spec) (Classical.choice hK.choose_spec) hp
  exact intrinsicProjection_of_fixed R c M K hc

end AlgebraicGeometry.Scheme
