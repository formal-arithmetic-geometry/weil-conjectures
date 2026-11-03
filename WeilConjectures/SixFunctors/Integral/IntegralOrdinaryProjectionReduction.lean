/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.SixFunctors.Integral.IntegralOrdinaryProjectionArrowComparison
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Reduction of the ordinary completed-coefficient projection

Source: blueprint sk-thm-sf-pf-adic, Steps 1--3, and sk-thm-sf-pf-proetale,
integral paragraph (blueprint: lem-sf-ordinary-projection-finite-reductions).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasProEtaleTorAmplitude
  ProEtale.projectionMapOfCompactification ProEtale.derivedTensorRightDerivedLowerShriek
attribute [local instance 100000] SheafOfModules.instAbelian

attribute [local instance 2000] CommRing.toRing isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat finiteProjection_upperFlat

private theorem fixed_constructible
    (A : Type u) [CommRing A] [Finite A] (W : Scheme.{u})
    (K : proEtaleDerivedCategory W A)
    (hc : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf W A
      ((DerivedCategory.homologyFunctor _ i).obj K))
    (a b : ℤ) (hab : a ≤ b)
    (hv : ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) :
    ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) W
      ((sfIntrinsicDerivedEquivalence W A).inverse.obj K) := by
  obtain ⟨M, ⟨eM⟩⟩ := ((finiteRing_constructibleDerived_origin W A).2.2.1 K).mpr
    ⟨hc, a, b, hab, hv⟩
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) W
  let G := ProEtale.finiteCoefficientIntrinsicRealization W A
  let R := sfIntrinsicDerivedEquivalence W A
  let ecomp : ProEtale.finiteCoefficientIntrinsicDerivedComparison W A ≅
      F.mapDerivedCategory.{u + 1, u + 1} ⋙ R.functor :=
    Functor.mapDerivedCategoryCompIso F G
  let e : F.mapDerivedCategory.{u + 1, u + 1}.obj M.obj ≅ R.inverse.obj K :=
    R.unitIso.app _ ≪≫ R.inverse.mapIso
      (ecomp.symm.app M.obj ≪≫ eM)
  have hb : DerivedCategory.TStructure.t.bounded M.obj := by
    obtain ⟨r, s, _, hz⟩ := M.property.2
    exact ⟨⟨r, (DerivedCategory.isGE_iff _ r).mpr (fun i hi ↦ hz i (.inl hi))⟩,
      ⟨s, (DerivedCategory.isLE_iff _ s).mpr (fun i hi ↦ hz i (.inr hi))⟩⟩
  apply (ProEtale.DerivedCategory.boundedConstructible_iff _ _ _).mpr
  exact ⟨M.obj, ⟨hb, fun i ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
    (M.property.1 i)⟩, ⟨e⟩⟩

attribute [local irreducible] sfIntrinsicModuleEquivalence

private theorem fixed_tor
    (A : Type u) [CommRing A] [Finite A] (W : Scheme.{u})
    (K : proEtaleDerivedCategory W A) (a b : ℤ)
    (ht : HasProEtaleTorAmplitude W A K a b) :
    ProEtale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) W a b
      ((sfIntrinsicDerivedEquivalence W A).inverse.obj K) := by
  let R := sfIntrinsicModuleEquivalence W A
  have hab : a ≤ b := by
    unfold HasProEtaleTorAmplitude at ht
    exact ht.1
  have ht' : HasProEtaleTorAmplitude W A
      (R.functor.mapDerivedCategory.obj (R.inverse.mapDerivedCategory.obj K)) a b := by
    unfold HasProEtaleTorAmplitude at ht ⊢
    refine ⟨ht.1, ?_⟩
    intro B P hB v hv hP M i hi
    exact ht.2 B P (hB.map (fun z ↦ z ≪≫ R.mapDerivedCategory.counitIso.app K))
      v hv hP M i hi
  have h := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    A W a b hab (R.inverse.mapDerivedCategory.obj K)).mp
      (by simpa only [R, sfIntrinsicModuleEquivalence, Functor.asEquivalence_functor] using ht')
  exact h

attribute [local irreducible] sfIntrinsicDerivedEquivalence
  scalarReductionDerivedExtension PurCompactSupport.projectionMap
private theorem integral_origin
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u}) (M : sfIntegralConstructibleCategory l E W) (n : ℕ)
    [Finite (Padic.coefficientExtensionRing l E (n + 1))] :
    ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) W
      ((sfIntrinsicDerivedEquivalence W (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj
        ((scalarReductionDerivedExtension l E W n).obj M.obj)) := by
  obtain ⟨_, r, s, hrs, hlevels⟩ := M.property
  apply fixed_constructible (Padic.coefficientExtensionRing l E (n + 1)) W _
    (hlevels n).1.2 r s hrs
  intro i hi
  by_contra hz
  have hb := (hlevels n).2 hz
  have hri : r ≤ i := hb.1
  have his : i ≤ s := hb.2
  omega

-- Keep the local instances inline for kernel comparison of the coefficient categories.
set_option linter.style.haveILetI false in
private theorem integral_tor
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
    (L : sfIntegralConstructibleCategory l E Y) (n : ℕ) :
    ∃ a b : ℤ, HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension l E Y n).obj L.obj) a b := by
  have hbase : IsUnit (l : D.k) := by
    letI : Fintype D.k₀ := Fintype.ofFinite _
    letI : Fact D.p.Prime := ⟨D.prime⟩
    haveI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
      rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
    haveI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
    exact isUnit_iff_ne_zero.mpr
      (CharP.cast_ne_zero_of_ne_of_prime _ (Fact.out : l.Prime) hl.symm)
  letI : ∀ y : Y, Invertible (l : Y.residueField y) := fun y ↦
    (show IsUnit (l : Y.residueField y) from by
      simpa only [map_natCast] using
        hbase.map ((Y ↘ Spec (.of D.k)).residueFieldAlgebraMap y)).invertible
  have hL : finiteTorConstructibleIntegral l E Y L.obj :=
    Eq.mp (congrFun (integral_residue_tor D l hl E Y).2 L.obj) L.property
  obtain ⟨a, b, _, ht⟩ := hL.2
  exact ⟨a, b, ht n⟩

private theorem projection_iso_of_property
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A))
    (h : ProEtale.HasProjectionFormulaOfCompactification A c K L) :
    IsIso (((ProEtale.projectionMapOfCompactification A c).app K).app L) := h

set_option linter.style.haveILetI false in
private theorem map_isIso_of_proof
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {M N : C} (f : M ⟶ N) (hf : IsIso f) : IsIso (F.map f) := by
  letI := hf
  exact F.map_isIso f

private theorem fixed_projection
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) (L : proEtaleDerivedCategory Y A)
    (hK : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
      ((sfIntrinsicDerivedEquivalence X A).inverse.obj K))
    (hL : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y
      ((sfIntrinsicDerivedEquivalence Y A).inverse.obj L))
    (a b : ℤ) (ht : ProEtale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y a b
      ((sfIntrinsicDerivedEquivalence Y A).inverse.obj L)) :
    IsIso ((sfIntrinsicDerivedEquivalence Y A).functor.map
      (((ProEtale.projectionMapOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app
          ((sfIntrinsicDerivedEquivalence X A).inverse.obj K)).app
          ((sfIntrinsicDerivedEquivalence Y A).inverse.obj L))) := by
  have hpf := ProEtale.hasProjectionFormulaOfCompactification_of_boundedConstructible
    (ULift.{u + 1, u} A) c hK ⟨hL, a, b, ht⟩
  exact map_isIso_of_proof (sfIntrinsicDerivedEquivalence Y A).functor _
    (projection_iso_of_property _ c _ _ hpf)

private theorem finite_projection_on_reductions
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
    {f : X ⟶ Y} (c : Compactification f)
    (K : sfIntegralConstructibleCategory l E X)
    (L : sfIntegralConstructibleCategory l E Y) (n : ℕ)
    [Finite (Padic.coefficientExtensionRing l E (n + 1))] :
    IsIso ((sfIntrinsicDerivedEquivalence Y
        (Padic.coefficientExtensionRing l E (n + 1))).functor.map
      (((ProEtale.projectionMapOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1)))) c).app
          ((sfIntrinsicDerivedEquivalence X
            (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj
            ((scalarReductionDerivedExtension l E X n).obj K.obj))).app
          ((sfIntrinsicDerivedEquivalence Y
            (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj
            ((scalarReductionDerivedExtension l E Y n).obj L.obj)))) := by
  obtain ⟨a, b, ht⟩ := integral_tor D l hl E Y L n
  exact fixed_projection (Padic.coefficientExtensionRing l E (n + 1)) c _ _
    (integral_origin l E X K n) (integral_origin l E Y L n) a b
    (fixed_tor (Padic.coefficientExtensionRing l E (n + 1)) Y _ a b ht)

set_option linter.style.haveILetI false in
private theorem isIso_of_arrow_iso
    {C : Type*} [Category C] {X Y X' Y' : C}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk g) (h : IsIso g) :
    IsIso f := by
  letI := h
  exact (Arrow.isIso_iff_isIso_of_isIso e.hom).mpr (by infer_instance)

attribute [local instance 100000] HasDerivedCategory.standard

-- These inline instance bindings avoid the kernel-normalization regression noted above.
set_option linter.style.haveILetI false in
/-- Every finite reduction of the specified ordinary projection is invertible.
This asserts nothing about the integral arrow before reduction.
Source: current blueprint sk-thm-sf-pf-adic, Steps 1--2; Stacks 099N
(blueprint: lem-sf-ordinary-projection-finite-reductions).

Proof: the residue-Tor theorem gives a uniform Tor interval for each integral
constructible input. At each positive quotient their constructible reductions
admit bounded constructible etale origins. Comparison reflects the second input's
Tor interval. The finite compact-support projection formula makes its projection
invertible. Reduce the proper-counit/open-extension composite defining the ordinary
integral projection. Normalized scalar tensor, pullback and compact-support
comparisons identify its source and target with those of that finite projection.
The proper square is the counit-mate tensor square; restriction of the open square
is the same tensor identity, so full faithfulness of open extension proves it.
Paste the squares. Thus the reduced ordinary arrow is conjugate to the finite
projection by invertible endpoint comparisons. The representative identifications
of each supplied tensor model ensure this holds for every such model. Empty schemes,
zero inputs and exponent one use these same equations. No separated structure
morphisms on X or Y, and no discrete integral etale realization, are required. -/
theorem integralOrdinaryProjection_finiteReductions
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
    (aX : ProEtaleTensorModel X ((PurCompactSupport.completed l E).ring X))
    (aZ : ProEtaleTensorModel c.Z ((PurCompactSupport.completed l E).ring c.Z))
    (aY : ProEtaleTensorModel Y ((PurCompactSupport.completed l E).ring Y))
    (K : sfIntegralConstructibleCategory l E X)
    (L : sfIntegralConstructibleCategory l E Y) (n : ℕ) :
    IsIso ((scalarReductionDerivedExtension l E Y n).map
      (((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c aX aZ aY
        (PurCompactSupport.completedPull_comp l E c.i c.g)).app K.obj).app L.obj)) := by
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  obtain ⟨e⟩ := integralOrdinaryProjection_reduction_arrowComparison l E c aX aZ aY
    K.obj L.obj n
  exact isIso_of_arrow_iso e (finite_projection_on_reductions D l hl E c K L n)

end WeilConjectures
