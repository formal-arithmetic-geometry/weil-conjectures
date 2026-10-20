/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import Sheaf.Paper.CompletedTowerDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import all Sheaf.Paper.ProperDirectImageFiniteness
import all Sheaf.Paper.RestrictionDirectImage
import all Sheaf.Paper.ConstructibleCoefficientSerre
import Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import all Sheaf.AlgebraicGeometry.ProEtaleOperations

/-! # Proper finite-coefficient direct image on intrinsic cohomology
Source: preservation proof, finite-level finiteness step; Stacks Tags 095U, 0GL0 and 09AL
(blueprint: lem-weil-pbc-finite-direct-image-cohomology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

open ProEtale

private def reductionEncoding (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :=
  pbcRestrict (pbcLevelConstantComparison T d n).hom ⋙
    CoefficientSerre.proEtaleModuleRestriction T (A ⧸ d.ideal ^ (n + 1))

private instance encoding_equivalence (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) : (reductionEncoding T d n).IsEquivalence := by
  let e := (adicLisseForget T).mapIso (pbcLevelConstantComparison T d n)
  have : (pbcRestrict (pbcLevelConstantComparison T d n).hom).IsEquivalence :=
    inferInstanceAs (proEtaleScalarEquivalence T e).functor.IsEquivalence
  dsimp [reductionEncoding]
  infer_instance

private instance encoding_additive (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) : (reductionEncoding T d n).Additive := by
  dsimp [reductionEncoding]
  infer_instance

private def reductionDirectImageEncoding {S T : Scheme.{u}} (f : S ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    completedFiniteModuleDirectImage f d n ⋙ reductionEncoding T d n ≅
      reductionEncoding S d n ⋙ lowerStar (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1))) f := by
  let B := A ⧸ d.ideal ^ (n + 1)
  let c := CoefficientSerre.coefficientIso f B
  have hs : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
      (pbcLevelConstantComparison T d n).hom ≫ completedFiniteCoefficientMap f d n =
        c.hom ≫ (pbcLevelConstantComparison S d n).hom := by
    simp only [completedFiniteCoefficientMap, ← Functor.map_comp_assoc,
      Iso.hom_inv_id]
    rw [(proEtaleSheafInverseImage f CommRingCat.{u + 1}).map_id, Category.id_comp]
    rfl
  let e := (proEtaleRingRestrictionDirectImage_existsUnique f
    (adicLisseConstantRing T B) ((pbcAdicRings T d).obj (op n))
    (adicLisseConstantRing S B) ((pbcAdicRings S d).obj (op n))
    (pbcLevelConstantComparison T d n).hom (pbcLevelConstantComparison S d n).hom
    c (asIso (completedFiniteCoefficientMap f d n)) hs.symm).exists.choose
  exact (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e _ ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (CoefficientSerre.directImageComparison f B) ≪≫
        (Functor.associator _ _ _).symm

private def reductionDerivedDirectImageEncoding {S T : Scheme.{u}} (f : S ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    completedFiniteDerivedDirectImage f d n ⋙ (reductionEncoding T d n).mapDerivedCategory ≅
      (reductionEncoding S d n).mapDerivedCategory ⋙
        (lowerStar (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1))) f).rightDerivedFunctor := by
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (reductionDirectImageEncoding f d n) ≪≫
      Functor.rightDerivedFunctorCompIso _ _ ≪≫
        Functor.isoWhiskerRight
          (reductionEncoding S d n).rightDerivedFunctorIsoMapDerivedCategory _

private theorem fixedDirectImage
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (hDimS : ∃ k : ℕ, topologicalKrullDim S ≤ (k : WithBot ℕ∞))
    (hDimT : ∃ k : ℕ, topologicalKrullDim T ≤ (k : WithBot ℕ∞))
    (f : S ⟶ T) [IsProper f] (B : Type (u + 1)) [CommRing B] [Finite B]
    (horder : ∀ (x : B) (t : T), IsUnit (addOrderOf x : T.presheaf.stalk t))
    (e : ℕ) (hFib : ∀ (Ω : Type u) [Field Ω] (y : Spec (.of Ω) ⟶ T),
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (a b : ℤ) (K : _root_.DerivedCategory (Sheaf (ProEt.topology S) (ModuleCat.{u + 1} B)))
    (hconstructible : ∀ q : ℤ, IsConstructible B
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K))
    (hbounded : ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) :
    let Φ := (lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor
    (∀ q : ℤ, IsConstructible B ((_root_.DerivedCategory.homologyFunctor _ q).obj (Φ.obj K))) ∧
      ∀ q : ℤ, (q < a ∨ b + 2 * (e : ℤ) < q) →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj (Φ.obj K)) := by
  let Φ := (lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor
  let P : ObjectProperty (Sheaf (ProEt.topology S) (ModuleCat.{u + 1} B)) := IsConstructible B
  have : P.IsClosedUnderIsomorphisms := ⟨fun i h ↦ isConstructible_of_iso i h⟩
  have single (F : Sheaf (ProEt.topology S) (ModuleCat.{u + 1} B)) (hF : P F) :
      (∀ q, IsConstructible B ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (Φ.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ∧
      _root_.DerivedCategory.homologyConcentratedIn 0 (2 * (e : ℤ))
        (Φ.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
    obtain ⟨G, hG, ⟨i⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj B hF
    let := hG
    have hfin := Etale.proper_directImage_finiteness hDimS hDimT f e
      (fun t ↦ hFib _ (T.algClosurePoint t)) B horder G
      ((isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf G).mpr hG)
    let j (q : ℤ) := (_root_.DerivedCategory.homologyFunctor _ q).mapIso
      (Φ.mapIso ((_root_.DerivedCategory.singleFunctor _ 0).mapIso i.symm)) ≪≫
        fixedHigherDirectImageIso f B G q
    have hge : (Φ.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).IsGE 0 :=
      (lowerStar (ModuleCat.{u + 1} B) f).isGE_rightDerivedFunctor_obj_singleFunctor F
    have hle : (Φ.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).IsLE
        (2 * (e : ℤ)) := (_root_.DerivedCategory.isLE_iff _ _).mpr (fun q hq ↦
      ((comparisonUpperStar (ModuleCat.{u + 1} B) T).map_isZero (hfin.2 q hq)).of_iso (j q))
    refine ⟨fun q ↦ ?_, hge, hle⟩
    by_cases hq : 0 ≤ q
    · have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hfin.1 q hq)
      exact isConstructible_of_iso (j q).symm (isConstructible_comparisonUpperStar_obj _)
    · have hz := _root_.DerivedCategory.isZero_of_isGE
        (Φ.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) 0 q (by omega)
      let : Zero (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) := HasZeroObject.zero' _
      let Z : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B) := 0
      have : IsConstructibleSheaf Z := IsConstructibleSheaf.of_isZero (isZero_zero _)
      exact isConstructible_of_iso
        (((comparisonUpperStar (ModuleCat.{u + 1} B) T).map_isZero
          (isZero_zero _)).iso hz) (isConstructible_comparisonUpperStar_obj Z)
  have hge : K.IsGE a := (_root_.DerivedCategory.isGE_iff _ _).mpr
    (fun q hq ↦ hbounded q (Or.inl hq))
  have hle : K.IsLE b := (_root_.DerivedCategory.isLE_iff _ _).mpr
    (fun q hq ↦ hbounded q (Or.inr hq))
  have hb : _root_.DerivedCategory.TStructure.t.bounded K := ⟨⟨a, hge⟩, b, hle⟩
  let Q := (ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} B) T).inverseImage Φ
  have hQ : Q K := _root_.DerivedCategory.prop_of_bounded Q P (fun F hF ↦ by
    obtain ⟨hc, hge, hle⟩ := single F hF
    exact ProEtale.DerivedCategory.boundedConstructible_of_homology B
      ⟨⟨0, hge⟩, 2 * (e : ℤ), hle⟩ (fun q ↦
        exists_isConstructibleSheaf_iso_comparisonUpperStar_obj B (hc q))) K hb hconstructible
  constructor
  · obtain ⟨L, hL, ⟨i⟩⟩ := hQ
    intro q
    have := hL.2 q
    exact isConstructible_of_iso
      (((comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategoryHomologyFunctorIso
          q).app L ≪≫
        (_root_.DerivedCategory.homologyFunctor _ q).mapIso i)
      (isConstructible_comparisonUpperStar_obj _)
  · have := hge
    have := hle
    by_cases hab : a ≤ b
    · have heq : a + ((b - a + 1).toNat : ℤ) - 1 = b := by omega
      have hle' : K.IsLE (a + ((b - a + 1).toNat : ℤ) - 1) := by rw [heq]; exact hle
      have hh := constructibleAmplitude Φ P (2 * (e : ℤ))
        (fun F hF ↦ (single F hF).2) (b - a + 1).toNat a K hge hle'
          (fun q _ _ ↦ hconstructible q)
      rw [heq] at hh
      intro q hq
      rcases hq with hq | hq
      · exact (_root_.DerivedCategory.isGE_iff _ _).mp hh.1 q hq
      · exact (_root_.DerivedCategory.isLE_iff _ _).mp hh.2 q hq
    · have hz := Φ.map_isZero (_root_.DerivedCategory.TStructure.t.isZero K b a (by omega))
      intro q _
      exact (_root_.DerivedCategory.homologyFunctor _ q).map_isZero hz

/-- One positive finite quotient of proper direct image has constructible cohomology
and the proper cohomological bound. No completed object or completeness is involved.
Source: blueprint preservation proof, steps 3--4; Stacks Tags 095U, 0GL0 and 09AL
(blueprint: lem-weil-pbc-finite-direct-image-cohomology).

Proof: restrict along the canonical function-to-constant ring isomorphism, then
use the exact constant-section equivalence of ConstructibleCoefficientSerre. The
canonical coefficient square gives the sectionwise direct-image comparison; derive
it using the universal right-derived composition comparisons. Intrinsic coefficient
constructibility is precisely fixed-module constructibility under this equivalence.

For a fixed-module sheaf choose its constructible etale origin and apply proper
finiteness on the etale site. Comparison with higher direct image gives constructible
cohomology in degrees [0,2e]. Successive truncation triangles extend this to a bounded
complex: prop_of_bounded gives constructibility, and constructibleAmplitude gives
[a,b+2e]. If a>b, the input and its additive derived direct image are zero. Finally
commute exact coefficient encoding with homology and reflect zero through its faithful
equivalence. This proves both assertions with the original quotient action, including
zero rings, empty schemes and unordered input intervals. -/
theorem pbc_finite_directImage_cohomology
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (hDimS : ∃ k : ℕ, topologicalKrullDim S ≤ (k : WithBot ℕ∞))
    (hDimT : ∃ k : ℕ, topologicalKrullDim T ≤ (k : WithBot ℕ∞))
    (f : S ⟶ T) [IsProper f] {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ)
    (_horderS : ∀ (x : A ⧸ d.ideal ^ (n + 1)) (s : S),
      IsUnit (addOrderOf x : S.presheaf.stalk s))
    (horderT : ∀ (x : A ⧸ d.ideal ^ (n + 1)) (t : T),
      IsUnit (addOrderOf x : T.presheaf.stalk t))
    (e : ℕ)
    (hFib : ∀ (Ω : Type u) [Field Ω] (y : Spec (.of Ω) ⟶ T),
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (a b : ℤ) (L : DerivedCategory (pbcModules S ((pbcAdicRings S d).obj (op n))))
    (hconstructible : ∀ q : ℤ,
      @IsConstructibleProEtaleCoefficientModuleSheaf S (A ⧸ d.ideal ^ (n + 1)) _
        (d.quotientFinite n) ((pbcRestrict (pbcLevelConstantComparison S d n).hom).obj
          ((DerivedCategory.homologyFunctor _ q).obj L)))
    (hbounded : ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj L)) :
    (∀ q : ℤ,
      @IsConstructibleProEtaleCoefficientModuleSheaf T (A ⧸ d.ideal ^ (n + 1)) _
        (d.quotientFinite n) ((pbcRestrict (pbcLevelConstantComparison T d n).hom).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((completedFiniteDerivedDirectImage f d n).obj L)))) ∧
      ∀ q : ℤ, (q < a ∨ b + 2 * (e : ℤ) < q) →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((completedFiniteDerivedDirectImage f d n).obj L)) := by
  let B := A ⧸ d.ideal ^ (n + 1)
  let F := reductionEncoding S d n
  let G := reductionEncoding T d n
  let J := F.mapDerivedCategory.obj L
  have hc (q : ℤ) : IsConstructible B
      ((_root_.DerivedCategory.homologyFunctor _ q).obj J) := by
    exact isConstructible_of_iso ((F.mapDerivedCategoryHomologyFunctorIso q).app L)
      ((CoefficientSerre.coefficient_constructible_iff S B _).mp (hconstructible q))
  have hb (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj J) :=
    F.isZero_homologyFunctor_mapDerivedCategory_obj (hbounded q hq)
  have hfin := fixedDirectImage hDimS hDimT f B horderT e hFib a b J hc hb
  let i := (reductionDerivedDirectImageEncoding f d n).app L
  constructor
  · intro q
    apply (CoefficientSerre.coefficient_constructible_iff T B _).mpr
    exact isConstructible_of_iso
      (((G.mapDerivedCategoryHomologyFunctorIso q).app
          ((completedFiniteDerivedDirectImage f d n).obj L) ≪≫
        (_root_.DerivedCategory.homologyFunctor _ q).mapIso i).symm) (hfin.1 q)
  · intro q hq
    apply G.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    exact (hfin.2 q hq).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso i)

end AlgebraicGeometry.Scheme
