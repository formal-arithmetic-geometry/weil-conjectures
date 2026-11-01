/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionRestrictionData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionBaseComparisonLaws

/-! # Fibre squares of section restriction and base change

Source: blueprint latest, sec-smooth-purity, orientation charts Step 3 and
composition coherence Step 1 (blueprint: lem-pur-section-fibre-squares).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.SectionRestriction

private noncomputable def oneSquare {B : Scheme.{u}} {d : ℕ} (X : Pair B d) :
    BaseChange (AffineSpace.oneSection (ULift.{u} (Fin 1)) B) X (familyPair X) :=
  ⟨Scheme.Hom.deformationSpaceOneFibre X.g X.s,
    Scheme.Hom.isPullback_deformationSpaceOneFibre X.g X.s,
    Scheme.Hom.comp_deformationSpaceOneFibre X.section_eq⟩

private noncomputable def zeroSquare (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} {d : ℕ} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (X : Pair B d) :
    BaseChange (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)
      (normalPair P aB X) (familyPair X) :=
  ⟨X.s.ker.normalConeToDeformationSpace,
    Scheme.Hom.isPullback_normalConeToDeformationSpace X.g X.s,
    Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace⟩

private theorem endpointOne_eq (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} {d : ℕ} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (X : Pair B d) :
    endpointOne P aB X =
      baseComparison P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) aB
        (oneSquare X) := by
  rfl

private theorem endpointZero_eq (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} {d : ℕ} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (X : Pair B d) :
    endpointZero P aB X =
      baseComparison P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) aB
        (zeroSquare P aB X) := by
  rfl

private theorem baseComparison_congr (P : PurityFiniteSetting.{u})
    {B' B : Scheme.{u}} {d : ℕ} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB' : B' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB'] [QuasiCompact aB']
    {b b' : B' ⟶ B} {X' : Pair B' d} {X : Pair B d}
    (sq : BaseChange b X' X) (sq' : BaseChange b' X' X)
    (hb : b = b') (hm : sq.map = sq'.map) :
    baseComparison P aB aB' sq =
      (ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) hb).app
        (invariant P aB X) ≪≫ baseComparison P aB aB' sq' := by
  subst b'
  have hs : sq = sq' := by
    cases sq
    cases sq'
    cases hm
    rfl
  subst sq'
  change baseComparison P aB aB' sq = Iso.refl _ ≪≫ baseComparison P aB aB' sq
  simp

private theorem base_rectangle (P : PurityFiniteSetting.{u})
    (laws : BasePasting P)
    {A A' B B' : Scheme.{u}}
    (aA : A ⟶ Spec (.of P.field.k))
    [IsSeparated aA] [LocallyOfFiniteType aA] [QuasiCompact aA]
    (aA' : A' ⟶ Spec (.of P.field.k))
    [IsSeparated aA'] [LocallyOfFiniteType aA'] [QuasiCompact aA']
    (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB' : B' ⟶ Spec (.of P.field.k))
    [IsSeparated aB'] [LocallyOfFiniteType aB'] [QuasiCompact aB']
    (v : A' ⟶ A) (i : B ⟶ A) (i' : B' ⟶ A') (b : B' ⟶ B)
    (hv : v ≫ aA = aA') (hi : i ≫ aA = aB)
    (hi' : i' ≫ aA' = aB') (hb : b ≫ aB = aB')
    (comm : i' ≫ v = b ≫ i) {d : ℕ}
    {X : Pair A d} {X' : Pair A' d} {Y : Pair B d} {Y' : Pair B' d}
    (top : BaseChange v X' X) (left : BaseChange i Y X)
    (right : BaseChange i' Y' X') (bottom : BaseChange b Y' Y)
    (hm : bottom.map ≫ left.map = right.map ≫ top.map) :
    (((ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        b i).app (invariant P aA X)).symm ≪≫
      (ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient)
        comm.symm).app (invariant P aA X) ≪≫
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        i' v).app (invariant P aA X)) ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) i').leftDerivedFunctor.mapIso
        (baseComparison P aA aA' top) ≪≫ baseComparison P aA' aB' right =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (baseComparison P aA aB left) ≪≫ baseComparison P aB aB' bottom := by
  have h := baseComparison_congr P aA aB' (bottom.comp left) (right.comp top)
    comm.symm hm
  rw [laws.2 _ _ _ aA aB aB' i hi b hb d X Y Y' left bottom,
    laws.2 _ _ _ aA aA' aB' v hv i' hi' d X X' Y' top right] at h
  apply Iso.ext
  have hh := congrArg Iso.hom h
  have hh' := congrArg
    (fun f ↦ ((ProEtale.leftDerivedUpperStarComp
      (ModuleCat.{u + 1} P.Coefficient) b i).app (invariant P aA X)).inv ≫ f) hh
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc] using hh'.symm

/-- The specified one- and zero-fibre comparisons commute with restriction and base change.
Source: blueprint latest, orientation charts Step 3 and composition coherence Step 1
(blueprint: lem-pur-section-fibre-squares).
Proof: the Rees coefficient map preserves t, the augmented section, and both fibre maps;
its one fibre is the original etale map and its zero fibre is normalMap. Apply smooth
exceptional base-change pasting to the two Cartesian fibre squares. The two paths in
each rectangle are the same counit mate, with the canonical pullback-composition
constraints. Thus restricting the family rho/compositor gives precisely the section
rho/compositor at each endpoint. For an arbitrary base square, the two factorizations
of the outer Cartesian rectangle give the same exceptional comparison by mate-pasting.
Pull back by the section and insert endpointPull. Naturality of the canonical nu*
comparison gives the displayed equations on the actual pro-etale objects. The published
sectionExceptional_etale_fibre_coherence and sectionExceptional_fibre_coherence express
these calculations in structural-locality coordinates; counit normalization identifies
them with the explicit rho/compositor coordinates here. No orientation is chosen. -/
theorem section_fibre_squares (P : PurityFiniteSetting.{u}) :
  (∀ (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d : ℕ) (X' X : Pair B d) (a : EtaleMap X' X),
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso
          (familyRestriction P aB a) ≪≫ endpointOne P aB X =
      endpointOne P aB X' ≪≫ restriction P aB a) ∧
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso
          (familyRestriction P aB a) ≪≫ endpointZero P aB X =
      endpointZero P aB X' ≪≫ restriction P aB (normalEtaleMap P aB a))) ∧
  (∀ (B B₀ : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB₀ : B₀ ⟶ Spec (.of P.field.k))
    [IsSeparated aB₀] [LocallyOfFiniteType aB₀] [QuasiCompact aB₀]
    (b : B₀ ⟶ B) (_hb : b ≫ aB = aB₀) (d : ℕ)
    (X : Pair B d) (X₀ : Pair B₀ d) (sq : BaseChange b X₀ X),
    (endpointPull P b _ _ (AffineSpace.oneSection_comp_map b)
        (invariant P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) (familyPair X)) ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) B₀)).leftDerivedFunctor.mapIso
          (baseComparison P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB)
            ((AffineSpace (ULift.{u} (Fin 1)) B₀ ↘ B₀) ≫ aB₀)
            (familyBaseChange P aB aB₀ sq)) ≪≫ endpointOne P aB₀ X₀ =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (endpointOne P aB X) ≪≫ baseComparison P aB aB₀ sq) ∧
    (endpointPull P b _ _ (AffineSpace.zeroSection_comp_map b)
        (invariant P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) (familyPair X)) ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B₀)).leftDerivedFunctor.mapIso
          (baseComparison P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB)
            ((AffineSpace (ULift.{u} (Fin 1)) B₀ ↘ B₀) ≫ aB₀)
            (familyBaseChange P aB aB₀ sq)) ≪≫ endpointZero P aB₀ X₀ =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (endpointZero P aB X) ≪≫
          baseComparison P aB aB₀ (normalBaseChange P aB aB₀ sq))) := by
  have laws := section_base_comparison_laws P
  constructor
  · intro B aB _ _ _ d X' X a
    constructor
    · rw [endpointOne_eq, endpointOne_eq]
      exact laws.2 _ _ _ aB _ (by
        rw [← Category.assoc, AffineSpace.oneSection_comp_over, Category.id_comp])
        d (familyPair X') (familyPair X) X' X (familyMap P aB a) a
        (oneSquare X) (oneSquare X') (geometry P aB a).2.2.2.2.2.2.2.2.2.2.1.symm
    · rw [endpointZero_eq, endpointZero_eq]
      exact laws.2 _ _ _ aB _ (by
        rw [← Category.assoc, AffineSpace.zeroSection_comp_over, Category.id_comp])
        d (familyPair X') (familyPair X) (normalPair P aB X') (normalPair P aB X)
        (familyMap P aB a) (normalEtaleMap P aB a)
        (zeroSquare P aB X) (zeroSquare P aB X')
        (geometry P aB a).2.2.2.2.2.2.2.2.2.2.2.symm
  · intro B B₀ aB _ _ _ aB₀ _ _ _ b hb d X X₀ sq
    constructor
    · rw [endpointOne_eq, endpointOne_eq]
      exact base_rectangle P laws.1 _ _ aB aB₀ _ _ _ b
        (by rw [← Category.assoc, AffineSpace.map_over, Category.assoc, hb])
        (by rw [← Category.assoc, AffineSpace.oneSection_comp_over, Category.id_comp])
        (by rw [← Category.assoc, AffineSpace.oneSection_comp_over, Category.id_comp])
        hb (AffineSpace.oneSection_comp_map b)
        (familyBaseChange P aB aB₀ sq) (oneSquare X) (oneSquare X₀) sq
        (reesBaseGeometry P aB aB₀ sq).2.2.symm
    · rw [endpointZero_eq, endpointZero_eq]
      apply base_rectangle P laws.1 _ _ aB aB₀ _ _ _ b
        (by rw [← Category.assoc, AffineSpace.map_over, Category.assoc, hb])
        (by rw [← Category.assoc, AffineSpace.zeroSection_comp_over, Category.id_comp])
        (by rw [← Category.assoc, AffineSpace.zeroSection_comp_over, Category.id_comp])
        hb (AffineSpace.zeroSection_comp_map b)
        (familyBaseChange P aB aB₀ sq) (zeroSquare P aB X) (zeroSquare P aB₀ X₀)
        (normalBaseChange P aB aB₀ sq)
      exact (Scheme.Hom.isPullback_normalConeToDeformationSpace X.g X.s).lift_fst _ _ _

end WeilConjectures.PurityFiniteSetting.SectionRestriction
