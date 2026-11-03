/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.NativeFiniteExceptional.NativeFiniteExceptionalConstructions
public import WeilConjectures.AlgebraicGeometry.CoefDualizingSiteMates.CoefDualizingSiteMates
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
public import WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperCoefficientTensorUnit
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeOpenImmersionSheaf

/-! # The ordinary etale normalization of finite compact-support reduction

Source: latest blueprint, part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/sk-thm-sf-package/
lem-coef-finite-exceptional.proof.md, final paragraph; part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/lem-coef-finite-dualizing.md, counit normalization
(blueprint: lem-sf-finite-exceptional-etale-compact-support-comparison).

The coefficient indices are predecessors of positive exponents, as in the native
finite exceptional construction. Universal tensor presentations are identified with
scalar extension by their scalar units, never by an independently chosen isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory

namespace WeilConjectures.NativeFiniteExceptional

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]

/-- Finiteness of the actual positive coefficient quotient, reused from the coefficient
library. Source: finite coefficient convention
(blueprint: lem-sf-finite-exceptional-etale-compact-support-comparison). -/
local instance finiteRing (n : ℕ) : Finite (Ring ell E n) :=
  Padic.finite_coefficientExtensionRing ell E (n + 1) (Nat.succ_pos n)

private theorem single_open_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (M : DerivedCategoryModule A X) :
    (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)).unit.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map
        ((ExceptionalCoefficients.openIso φ j).hom.app M) =
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        ((Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).unit.app M) ≫
      (derivedRestrictScalarsCompOpenImmersionLowerShriekIso φ j).hom.app
        ((scalarExtension φ X).obj M) := by
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let z := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)
  let q := openDerivedRestrictScalarsIso φ j
  let β := openScalarExtension φ j
  let d := derivedRestrictScalarsCompOpenImmersionLowerShriekIso φ j
  have hc : conjugateEquiv (x.comp b) (a.comp z) β.hom = q.hom := by
    apply conjugateEquiv_eq_of_unit
    intro K
    exact (Adjunction.unit_leftAdjointUniq_hom_app
      (a.comp z) ((x.comp b).ofNatIsoRight q) K).symm
  have hm := iterated_mateEquiv_conjugateEquiv x z a b
    (TwoSquare.mk _ _ _ _ β.hom)
  have hd : (mateEquiv b a (TwoSquare.mk _ _ _ _ d.hom)).natTrans = q.hom :=
    single_open_mate φ j
  have hh : mateEquiv x z (TwoSquare.mk _ _ _ _ β.hom) =
      TwoSquare.mk _ _ _ _ d.hom := by
    apply (mateEquiv b a).injective
    apply TwoSquare.ext
    intro K
    exact congrArg (fun e ↦ e.app K) (hm.trans (hc.trans hd.symm))
  have h := unit_mateEquiv x z (TwoSquare.mk _ _ _ _ β.hom) M
  change _ ≫ (mateEquiv x z (TwoSquare.mk _ _ _ _ β.hom)).natTrans.app _ = _ at h
  rw [hh] at h
  rw [compactScalarOpen_eq]
  exact h.symm

private theorem ordinary_open_map_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    coefficientRestrictionOpenMap φ j =
      (openImmersionLowerShriekRestrictScalarsIso.{u} φ j).hom := by
  apply (mateEquiv
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)).injective
  rw [coefficientRestrictionOpenMap, Equiv.apply_symm_apply]
  symm
  apply mateEquiv_eq_of_unit
  intro M
  have h := openImmersionLowerShriekUpperStarAdjunction_unit_app_comp_upperStarMap.{u} φ j M
  have hh := congrArg (fun z ↦ z ≫
    (upperStarRestrictScalarsIso.{u} φ j).inv.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).obj M)) h
  simp only [Category.assoc, Iso.hom_inv_id_app] at hh
  erw [Category.comp_id] at hh
  exact hh.symm

private theorem ordinary_open_plus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (((coefficientRestrictionOpenPlus φ j).hom.app L).hom) =
      (derivedRestrictScalarsCompOpenImmersionLowerShriekIso φ j).hom.app L.obj := by
  have hi := coefficientRestrictionOpenMap_isIso φ j
  have he : asIso (coefficientRestrictionOpenMap φ j) =
      openImmersionLowerShriekRestrictScalarsIso φ j := Iso.ext (ordinary_open_map_eq φ j)
  have hcomp : DerivedCategory.Plus.ι.mapIso
      (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusCompIso
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)).app L) =
      (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryCompIso
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)).app L.obj) :=
    Iso.ext (Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app _ _ _)
  have hinv := congrArg Iso.inv hcomp
  change DerivedCategory.Plus.ι.map
      ((coefficientRestrictionOpenPlus φ j).hom.app L) = _
  simp only [coefficientRestrictionOpenPlus, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp]
  change DerivedCategory.Plus.ι.map
      (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusCompIso
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)).inv.app L) = _ at hinv
  rw [hinv]
  simp only [Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app]
  change (Functor.mapDerivedCategorySquareIso
    (asIso (coefficientRestrictionOpenMap φ j))).hom.app L.obj = _
  rw [he]
  rfl

private def restrictionInverse
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⋙
        Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ ⟶
      Sheaf.derivedRestrictScalars X.smallEtaleTopology φ ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  Functor.whiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory
      (scalarRestrictionDirectImageMap φ c.g) ≫
    Functor.whiskerRight (derivedRestrictScalarsCompOpenImmersionLowerShriekIso
      φ c.i).inv (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor

private theorem compact_unit_forward
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) :
    (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)).homEquiv
        _ _ (ExceptionalCoefficients.compactSupportMap φ c M) ≫
      (restrictionInverse φ c).app ((scalarExtension φ X).obj M) =
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).unit.app M) := by
  rw [Adjunction.homEquiv_unit]
  dsimp only [ExceptionalCoefficients.compactSupportMap,
    restrictionInverse, rightDerivedLowerShriekOfCompactification, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (scalarRestrictionDirectImageMap φ c.g).naturality
    ((ExceptionalCoefficients.openIso φ c.i).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  have hu := scalar_unit_directImage φ c.g
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)
  change (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)).unit.app
      ((lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)) ≫
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
      ((scalarMate φ c.g).app _) ≫
    (scalarRestrictionDirectImageMap φ c.g).app _ ≫ _ = _
  rw [reassoc_of% hu]
  rw [← Functor.map_comp_assoc, single_open_unit]
  rw [Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  congr 1
  erw [Category.comp_id]

private theorem restriction_plus_forward
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (((compactSupportCoefficientRestrictionPlus φ c).hom.app L).hom) ≫
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
        ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} B) c).hom.app L) ≫
      (restrictionInverse φ c).app L.obj =
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) := by
  let JA := openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i
  let JB := openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i
  let RA := lowerStar (ModuleCat.{u + 1} A) c.g
  let RB := lowerStar (ModuleCat.{u + 1} B) c.g
  have hd := directImage_comparison_plus φ c.g (JB.mapDerivedCategoryPlus.obj L)
  have hn := RA.rightDerivedFunctorPlusCompatibility.hom.naturality
    ((coefficientRestrictionOpenPlus φ c.i).hom.app L)
  dsimp only [Functor.comp_map] at hn
  simp only [compactSupportCoefficientRestrictionPlus,
    rightDerivedLowerShriekOfCompactificationPlusCompatibility, restrictionInverse,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
  change DerivedCategory.Plus.ι.map
      (RA.rightDerivedFunctorPlus.map ((coefficientRestrictionOpenPlus φ c.i).hom.app L)) ≫
    DerivedCategory.Plus.ι.map
      ((asIso (rightDerivedLowerStarRestrictScalars φ c.g)).inv.app
        (JB.mapDerivedCategoryPlus.obj L)) ≫
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
      (RB.rightDerivedFunctorPlusCompatibility.hom.app (JB.mapDerivedCategoryPlus.obj L)) ≫
    (scalarRestrictionDirectImageMap φ c.g).app (JB.mapDerivedCategory.obj L.obj) ≫
    RA.rightDerivedFunctor.map
      ((derivedRestrictScalarsCompOpenImmersionLowerShriekIso φ c.i).inv.app L.obj) =
    RA.rightDerivedFunctorPlusCompatibility.hom.app _
  erw [← reassoc_of% hd]
  simp only [← Functor.map_comp_assoc, ← NatTrans.comp_app, asIso_inv,
    IsIso.inv_hom_id, NatTrans.id_app]
  erw [Category.comp_id, reassoc_of% hn]
  have ho := ordinary_open_plus φ c.i L
  change DerivedCategory.Plus.ι.map ((coefficientRestrictionOpenPlus φ c.i).hom.app L) =
    (derivedRestrictScalarsCompOpenImmersionLowerShriekIso φ c.i).hom.app L.obj at ho
  erw [ho, ← RA.rightDerivedFunctor.map_comp, Iso.hom_inv_id_app]
  erw [RA.rightDerivedFunctor.map_id, Category.comp_id]
  rfl

private theorem model_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B}
    {T : Scheme.{u}}
    {K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ T K) :
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).unit.app K.obj ≫
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map
        (ProEtale.CoefDualizingSiteMates.modelIso M).hom = M.unit.hom := by
  exact ((Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)

private theorem comparison_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj K)) :
    N.unit.hom ≫ (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
      (compactSupportCoefficientComparisonPlus c M N).hom =
    ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).map
      M.unit).hom ≫ ((compactSupportCoefficientRestrictionPlus φ c).hom.app M.obj).hom := by
  exact (Equiv.ofBijective _ (N.universal _)).apply_symm_apply _

private theorem comparison_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj K)) :
    ExceptionalCoefficients.compactSupportMap φ c K.obj =
      (scalarExtension φ Y).map
          ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
            (ModuleCat.{u + 1} A) c).inv.app K) ≫
        (ProEtale.CoefDualizingSiteMates.modelIso N).hom ≫
        (compactSupportCoefficientComparisonPlus c M N).hom ≫
        (rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} B) c).hom.app M.obj ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
          (ProEtale.CoefDualizingSiteMates.modelIso M).inv := by
  let FA := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let FB := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
  let UY := Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ
  let aA := rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) c
  let aB := rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} B) c
  let eX := ProEtale.CoefDualizingSiteMates.modelIso M
  let eY := ProEtale.CoefDualizingSiteMates.modelIso N
  let ad := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)
  have := scalar_directImage_isIso φ c.g
  have hr : IsIso (restrictionInverse φ c) := by
    dsimp only [restrictionInverse]
    infer_instance
  apply (cancel_mono (FB.map eX.hom)).1
  change _ = (_ ≫ _ ≫ _ ≫ _ ≫ FB.map eX.inv) ≫ FB.map eX.hom
  rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc,
    ← FB.map_comp, eX.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
  apply (ad.homEquiv _ _).injective
  apply (cancel_mono ((restrictionInverse φ c).app M.obj.obj)).1
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (restrictionInverse φ c).naturality eX.hom
  dsimp only [Functor.comp_map] at hn
  change UY.map (FB.map eX.hom) ≫ (restrictionInverse φ c).app M.obj.obj =
    (restrictionInverse φ c).app ((scalarExtension φ X).obj K.obj) ≫
      FA.map ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map eX.hom) at hn
  erw [hn]
  have hcu := compact_unit_forward φ c K.obj
  rw [Adjunction.homEquiv_unit, Category.assoc] at hcu
  change ad.unit.app _ ≫ UY.map (ExceptionalCoefficients.compactSupportMap φ c K.obj) ≫
    (restrictionInverse φ c).app _ =
      FA.map ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).unit.app K.obj) at hcu
  erw [reassoc_of% hcu]
  rw [← FA.map_comp, model_unit M]
  have hu := ad.unit.naturality (aA.inv.app K)
  dsimp only [Functor.comp_map, Functor.id_map] at hu
  erw [← reassoc_of% hu, reassoc_of% (model_unit N)]
  erw [reassoc_of% (comparison_unit c M N)]
  erw [restriction_plus_forward φ c M.obj]
  have ha := aA.hom.naturality M.unit
  dsimp only [Functor.comp_map] at ha
  erw [ha]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

/-- The ordinary etale arrow in the structural compositor is the specified tensor
comparison, naturally in its input, with its proper and open factors retained.
Source: lem-coef-finite-exceptional.proof.md, final paragraph
(blueprint: lem-sf-finite-exceptional-etale-compact-support-comparison).

Proof: write c=(j,p). By def-per-exceptional-coefficient-maps the ordinary arrow is
scalarMate at j_!K followed by Rp_* of the open balancing isomorphism. The proper
scalar normalization identifies the first factor with the ordered projection map;
the open scalar coherence identifies the second with the unit-normalized balancing
map. Apply the scalar Hom adjunction and precompose both candidates with its unit.
On K-flat representatives both apply the proper counit to the original factor and
retain the B factor in the same order. Injectivity of the Hom equivalence gives
B-linear equality. The canonical modelIso is itself the transpose of the universal
tensor unit, so the displayed transports preserve this calculation. Both factors
are natural, giving the final square. No flatness of the quotient is used. -/
theorem etaleCompactSupportComparison (D : FiniteFieldDatum.{u}) (_hell : ell ≠ D.p)
    (n : ℕ) {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f) :
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing ell E (n + 1 + 1))
    let B := ULift.{u + 1} (Padic.coefficientExtensionRing ell E (n + 1))
    let φ : A →+* B :=
      RingHom.ulift.{u + 1, u + 1} (Padic.coefficientExtensionTransition ell E (n + 1))
    ∀ (K : _root_.DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (M : Etale.CoefficientTensorModel φ X K)
      (N : Etale.CoefficientTensorModel φ Y
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} A) c).obj K)),
    (_hK : finiteTorConstructibleEtale ell E (n + 1 + 1)
      (Nat.succ_pos (n + 1)) X K.obj) →
    let eX := ProEtale.CoefDualizingSiteMates.modelIso M
    let eY := ProEtale.CoefDualizingSiteMates.modelIso N
    let FA := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
    let FB := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
    let aA := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c
    let aB := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} B) c
    (Etale.ExceptionalCoefficients.compactSupportMap φ c K.obj =
      (Etale.scalarExtension φ Y).map (aA.inv.app K) ≫ eY.hom ≫
        (Etale.compactSupportCoefficientComparisonPlus c M N).hom ≫
        aB.hom.app M.obj ≫ FB.map eX.inv) ∧
    (Etale.ExceptionalCoefficients.compactSupportMap φ c K.obj =
      (Etale.scalarMate φ c.g).app
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K.obj) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.map
        ((Etale.ExceptionalCoefficients.openIso φ c.i).hom.app K.obj)) ∧
    (∀ (L : _root_.DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (_hL : finiteTorConstructibleEtale ell E (n + 1 + 1)
        (Nat.succ_pos (n + 1)) X L.obj) (a : K.obj ⟶ L.obj),
      (Etale.scalarExtension φ Y).map (FA.map a) ≫
          Etale.ExceptionalCoefficients.compactSupportMap φ c L.obj =
        Etale.ExceptionalCoefficients.compactSupportMap φ c K.obj ≫
          FB.map ((Etale.scalarExtension φ X).map a)) := by
  dsimp only
  intro K M N hK
  refine ⟨?_, rfl, ?_⟩
  · exact Etale.comparison_eq c M N
  · intro L hL a
    exact Etale.compactScalarMap_naturality _ c a

/-- At the structural dualizing object the same ordinary map occurs in the prescribed
counit identity; the scalar-unit comparison is retained explicitly.
Source: lem-coef-finite-dualizing.md, displayed adjunct and final sentence, and
lem-coef-finite-exceptional.proof.md, final paragraph
(blueprint: lem-sf-finite-exceptional-etale-compact-support-comparison).

Proof: retain the specified word, including the inverse compact-support comparison,
the scalar image of the A counit, and the regular-unit comparison. By definition u
is its image under the exceptional Hom equivalence. The inverse Hom equivalence
sends u to F_B(u) followed by the B counit. Applying the inverse to the image of
the word returns the word, which is exactly the displayed identity. This formal
adjunction identity requires no additional comparison or invertibility argument. -/
theorem etaleCompactSupportComparison_counit (n : ℕ)
    (D : FiniteFieldDatum.{u}) (_hell : ell ≠ D.p) (X : Scheme.{u})
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (c : Compactification (X ↘ Spec (.of D.k))) :
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing ell E (n + 1 + 1))
    let B := ULift.{u + 1} (Padic.coefficientExtensionRing ell E (n + 1))
    let φ : A →+* B :=
      RingHom.ulift.{u + 1, u + 1} (Padic.coefficientExtensionTransition ell E (n + 1))
    letI : Finite A := inferInstance
    letI : Finite B := inferInstance
    let adA := Etale.rightDerivedUpperShriekOfCompactificationAdjunction A c
    let adB := Etale.rightDerivedUpperShriekOfCompactificationAdjunction B c
    let GA := Etale.rightDerivedUpperShriekOfCompactification A c
    let FB := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
    let omega := GA.obj (𝟙_ (Etale.DerivedCategoryModule A (Spec (.of D.k))))
    let word := Etale.ExceptionalCoefficients.comparisonInverse φ c omega ≫
      (Etale.scalarExtension φ (Spec (.of D.k))).map
        (adA.counit.app (𝟙_ (Etale.DerivedCategoryModule A (Spec (.of D.k))))) ≫
      (Etale.ExceptionalCoefficients.unitIso φ (Spec (.of D.k))).hom
    let u := adB.homEquiv _ _ word
    FB.map u ≫
        adB.counit.app (𝟙_ (Etale.DerivedCategoryModule B (Spec (.of D.k)))) = word := by
  dsimp only
  exact ((Etale.rightDerivedUpperShriekOfCompactificationAdjunction
      (ULift.{u + 1} (Padic.coefficientExtensionRing ell E (n + 1))) c).homEquiv
      _ _).symm_apply_apply _

end WeilConjectures.NativeFiniteExceptional
