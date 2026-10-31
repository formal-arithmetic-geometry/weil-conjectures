/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions

import all WeilConjectures.SmoothPurity.PurityFiniteSetting.OrdinaryDiagonal.DiagonalOrdinaryChartLift
import all WeilConjectures.AlgebraicGeometry.ProjectiveLineTateCoefficientGenerator
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import all WeilConjectures.AlgebraicGeometry.ProjectiveLineConstantCoefficientGenerator
import all WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
import all WeilConjectures.AlgebraicGeometry.ProjectiveLineGenusZero
import all WeilConjectures.AlgebraicGeometry.Curve
import all WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import all WeilConjectures.Topology.RingedSpaceModuleCohomology
import all WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import all WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import all WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import all WeilConjectures.AlgebraicGeometry.Curve.Estimate
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import all WeilConjectures.AlgebraicGeometry.Sites.Kummer
import all Mathlib.Algebra.Module.ZMod
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import all WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import all WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import all WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import all WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.AlgebraicGeometry.DegreeZeroMapGluing.DegreeZeroDerivedMapGluing

/-! # A step of the model orientation descent argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

private def realizedConstantUnit (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] [Finite A] :
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    (ProEtale.finiteCoefficientRealization X A).obj
      ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A A)) ≅
      SheafOfModules.unit (ProEtale.finiteCoefficientRingSheaf X A) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  let t := Scheme.ProEt.topology X
  let R := ProEtale.finiteCoefficientRingSheaf X A
  let α := ProEtale.finiteCoefficientScalarMap X A
  let E := ProEtale.finiteCoefficientModulePresheaf X.ProEt A
  let Q := PresheafOfModules.sheafification.{u + 1} α
  let B := (Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A)
  let p : E.obj B ⟶ (PresheafOfModules.restrictScalars α).obj
      (SheafOfModules.unit R).val :=
    { app := fun W ↦ ModuleCat.ofHom (X := (E.obj B).obj W)
        (Y := ((PresheafOfModules.restrictScalars α).obj
          (SheafOfModules.unit R).val).obj W)
        { toFun := fun a ↦ (α.app W).hom a
          map_add' := fun a b ↦ map_add (α.app W).hom a b
          map_smul' := fun a b ↦ map_mul (α.app W).hom a b }
      naturality := fun {W V} f ↦ by
        ext
        exact ConcreteCategory.congr_hom (α.naturality f) 1 }
  have hp : IsIso (Q.map p) := by
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf R)]
    change IsIso ((presheafToSheaf t AddCommGrpCat.{u + 1}).map
      ((PresheafOfModules.toPresheaf _).map p))
    rw [← GrothendieckTopology.W_iff, GrothendieckTopology.W_iff_isLocallyBijective]
    constructor
    · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem t α x y h⟩
    · exact ⟨fun x ↦ Presheaf.imageSieve_mem t α x⟩
  have hη : IsIso (Q.map (E.map (toSheafify t B))) := by
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf R)]
    change IsIso ((presheafToSheaf t AddCommGrpCat.{u + 1}).map
      (Functor.whiskerRight (toSheafify t B)
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})))
    rw [← GrothendieckTopology.W_iff]
    let : t.PreservesSheafification
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) :=
      Sheaf.preservesSheafification_of_adjunction _ (ModuleCat.forget₂CoinduceAdj A)
    exact t.W_of_preservesSheafification _ _ (t.W_toSheafify B)
  exact (asIso (Q.map (E.map (toSheafify t B)))).symm ≪≫ asIso (Q.map p) ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction α).counit.app
      (SheafOfModules.unit R))

/-- Shifted finite Tate powers are rank-one degree-zero objects after shift removal,
and their automorphisms are detected on any Zariski cover.
Source: model descent Step 8; Stacks 06XS, 03EM, 04TQ
(blueprint: lem-pur-model-orientation-tate-detection).

Proof: the structure morphism to the algebraically closed field k makes the
diagonal exponent N invertible on X. A primitive N-th root in k identifies the
finite Tate line with the constant regular A-module; the integer tensor-family
comparison then identifies every Tate power with the coefficient unit. The ordinary
shifted normal form identifies diagonalTwist(X,r) with the single Tate sheaf in
degree zero shifted by 2r; exact comparison inverse image commutes with the shift and
the single functor, so after removing the shift the unshifted object is isomorphic to
the coefficient unit in degree zero. This gives concentration in degree zero, and H^0
realizes to the unit module over the finite coefficient ring sheaf (sheafification of
the constant regular presheaf), which is finite locally free of rank one.
For an arbitrary Zariski covering, exact restriction preserves this concentration.
Apply degreeZeroDerivedMapGluing with this object as both endpoints: the restriction
map on endomorphisms is injective. Naturality of the restriction/shift isomorphism
identifies endomorphisms before and after shift removal, compatibly with restriction.
Apply Iso.ext to obtain injectivity for automorphisms. Degree-zero gluing includes the
empty cover, so no nonemptiness hypothesis is needed. -/
theorem model_orientation_tate_detection (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (aX : X ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] (r : ℕ) :
    ModelOrientationDetection.{u, w} P X r := by
  classical
  let A := P.Coefficient
  let J := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
  let L : C := 𝟙_ C
  let S := _root_.DerivedCategory.singleFunctor C 0
  let n : ℤ := 2 * (r : ℤ)
  have hN : (P.diagonalExponent : P.field.k) ≠ 0 := by
    have h := P.diagonalExponent_isUnit (𝟙 (Spec (.of P.field.k)))
    have hh := h.map (Scheme.ΓSpecIso (.of P.field.k)).hom.hom
    simpa only [map_natCast] using hh.ne_zero
  obtain ⟨el⟩ := Etale.kummer_line_as_constant P.diagonalExponent A
    P.diagonalExponent_annihilates P.field.k aX hN
  let F := Scheme.finiteEtaleTateTensorFamily X P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) A P.diagonalExponent_annihilates
      (P.diagonalExponent_isUnit aX)
  let ep : Scheme.finiteEtaleTateSheaf A P.diagonalExponent X
      P.diagonalExponent_annihilates (r : ℤ) ≅ 𝟙_ _ :=
    IntTensorFamily.iso F .constant el (r : ℤ)
  obtain ⟨e⟩ := OrdinaryDiagonal.base_normal_form P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) A P.diagonalExponent_annihilates X
      (P.diagonalExponent_isUnit aX) r
  let et : P.diagonalTwist X r ≅ (S.obj L)⟦n⟧ :=
    J.mapIso e ≪≫ (J.commShiftIso n).app _ ≪≫
      (shiftFunctor _ n).mapIso
        (((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} A) X).mapDerivedCategorySingleFunctor 0).app _ ≪≫
          S.mapIso ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapIso ep ≪≫
            (Functor.Monoidal.εIso
              (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)).symm))
  let eu : P.modelOrientationUnshifted X r ≅ S.obj L :=
    (shiftFunctor _ (-n)).mapIso et ≪≫ shiftShiftNeg _ n
  have hc : _root_.DerivedCategory.homologyConcentratedIn 0 0
      (P.modelOrientationUnshifted X r) :=
    ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso eu.symm 0,
      _root_.DerivedCategory.TStructure.t.isLE_of_iso eu.symm 0⟩
  refine ⟨hc, ?_, ?_⟩
  · let : TopologicalSpace A := ⊥
    let : DiscreteTopology A := ⟨rfl⟩
    let h : ((_root_.DerivedCategory.homologyFunctor C 0).obj
        (P.modelOrientationUnshifted X r)) ≅ L :=
      (_root_.DerivedCategory.homologyFunctor C 0).mapIso eu ≪≫
        (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app L
    let er := (ProEtale.finiteCoefficientRealization X A).mapIso h ≪≫
      realizedConstantUnit X A
    have : (SheafOfModules.unit
        (ProEtale.finiteCoefficientRingSheaf X A)).IsFiniteLocallyFreeOfRank 1 :=
      (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one _).mp inferInstance
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso er.symm
  · intro I U hU a b hab
    let K := P.modelOrientationUnshifted X r
    have hc' (i : I) : _root_.DerivedCategory.homologyConcentratedIn 0 0
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategory.obj K) := by
      have : K.IsGE 0 := hc.1
      have : K.IsLE 0 := hc.2
      exact ⟨(ProEtale.upperStar (ModuleCat.{u + 1} A) (U i).ι).isGE_mapDerivedCategory_obj K 0,
        (ProEtale.upperStar (ModuleCat.{u + 1} A) (U i).ι).isLE_mapDerivedCategory_obj K 0⟩
    have hg := ((DegreeZeroMapGluing.degreeZeroDerivedMapGluing A X U hU).2).2
      K K (fun i ↦ ⟨hc' i, hc' i⟩)
    apply Iso.ext
    apply (shiftFunctor _ (-n)).map_injective
    apply (hg.2.2.2.2.2 _ _).mp
    intro i
    let R := (ProEtale.upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategory
    have hi : R.map a.hom = R.map b.hom :=
      congrArg Iso.hom (congrFun hab i)
    apply (cancel_mono ((R.commShiftIso (-n)).hom.app (P.diagonalTwist X r))).1
    have hn (f : P.diagonalTwist X r ⟶ P.diagonalTwist X r) :
        R.map ((shiftFunctor _ (-n)).map f) ≫
            (R.commShiftIso (-n)).hom.app (P.diagonalTwist X r) =
          (R.commShiftIso (-n)).hom.app (P.diagonalTwist X r) ≫
            (shiftFunctor _ (-n)).map (R.map f) := by
      simpa only [Functor.comp_map] using (R.commShiftIso (-n)).hom.naturality f
    exact (hn a.hom).trans ((congrArg (fun f ↦
      (R.commShiftIso (-n)).hom.app (P.diagonalTwist X r) ≫
        (shiftFunctor _ (-n)).map f) hi).trans (hn b.hom).symm)

end WeilConjectures.PurityFiniteSetting
