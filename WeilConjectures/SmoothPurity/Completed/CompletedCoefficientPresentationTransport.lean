/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient

import all WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Data.Nat.Prime.Infinite
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientIsoBoundedConstructible
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedCoefficientTransportSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.ProEtaleCoefficients.CompletedCoefficientCompletionRoosTransportLegacy
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
public import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction

/-! # Completed coefficient presentation and tensor transport

Source: main-20261015, sec-six-functors-basics/sk-lem-sf-mate,
fix-prop-adjunctions.proof.md, Step 1; Stacks 099N (2),(5), 03D7, 070I;
Bhatt--Scholze, Lemma 6.8.2(1).
(blueprint: def-pur-completed-coefficient-presentation-transport).

The coefficient ring comparison and derived transport are the landed integral
stratified-perfect interfaces. Only the CommRing lift, its explicit inverse
restriction model, completeness tests and normalized tensor comparison are supplied here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme TensorProduct
open scoped ChangeOfRings
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Bounded constructibility comparison under exactly the landed geometric bounds.
Source: Bhatt--Scholze 6.5.1, 6.8.11(3)
(blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: apply integralStratifiedPerfectDetailed to the transported object. The
inverse functor of purCoefficientModel is the landed integralDetailedTransport,
so its unit identifies the resulting object with K. Both bounded constructible
predicates are invariant under that isomorphism. The Noetherian, dimension and
invertibility assumptions are precisely those of the landed characterization. -/
theorem purCoefficientModel_bounded_predicate (W : Scheme.{u}) [IsNoetherian W]
    (_hdim : ∃ n : ℕ, topologicalKrullDim W ≤ n)
    (_hinv : IsUnit (l : Γ(W, ⊤)))
    (K : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E) K ↔
      sfIntegralConstructible l E W ((purCoefficientModel l E W).functor.obj K) := by
  have hInv : ∀ t : W, IsUnit (l : W.presheaf.stalk t) := by
    intro t
    simpa only [map_natCast] using
      RingHom.isUnit_map (W.presheaf.germ ⊤ t trivial).hom _hinv
  have := (pbcIntegralUniformComplete_isTriangulated l E W _hdim hInv).1
  let Φ := purCoefficientModel l E W
  have h := integralStratifiedPerfectDetailed W l E _hdim _hinv (Φ.functor.obj K)
  have e : (integralDetailedTransport W l E).obj (Φ.functor.obj K) ≅ K :=
    (Φ.unitIso.app K).symm
  exact (ObjectProperty.prop_iff_of_iso
    (PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E)) e).symm.trans h.symm

/-- The recorded tensor generator for ordinary integral scalar extension.
Source: Stacks 03EK (blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purRawTensorSection (W : Scheme.{u}) (M : integralTowerModules l E W)
    (U : W.ProEtᵒᵖ) (a : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
    (x : M.val.obj U) : ((integralOrdinaryScalar l E L ι W).obj M).val.obj U :=
  (eqToHom ((integralOrdinaryScalarWitness l E L ι W).choose_spec.choose M).symm).val.app U
    ((toSheafify (ProEt.topology W)
      (SheafOfModules.changeOfRingsPresheaf
        (integralCompletedScalarMap l E L ι W) M).presheaf).app U
        (a ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E W).obj.obj U,
          ((integralCompletedScalarMap l E L ι W).hom.app U).hom] x))

private theorem levelConstant_hom (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (pbcLevelConstantComparison W d n).hom =
      AdicCoefficients.constantComparison W (A ⧸ d.ideal ^ (n + 1)) := by
  let := d.quotientFinite
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((pbcAdicRings W d).obj (Opposite.op n)).property
  change toSheafify _ _ ≫ (pbcLevelConstantComparison W d n).hom.hom =
    toSheafify _ _ ≫ sheafifyMap _ _
  rw [← toSheafify_naturality]
  ext U b
  exact (pbcLevelConstantComparison_exists W d n).exists.choose_spec U b

private theorem levelConstant_scalar (W : Scheme.{u}) (n : ℕ) :
    (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (pbcScalarQuotientMap l E L ι n)) ≫
        (pbcLevelConstantComparison W (pbcIntegralDatum l L) n).hom =
      (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom ≫
        AdicCoefficients.coefficientMap W (pbcScalarQuotientMap l E L ι n) := by
  rw [levelConstant_hom, levelConstant_hom]
  change (presheafToSheaf _ CommRingCat).map _ ≫
      (presheafToSheaf _ CommRingCat).map _ =
    (presheafToSheaf _ CommRingCat).map _ ≫
      (presheafToSheaf _ CommRingCat).map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1

private theorem quotientScalar_square (W : Scheme.{u}) (n : ℕ) :
    (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (pbcScalarQuotientMap l E L ι n)) ≫
      (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (integralCoefficientULift l L n).toCommRingCatIso.hom =
    (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (integralCoefficientULift l E n).toCommRingCatIso.hom ≫
      integralScalarQuotientSheafMap l E L ι W n := by
  let C := constantSheaf (ProEt.topology W) CommRingCat.{u + 1}
  change C.map _ ≫ C.map _ = C.map _ ≫ C.map _
  rw [← C.map_comp, ← C.map_comp]
  apply congrArg C.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change integralCoefficientULift l L n
      (pbcScalarQuotientMap l E L ι n (Ideal.Quotient.mk _ x)) = _
  rw [show pbcScalarQuotientMap l E L ι n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (ULift.up (integralScalarIntegerInclusion l E L ι x.down)) from rfl]
  have hqL (z : PbcIntegralRing l L) :
      integralCoefficientULift l L n (Ideal.Quotient.mk _ z) =
        ULift.up (Ideal.Quotient.mk _ z.down) :=
    (integralCoefficientULift_exists l L n).exists.choose_spec z
  have hqE (z : PbcIntegralRing l E) :
      integralCoefficientULift l E n (Ideal.Quotient.mk _ z) =
        ULift.up (Ideal.Quotient.mk _ z.down) :=
    (integralCoefficientULift_exists l E n).exists.choose_spec z
  rw [hqL]
  change ULift.up _ = ULift.up
    (integralScalarQuotientMap l E L ι n
      ((integralCoefficientULift l E n (Ideal.Quotient.mk _ x)).down))
  rw [hqE]
  rfl

private theorem detailedLevel_scalar (W : Scheme.{u}) (n : ℕ) :
    (adicLisseForget W).map
        (AdicCoefficients.coefficientMap W (pbcScalarQuotientMap l E L ι n)) ≫
      (integralDetailedLevelComparison W l L n).hom =
    (integralDetailedLevelComparison W l E n).hom ≫
      (adicLisseForget W).map (integralScalarQuotientSheafMap l E L ι W n) := by
  let F := adicLisseForget W
  let C := constantSheaf (ProEt.topology W) CommRingCat.{u + 1}
  let eE := pbcLevelConstantComparison W (pbcIntegralDatum l E) n
  let eL := pbcLevelConstantComparison W (pbcIntegralDatum l L) n
  have hc : AdicCoefficients.coefficientMap W (pbcScalarQuotientMap l E L ι n) ≫
        eL.inv = eE.inv ≫ C.map (CommRingCat.ofHom (pbcScalarQuotientMap l E L ι n)) := by
    apply (Iso.comp_inv_eq eL).mpr
    rw [Category.assoc]
    exact ((Iso.inv_comp_eq eE).mpr (levelConstant_scalar l E L ι W n)).symm
  change F.map _ ≫ F.map (eL.inv ≫ C.map _) =
    F.map (eE.inv ≫ C.map _) ≫ F.map _
  simp only [← F.map_comp]
  apply congrArg F.map
  rw [← Category.assoc, hc, Category.assoc, quotientScalar_square l E L ι W n,
    ← Category.assoc]

private theorem coefficientScalar_square (W : Scheme.{u}) :
    (purCoefficientIso l E W).hom ≫ integralCompletedScalarMap l E L ι W =
      pbcScalarCoefficientMap l E L ι W ≫ (purCoefficientIso l L W).hom := by
  let F := adicLisseForget W
  have hp (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      (n : ℕ) :
      F.map (purCoefficientIso l A W).hom ≫
          limit.π (integralCoefficientSheafSystem l A W) (Opposite.op n) =
        F.map (pbcAdicProjection W (pbcIntegralDatum l A) n) ≫
          (integralDetailedLevelComparison W l A n).hom := by
    have h := congrArg Iso.hom (purCoefficientIso_existsUnique l A W).exists.choose_spec
    change F.map (purCoefficientIso l A W).hom =
      (integralDetailedCoefficientComparison W l A).hom at h
    rw [h]
    exact (integralDetailedCoefficientComparison_exists W l A).exists.choose_spec n
  apply F.map_injective
  apply limit.hom_ext
  intro n
  change (F.map (purCoefficientIso l E W).hom ≫
      F.map (integralCompletedScalarMap l E L ι W)) ≫ limit.π _ n =
    (F.map (pbcScalarCoefficientMap l E L ι W) ≫
      F.map (purCoefficientIso l L W).hom) ≫ limit.π _ n
  have hg := congrArg F.map
    ((integralCompletedScalarMap_existsUnique l E L ι W).exists.choose_spec n.unop)
  change F.map (integralCompletedScalarMap l E L ι W) ≫ limit.π _ n =
    F.map (integralScalarRho l E L ι W n.unop) at hg
  have hf := congrArg F.map
    ((pbcScalarCoefficientMap_exists l E L ι W).exists.choose_spec n.unop)
  simp only [F.map_comp] at hf
  change F.map (pbcScalarCoefficientMap l E L ι W) ≫ F.map (pbcAdicProjection W
      (pbcIntegralDatum l L) n.unop) = _ at hf
  rw [Category.assoc, Category.assoc, hg, hp L n.unop]
  rw [← Category.assoc, hf, Category.assoc, detailedLevel_scalar l E L ι W n.unop]
  change F.map (purCoefficientIso l E W).hom ≫
      F.map (completedIntegralCommRingProjectionUnrestricted l E W n.unop ≫
        integralScalarQuotientSheafMap l E L ι W n.unop) = _
  rw [F.map_comp, ← Category.assoc]
  change (F.map (purCoefficientIso l E W).hom ≫
      limit.π (integralCoefficientSheafSystem l E W) n) ≫ F.map _ = _
  rw [hp E n.unop, Category.assoc]

attribute [local irreducible] completedAdicChange
  completedIntegralCommRingSheafUnrestricted
  completedAdicChangeData integralDetailedCoefficientComparison integralCompletedScalarMap
  pbcScalarCoefficientMap purCoefficientIso

private theorem ordinaryScalarAdjunction (W : Scheme.{u}) :
    ∃ a : integralOrdinaryScalar l E L ι W ⊣
        pbcRestrict (integralCompletedScalarMap l E L ι W),
      ∀ (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = purRawTensorSection l E L ι W M U 1 x := by
  have h : ∀ M, (integralOrdinaryScalar l E L ι W).obj M =
      SheafOfModules.changeOfRings (integralCompletedScalarMap l E L ι W) M :=
    (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose
  obtain ⟨_, _, ha⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (integralCompletedScalarMap l E L ι W)
  obtain ⟨a, hn⟩ := ha (integralOrdinaryScalar l E L ι W) h
    (fun f ↦ (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose_spec.choose f)
  refine ⟨a, ?_⟩
  intro M U x
  have hh := hn M _ (eqToHom (h M).symm) U x
  have hi : eqToHom (h M) ≫ eqToHom (h M).symm = 𝟙 _ := by simp
  rw [hi, Adjunction.homEquiv_id] at hh
  exact hh

private theorem rawTensor_smul (W : Scheme.{u}) (M : integralTowerModules l E W)
    (U : W.ProEtᵒᵖ) (s z : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
    (x : M.val.obj U) :
    purRawTensorSection l E L ι W M U (s * z) x =
      s • purRawTensorSection l E L ι W M U z x :=
  normalizedTensor_smul W (integralCompletedScalarMap l E L ι W) M _
    ((integralOrdinaryScalarWitness l E L ι W).choose_spec.choose M) U s z x

attribute [local irreducible] purRawTensorSection pbcTensorSection completedAdicChangeTensor

private theorem restrict_map_apply (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S)
    {M N : pbcModules W S} (k : M ⟶ N) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrict φ).map k).val.app U x = k.val.app U x := rfl

private theorem coefficientRestrictionAdjunction (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (c : R ≅ S) :
    ∃ a : pbcRestrict c.inv ⊣ pbcRestrict c.hom,
      ∀ (M : pbcModules W R) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = x := by
  refine ⟨(restrictionEquivalence ((adicLisseForget W).mapIso c.symm)).toAdjunction, ?_⟩
  intro M U x
  exact restrictionEquivalence_unit ((adicLisseForget W).mapIso c.symm) M U x

private theorem ordinaryScalarUnitComparison
    (W : Scheme.{u}) {R S R' S' : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (cE : R ≅ R') (cL : S ≅ S') (f : R ⟶ S) (g : R' ⟶ S')
    (hfg : cE.hom ≫ g = f ≫ cL.hom)
    (I : pbcModules W R' ⥤ pbcModules W S')
    (τ : ∀ (M : pbcModules W R') (U : W.ProEtᵒᵖ),
      S'.obj.obj U → M.val.obj U → (I.obj M).val.obj U)
    (aI : I ⊣ pbcRestrict g)
    (hI : ∀ (M : pbcModules W R') (U : W.ProEtᵒᵖ) (x : M.val.obj U),
      (aI.unit.app M).val.app U x = τ M U 1 x)
    (aG : pbcRestrict cE.inv ⊣ pbcRestrict cE.hom)
    (hG : ∀ (M : pbcModules W R) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
      (aG.unit.app M).val.app U x = x)
    (aH : pbcRestrict cL.inv ⊣ pbcRestrict cL.hom)
    (hH : ∀ (M : pbcModules W S) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
      (aH.unit.app M).val.app U x = x) :
    ∃ a : pbcExtend f ⋙ pbcRestrict cL.inv ⊣
        pbcRestrict g ⋙ pbcRestrict cE.hom,
      ∃ e : pbcExtend f ⋙ pbcRestrict cL.inv ≅ pbcRestrict cE.inv ⋙ I,
        (∀ (M : pbcModules W R) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
          (e.hom.app M).val.app U (pbcTensorSection f M U 1 x) =
            τ ((pbcRestrict cE.inv).obj M) U 1 x) ∧
        (∀ (M : pbcModules W R) (N : pbcModules W S')
          (k : (pbcExtend f ⋙ pbcRestrict cL.inv).obj M ⟶ N)
          (U : W.ProEtᵒᵖ) (x : M.val.obj U),
          (a.homEquiv M N k).val.app U x =
            k.val.app U (pbcTensorSection f M U 1 x)) := by
  let F := pbcExtend f
  let G := pbcRestrict cE.inv
  let H := pbcRestrict cL.inv
  let χ := f ≫ cL.hom
  obtain ⟨r1, hr1, _⟩ := pbcRestrictComp_exists f cL.hom χ rfl
  obtain ⟨r2, hr2, _⟩ := pbcRestrictComp_exists cE.hom g χ
    hfg
  let r : pbcRestrict cL.hom ⋙ pbcRestrict f ≅
      pbcRestrict g ⋙ pbcRestrict cE.hom := r1 ≪≫ r2.symm
  have hr (M : pbcModules W S') (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
      (r.hom.app M).val.app U x = x := by
    change (r2.inv.app M).val.app U ((r1.hom.app M).val.app U x) = x
    rw [hr1]
    have hh := hr2 M U ((r2.inv.app M).val.app U x)
    have hi := congrArg
      (fun k ↦ k.val.app U (show ((pbcRestrict χ).obj M).val.obj U from x))
      (r2.inv_hom_id_app M)
    exact hh.symm.trans hi
  clear_value r
  let a1 := ((pbcScalarAdjunction f).comp aH).ofNatIsoRight r
  let a2 := aG.comp aI
  have ha1 (M : pbcModules W R)
      (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
      (a1.unit.app M).val.app U x = pbcTensorSection f M U 1 x := by
    have hh : a1.unit.app M =
        ((pbcScalarAdjunction f).comp aH).unit.app M ≫
          r.hom.app ((F ⋙ H).obj M) := by
      rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply,
        Adjunction.homEquiv_id]
    rw [hh]
    change (r.hom.app _).val.app U
      ((((pbcScalarAdjunction f).comp aH).unit.app M).val.app U x) = _
    rw [hr, Adjunction.comp_unit_app]
    change ((aH.unit.app _).val.app U
      (((pbcScalarAdjunction f).unit.app M).val.app U x)) = _
    rw [hH]
    exact (pbcScalarAdjunction_exists f).exists.choose_spec M U x
  have ha2 (M : pbcModules W R)
      (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
      (a2.unit.app M).val.app U x =
        τ (G.obj M) U 1 x := by
    rw [Adjunction.comp_unit_app]
    change (aI.unit.app (G.obj M)).val.app U ((aG.unit.app M).val.app U x) = _
    rw [hG, hI]
  clear_value a1 a2
  have hAdj (M : pbcModules W R) (N : pbcModules W S')
      (k : (F ⋙ H).obj M ⟶ N) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
      (a1.homEquiv M N k).val.app U x = k.val.app U (pbcTensorSection f M U 1 x) := by
    rw [Adjunction.homEquiv_unit, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply, CategoryTheory.Functor.comp_map]
    exact (restrict_map_apply W cE.hom ((pbcRestrict g).map k) U _).trans
      ((restrict_map_apply W g k U _).trans
        (congrArg (fun z ↦ k.val.app U z) (ha1 M U x)))
  let e := Adjunction.leftAdjointUniq a1 a2
  have hu (M : pbcModules W R)
      (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
      (e.hom.app M).val.app U (pbcTensorSection f M U 1 x) =
        τ (G.obj M) U 1 x := by
    have h := congrArg (fun k ↦ k.val.app U x)
      (Adjunction.homEquiv_leftAdjointUniq_hom_app a1 a2 M)
    exact (hAdj M _ (e.hom.app M) U x).symm.trans (h.trans (ha2 M U x))
  exact ⟨a1, e, hu, hAdj⟩

private theorem ordinaryScalarComparison
    (W : Scheme.{u}) {R S R' S' : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (cE : R ≅ R') (cL : S ≅ S') (f : R ⟶ S) (g : R' ⟶ S')
    (hfg : cE.hom ≫ g = f ≫ cL.hom)
    (I : pbcModules W R' ⥤ pbcModules W S')
    (τ : ∀ (M : pbcModules W R') (U : W.ProEtᵒᵖ),
      S'.obj.obj U → M.val.obj U → (I.obj M).val.obj U)
    (aI : I ⊣ pbcRestrict g)
    (hI : ∀ (M : pbcModules W R') (U : W.ProEtᵒᵖ) (x : M.val.obj U),
      (aI.unit.app M).val.app U x = τ M U 1 x)
    (hsmul : ∀ (M : pbcModules W R') (U : W.ProEtᵒᵖ) (s z : S'.obj.obj U)
      (x : M.val.obj U), τ M U (s * z) x = s • τ M U z x)
    (aG : pbcRestrict cE.inv ⊣ pbcRestrict cE.hom)
    (hG : ∀ (M : pbcModules W R) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
      (aG.unit.app M).val.app U x = x)
    (aH : pbcRestrict cL.inv ⊣ pbcRestrict cL.hom)
    (hH : ∀ (M : pbcModules W S) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
      (aH.unit.app M).val.app U x = x) :
    ∃! e : pbcExtend f ⋙ pbcRestrict cL.inv ≅ pbcRestrict cE.inv ⋙ I,
      ∀ (M : pbcModules W R) (U : W.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U),
        (e.hom.app M).val.app U (pbcTensorSection f M U a x) =
          τ ((pbcRestrict cE.inv).obj M) U (cL.hom.hom.app U a) x := by
  let F := pbcExtend f
  let G := pbcRestrict cE.inv
  let H := pbcRestrict cL.inv
  obtain ⟨a, e, hu, hAdj⟩ := ordinaryScalarUnitComparison W cE cL f g hfg I τ
    aI hI aG hG aH hH
  refine ⟨e, ?_, ?_⟩
  · intro M U a x
    have hs : pbcTensorSection f M U (a * 1) x = a • pbcTensorSection f M U 1 x := by
      unfold pbcTensorSection
      exact completedTensor_smul W f M U a 1 x
    rw [mul_one] at hs
    have hcancel : cL.inv.hom.app U (cL.hom.hom.app U a) = a :=
      ConcreteCategory.congr_hom
        (congrArg (fun k ↦ k.hom.app U) cL.hom_inv_id) a
    have ht : pbcTensorSection f M U a x =
        (cL.hom.hom.app U a) •
          (show (H.obj (F.obj M)).val.obj U from pbcTensorSection f M U 1 x) := by
      change pbcTensorSection f M U a x =
        (cL.inv.hom.app U (cL.hom.hom.app U a)) • pbcTensorSection f M U 1 x
      rw [hcancel]
      exact hs
    have hraw := hsmul (G.obj M) U
      (cL.hom.hom.app U a) 1 x
    rw [mul_one] at hraw
    calc
      (e.hom.app M).val.app U (pbcTensorSection f M U a x) =
          (e.hom.app M).val.app U ((cL.hom.hom.app U a) •
            (show (H.obj (F.obj M)).val.obj U from
              pbcTensorSection f M U 1 x)) := congrArg _ ht
      _ = (cL.hom.hom.app U a) •
          (e.hom.app M).val.app U (pbcTensorSection f M U 1 x) :=
        ((e.hom.app M).val.app U).hom.map_smul _ _
      _ = (cL.hom.hom.app U a) •
          τ (G.obj M) U 1 x :=
        congrArg (fun z ↦ (cL.hom.hom.app U a) • z) (hu M U x)
      _ = τ (G.obj M) U
          (cL.hom.hom.app U a) x := hraw.symm
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (a.homEquiv M _).injective
    ext U x
    rw [hAdj, hAdj, hu, he']
    rw [map_one]

/-- Coefficient-model transport commutes with ordinary scalar tensor by the specified
balanced tensor map, on every generator.
Source: Stacks 03EK, Bhatt--Scholze 6.8.2(1)
(blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: every finite projection identifies the scalar coefficient square. Thus its
completed square commutes. Send a tensor x to the same tensor with a transported
by the completed ring isomorphism. The inverse uses the inverse ring isomorphism.
Balancedness, restriction compatibility and the inverse identities hold on tensor
generators and descend through sheafification. Local generation proves uniqueness. -/
theorem purOrdinaryScalarModel_existsUnique (W : Scheme.{u}) :
    ∃! e : pbcExtend (pbcScalarCoefficientMap l E L ι W) ⋙
        purOrdinaryCoefficientModel l L W ≅
      purOrdinaryCoefficientModel l E W ⋙ integralOrdinaryScalar l E L ι W,
      ∀ (M : pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E)))
        (U : W.ProEtᵒᵖ) (a : (pbcAdicCompletion W (pbcIntegralDatum l L)).obj.obj U)
        (x : M.val.obj U),
        (e.hom.app M).val.app U (pbcTensorSection (pbcScalarCoefficientMap l E L ι W) M U a x) =
          purRawTensorSection l E L ι W ((purOrdinaryCoefficientModel l E W).obj M) U
            ((purCoefficientIso l L W).hom.hom.app U a) x := by
  obtain ⟨aI, hI⟩ := ordinaryScalarAdjunction l E L ι W
  obtain ⟨aG, hG⟩ := coefficientRestrictionAdjunction W (purCoefficientIso l E W)
  obtain ⟨aH, hH⟩ := coefficientRestrictionAdjunction W (purCoefficientIso l L W)
  exact ordinaryScalarComparison W (purCoefficientIso l E W) (purCoefficientIso l L W)
    (pbcScalarCoefficientMap l E L ι W) (integralCompletedScalarMap l E L ι W)
    (coefficientScalar_square l E L ι W) (integralOrdinaryScalar l E L ι W)
    (purRawTensorSection l E L ι W) aI hI (rawTensor_smul l E L ι W) aG hG aH hH

/-- The ordinary scalar comparison, uniquely fixed on all tensor generators.
Source: Stacks 03EK (blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purOrdinaryScalarModel (W : Scheme.{u}) :=
  (purOrdinaryScalarModel_existsUnique l E L ι W).exists.choose

/-- Termwise transport of the specified ordinary balanced tensor comparison.
Source: Stacks 06YY (blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purScalarModelComplexIso (W : Scheme.{u}) :
    (pbcExtend (pbcScalarCoefficientMap l E L ι W)).mapHomologicalComplex (.up ℤ) ⋙
        (purOrdinaryCoefficientModel l L W).mapHomologicalComplex (.up ℤ) ≅
      (purOrdinaryCoefficientModel l E W).mapHomologicalComplex (.up ℤ) ⋙
        (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
    (purOrdinaryScalarModel l E L ι W) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (F := purOrdinaryCoefficientModel l E W)
      (G := integralOrdinaryScalar l E L ι W) (Iso.refl _) (.up ℤ)).symm

private theorem legacyDerivedSquare_factors
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : A ⥤ B} {H : B ⥤ D} {G : A ⥤ C} {I : C ⥤ D}
    [F.Additive] [H.Additive] [G.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : F ⋙ H ≅ G ⋙ I) (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
        I.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
        I.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) =
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (G ⋙ I)) (.up ℤ)).inv.app P) := by
  have hi : (Functor.mapDerivedCategoryCompIso F H).inv.app (DerivedCategory.Q.obj P) ≫
      (F ⋙ H).mapDerivedCategoryFactors.hom.app P =
    H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
    apply (cancel_epi
      ((Functor.mapDerivedCategoryCompIso F H).hom.app (DerivedCategory.Q.obj P))).mp
    rw [Iso.hom_inv_id_app_assoc]
    exact (Functor.mapDerivedCategoryCompIso_hom_app_factors F H P).symm
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Category.assoc, hi, Category.assoc]
  congr 2
  apply congrArg DerivedCategory.Q.map
  ext i
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
    Iso.refl_inv, NatTrans.id_app]
  exact (Category.comp_id _).symm

private def ordinaryRestrictionSquare :
    (Mod.comap b.hom : Mod C S' ⥤ Mod C S) ⋙ Mod.comap f ≅
      Mod.comap g ⋙ Mod.comap a.hom :=
  (Mod.comapComp f b.hom).symm ≪≫ Mod.comapCongr sq.symm ≪≫
    Mod.comapComp a.hom g

private theorem ordinaryRestrictionSquare_hom (N : Mod C S') :
    ((ordinaryRestrictionSquare a b f g sq).hom.app N).hom = 𝟙 N.X := by
  simp only [ordinaryRestrictionSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Mod.comp_hom', Mod.comapComp_inv_app_hom, Mod.comapCongr_hom_app_hom,
    Mod.comapComp_hom_app_hom]
  change (𝟙 N.X ≫ 𝟙 N.X ≫ 𝟙 N.X : N.X ⟶ N.X) = 𝟙 N.X
  simp only [Category.id_comp]

/-- The tensor comparison of two isomorphic coefficient presentations is uniquely
normalized by `1 tensor x`. This is an equality of maps of underlying objects,
so it applies to sheafified tensors without assuming that sections are pure tensors.

Source: Stacks 03EK; latest blueprint `fix-prop-adjunctions.proof.md`, Step 1.
(blueprint: def-pur-completed-coefficient-presentation-transport).

Proof: compose the tensor/restriction adjunction with inverse restriction on each
side. The coefficient square identifies the two right adjoints by identity maps
on underlying objects. Uniqueness of left adjoints gives the comparison. Its unit
identity gives the displayed normalization. Conversely, the adjunction Hom
bijection identifies any two normalized maps; hence the isomorphism is unique. -/
theorem purCondensedOrdinaryScalarModel_existsUnique :
    ∃! e : Mod.extendScalars f ⋙ Mod.comap (inv b.hom) ≅
        Mod.comap (inv a.hom) ⋙ Mod.extendScalars g,
      ∀ M : Mod C R,
        Mod.extendUnitHom f M ≫ (e.hom.app M).hom =
          Mod.extendUnitHom g ((Mod.comap (inv a.hom)).obj M) := by
  let aG : (Mod.comap (inv a.hom) : Mod C R ⥤ Mod C R') ⊣ Mod.comap a.hom :=
    (Mod.comapEquivalenceOfIsIso a.hom).symm.toAdjunction
  let aH : (Mod.comap (inv b.hom) : Mod C S ⥤ Mod C S') ⊣ Mod.comap b.hom :=
    (Mod.comapEquivalenceOfIsIso b.hom).symm.toAdjunction
  let r := ordinaryRestrictionSquare a b f g sq
  let a1 := ((Mod.extendRestrictAdjunction f).comp aH).ofNatIsoRight r
  let a2 := aG.comp (Mod.extendRestrictAdjunction g)
  have hG (M : Mod C R) : (aG.unit.app M).hom = 𝟙 M.X :=
    Mod.comapEquivalenceOfIsIso_counitInv_app_hom a.hom M
  have hH (N : Mod C S) : (aH.unit.app N).hom = 𝟙 N.X :=
    Mod.comapEquivalenceOfIsIso_counitInv_app_hom b.hom N
  have h1 (M : Mod C R) : (a1.unit.app M).hom = Mod.extendUnitHom f M := by
    have he : a1.unit.app M =
        ((Mod.extendRestrictAdjunction f).comp aH).unit.app M ≫ r.hom.app _ := by
      rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply,
        Adjunction.homEquiv_id]
    erw [he, Mod.comp_hom', ordinaryRestrictionSquare_hom, Category.comp_id]
    rw [Adjunction.comp_unit_app, Mod.comp_hom']
    change ((Mod.extendRestrictAdjunction f).unit.app M).hom ≫
      (aH.unit.app ((Mod.extendScalars f).obj M)).hom = _
    rw [hH]
    exact (Category.comp_id _).trans (Mod.extendRestrictAdjunction_unit_app_hom f M)
  have h2 (M : Mod C R) : (a2.unit.app M).hom =
      Mod.extendUnitHom g ((Mod.comap (inv a.hom)).obj M) := by
    rw [Adjunction.comp_unit_app, Mod.comp_hom', hG, Mod.comap_map_hom]
    dsimp only [Mod.comap, Functor.id_obj]
    rw [Category.id_comp, Mod.extendRestrictAdjunction_unit_app_hom]
  have hAdj (M : Mod C R) (N : Mod C S')
      (k : (Mod.extendScalars f ⋙ Mod.comap (inv b.hom)).obj M ⟶ N) :
      (a1.homEquiv M N k).hom = Mod.extendUnitHom f M ≫ k.hom := by
    rw [Adjunction.homEquiv_unit, Mod.comp_hom', h1]
    rfl
  let e := a1.leftAdjointUniq a2
  have he (M : Mod C R) : Mod.extendUnitHom f M ≫ (e.hom.app M).hom =
      Mod.extendUnitHom g ((Mod.comap (inv a.hom)).obj M) := by
    have h := congrArg Mod.Hom.hom
      (Adjunction.homEquiv_leftAdjointUniq_hom_app a1 a2 M)
    exact (hAdj M _ (e.hom.app M)).symm.trans (h.trans (h2 M))
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (a1.homEquiv M _).injective
  apply Mod.hom_ext
  rw [hAdj, hAdj, he', he]

/-- The ordinary scalar comparison, fixed by its tensor-unit equation.
Source: Stacks 03EK
(blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purCondensedOrdinaryScalarModel :
    Mod.extendScalars f ⋙ Mod.comap (inv b.hom) ≅ Mod.comap (inv a.hom) ⋙ Mod.extendScalars g :=
  (purCondensedOrdinaryScalarModel_existsUnique a b f g sq).exists.choose

/-- The chosen comparison retains its tensor-unit normalization.
Source: Stacks 03EK
(blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: this is the property of the uniquely specified comparison. -/
theorem purCondensedOrdinaryScalarModel_unit (M : Mod C R) :
    Mod.extendUnitHom f M ≫ ((purCondensedOrdinaryScalarModel a b f g sq).hom.app M).hom =
      Mod.extendUnitHom g ((Mod.comap (inv a.hom)).obj M) := by
  exact (purCondensedOrdinaryScalarModel_existsUnique a b f g sq).exists.choose_spec M

/-- The comparison sends every scalar tensor to the tensor with transported scalar.
The displayed map is the coequalizer projection from the unbalanced tensor, so
this statement includes all local pure-tensor formulas on a sheaf site.
Source: Stacks 03EK
(blueprint: def-pur-completed-coefficient-presentation-transport).

Proof: write the tensor projection as the scalar action on the tensor unit.
Linearity of the comparison transports that action along the coefficient
isomorphism. Its tensor-unit equation then gives the target projection. -/
theorem purCondensedOrdinaryScalarModel_tensor (M : Mod C R) :
    Mod.extendπ f M ≫ ((purCondensedOrdinaryScalarModel a b f g sq).hom.app M).hom =
      b.hom ▷ M.X ≫ Mod.extendπ g ((Mod.comap (inv a.hom)).obj M) := by
  let k := (purCondensedOrdinaryScalarModel a b f g sq).hom.app M
  have hk := Mod.act_hom k
  change ((inv b.hom) ▷ (Mod.extendScalarsObj f M).X ≫
      Mod.act (Mod.extendScalarsObj f M).X) ≫ k.hom =
    S' ◁ k.hom ≫ Mod.act ((Mod.extendScalars g).obj
      ((Mod.comap (inv a.hom)).obj M)).X at hk
  have h := congrArg (fun t ↦ b.hom ▷ (Mod.extendScalarsObj f M).X ≫ t) hk
  rw [← Category.assoc, ← Category.assoc, ← comp_whiskerRight, IsIso.hom_inv_id,
    id_whiskerRight, Category.id_comp] at h
  rw [← Mod.whiskerLeft_extendUnitHom_smul' f M, Category.assoc, h,
    ← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    purCondensedOrdinaryScalarModel_unit a b f g sq M]
  change S ◁ Mod.extendUnitHom g ((Mod.comap (inv a.hom)).obj M) ≫
    b.hom ▷ (Mod.extendScalarsObj g ((Mod.comap (inv a.hom)).obj M)).X ≫
    Mod.act (Mod.extendScalarsObj g ((Mod.comap (inv a.hom)).obj M)).X =
    b.hom ▷ ((Mod.comap (inv a.hom)).obj M).X ≫
    Mod.extendπ g ((Mod.comap (inv a.hom)).obj M)
  rw [whisker_exchange_assoc, Mod.whiskerLeft_extendUnitHom_smul']

private theorem derivedSquare_factors
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : A ⥤ B} {H : B ⥤ D} {G : A ⥤ C} {I : C ⥤ D}
    [F.Additive] [H.Additive] [G.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : F ⋙ H ≅ G ⋙ I) (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
        I.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
        I.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) =
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (G ⋙ I)) (.up ℤ)).inv.app P) := by
  have hi : (Functor.mapDerivedCategoryCompIso F H).inv.app (DerivedCategory.Q.obj P) ≫
      (F ⋙ H).mapDerivedCategoryFactors.hom.app P =
    H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
    apply (cancel_epi
      ((Functor.mapDerivedCategoryCompIso F H).hom.app (DerivedCategory.Q.obj P))).mp
    rw [Iso.hom_inv_id_app_assoc]
    exact (Functor.mapDerivedCategoryCompIso_hom_app_factors F H P).symm
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Category.assoc, hi, Category.assoc]
  congr 2
  apply congrArg DerivedCategory.Q.map
  ext i
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
    Iso.refl_inv, NatTrans.id_app]
  exact (Category.comp_id _).symm

/-- Termwise transport of the uniquely normalized tensor comparison.
Source: Stacks 06YY
(blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purCondensedScalarModelComplexIso :
    (Mod.extendScalars f).mapHomologicalComplex (.up ℤ) ⋙
        (Mod.comap (inv b.hom)).mapHomologicalComplex (.up ℤ) ≅
      (Mod.comap (inv a.hom)).mapHomologicalComplex (.up ℤ) ⋙
        (Mod.extendScalars g).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (purCondensedOrdinaryScalarModel a b f g sq) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (F := Mod.comap (inv a.hom)) (G := Mod.extendScalars g) (Iso.refl _) (.up ℤ)).symm

/-- The derived scalar comparison is uniquely fixed on every complex representative.
Source: Stacks 06YY; latest blueprint `fix-prop-adjunctions.proof.md`, Step 1.
(blueprint: def-pur-completed-coefficient-presentation-transport).

Proof: descend the ordinary comparison through the exact functors and their
localization factors. The composition-factor equations give the formula on
complexes. Cancel the invertible factors and use natural-transformation
extensionality for the localization to prove uniqueness. This is the localization
argument of the previous proof, with coefficient module objects in place of the
two old presentations. -/
theorem purCondensedScalarModelExact_existsUnique :
    ∃! e : (Mod.extendScalars f).mapDerivedCategory ⋙
        (Mod.comap (inv b.hom)).mapDerivedCategory ≅
      (Mod.comap (inv a.hom)).mapDerivedCategory ⋙ (Mod.extendScalars g).mapDerivedCategory,
      ∀ P : CochainComplex (Mod C R) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (Mod.extendScalars g).mapDerivedCategory.map
            ((Mod.comap (inv a.hom)).mapDerivedCategoryFactors.hom.app P) ≫
          (Mod.extendScalars g).mapDerivedCategoryFactors.hom.app
            (((Mod.comap (inv a.hom)).mapHomologicalComplex (.up ℤ)).obj P) =
        (Mod.comap (inv b.hom)).mapDerivedCategory.map
            ((Mod.extendScalars f).mapDerivedCategoryFactors.hom.app P) ≫
          (Mod.comap (inv b.hom)).mapDerivedCategoryFactors.hom.app
            (((Mod.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((purCondensedScalarModelComplexIso a b f g sq).hom.app P) := by
  let e := Functor.mapDerivedCategorySquareIso (purCondensedOrdinaryScalarModel a b f g sq)
  have he (P : CochainComplex (Mod C R) ℤ) :
      e.hom.app (DerivedCategory.Q.obj P) ≫
        (Mod.extendScalars g).mapDerivedCategory.map
          ((Mod.comap (inv a.hom)).mapDerivedCategoryFactors.hom.app P) ≫
        (Mod.extendScalars g).mapDerivedCategoryFactors.hom.app
          (((Mod.comap (inv a.hom)).mapHomologicalComplex (.up ℤ)).obj P) =
      (Mod.comap (inv b.hom)).mapDerivedCategory.map
          ((Mod.extendScalars f).mapDerivedCategoryFactors.hom.app P) ≫
        (Mod.comap (inv b.hom)).mapDerivedCategoryFactors.hom.app
          (((Mod.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((purCondensedScalarModelComplexIso a b f g sq).hom.app P) := by
    exact derivedSquare_factors (purCondensedOrdinaryScalarModel a b f g sq) P
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (Mod C R) (.up ℤ))
  intro P
  exact (cancel_mono ((Mod.extendScalars g).mapDerivedCategory.map
    ((Mod.comap (inv a.hom)).mapDerivedCategoryFactors.hom.app P) ≫
    (Mod.extendScalars g).mapDerivedCategoryFactors.hom.app
      (((Mod.comap (inv a.hom)).mapHomologicalComplex (.up ℤ)).obj P))).mp
        ((he' P).trans (he P).symm)

/-- The derived balanced-tensor comparison between the coefficient presentations.
Source: Stacks 06YY
(blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purCondensedScalarModelExact :
    (Mod.extendScalars f).mapDerivedCategory ⋙ (Mod.comap (inv b.hom)).mapDerivedCategory ≅
      (Mod.comap (inv a.hom)).mapDerivedCategory ⋙ (Mod.extendScalars g).mapDerivedCategory :=
  (purCondensedScalarModelExact_existsUnique a b f g sq).exists.choose

/-- The actual total left-derived tensor comparison, normalized by the universal
comparison from total derivation to exact localization.
Source: latest blueprint `def-weil-derived-pullback-tensor-hom`; Stacks 06YY.
(blueprint: def-pur-completed-coefficient-presentation-transport).

Proof: compose the universal exact/left-derived comparison on the source,
the normalized exact square, and the inverse universal comparison on the target.
The inverse laws give the displayed equation. Conversely that equation determines
every component after cancellation of its final isomorphism. -/
theorem purCondensedScalarModel_existsUnique :
    ∃! e : (Mod.extendScalars f).leftDerivedFunctor ⋙
        (Mod.comap (inv b.hom)).mapDerivedCategory ≅
      (Mod.comap (inv a.hom)).mapDerivedCategory ⋙ (Mod.extendScalars g).leftDerivedFunctor,
      ∀ K : DerivedCategory (Mod C R),
        e.hom.app K ≫
          (Mod.extendScalars g).leftDerivedFunctorIsoMapDerivedCategory.hom.app
            ((Mod.comap (inv a.hom)).mapDerivedCategory.obj K) =
        (Mod.comap (inv b.hom)).mapDerivedCategory.map
            ((Mod.extendScalars f).leftDerivedFunctorIsoMapDerivedCategory.hom.app K) ≫
          (purCondensedScalarModelExact a b f g sq).hom.app K := by
  let e := isoWhiskerRight
      (Mod.extendScalars f).leftDerivedFunctorIsoMapDerivedCategory
      (Mod.comap (inv b.hom)).mapDerivedCategory ≪≫
    purCondensedScalarModelExact a b f g sq ≪≫
    isoWhiskerLeft (Mod.comap (inv a.hom)).mapDerivedCategory
      (Mod.extendScalars g).leftDerivedFunctorIsoMapDerivedCategory.symm
  have he (K : DerivedCategory (Mod C R)) :
      e.hom.app K ≫
          (Mod.extendScalars g).leftDerivedFunctorIsoMapDerivedCategory.hom.app
            ((Mod.comap (inv a.hom)).mapDerivedCategory.obj K) =
        (Mod.comap (inv b.hom)).mapDerivedCategory.map
            ((Mod.extendScalars f).leftDerivedFunctorIsoMapDerivedCategory.hom.app K) ≫
          (purCondensedScalarModelExact a b f g sq).hom.app K := by
    simp only [e, Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
      NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id_app]
    exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact (cancel_mono
    ((Mod.extendScalars g).leftDerivedFunctorIsoMapDerivedCategory.hom.app
      ((Mod.comap (inv a.hom)).mapDerivedCategory.obj K))).mp
    ((he' K).trans (he K).symm)

/-- The normalized comparison for actual total left-derived scalar extension.
Source: latest blueprint `def-weil-derived-pullback-tensor-hom`; Stacks 06YY.
(blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purCondensedScalarTransportModel :
    (Mod.extendScalars f).leftDerivedFunctor ⋙ (Mod.comap (inv b.hom)).mapDerivedCategory ≅
      (Mod.comap (inv a.hom)).mapDerivedCategory ⋙ (Mod.extendScalars g).leftDerivedFunctor :=
  (purCondensedScalarModel_existsUnique a b f g sq).exists.choose

/-- Change of presentation of a condensed coefficient ring on the actual pro-etale site.
Source: latest blueprint `fix-prop-adjunctions.proof.md`, Step 1.
(blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purCondensedCoefficientModel :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W)) ≌
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ' W)) :=
  let E := (Mod.comapEquivalenceOfIsIso (coefficientMap e.hom W)).symm
  letI : E.functor.Additive := inferInstanceAs
    (Mod.comap (inv (coefficientMap e.hom W))).Additive
  letI : E.inverse.Additive := inferInstanceAs
    (Mod.comap (coefficientMap e.hom W)).Additive
  E.mapDerivedCategory

/-- The coefficient equivalence preserves and reflects the actual bounded
constructible predicate, with no additional geometric bounds.
Source: latest blueprint `fix-prop-adjunctions.proof.md`, Step 1.
(blueprint: def-pur-completed-coefficient-presentation-transport).

Proof: inverse restriction commutes with cohomology, preserves finite presentations
and their stratifications, and preserves zero objects. Apply the same argument to
the inverse isomorphism; the restriction round trip identifies the original object. -/
theorem purCondensedCoefficientModel_bounded_predicate
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W))) :
    boundedConstructible (condensedRingObj Λ' W)
        ((purCondensedCoefficientModel W e).functor.obj K) ↔
      boundedConstructible (condensedRingObj Λ W) K := by
  exact boundedConstructible_comap_iso_iff (inv (coefficientMap e.hom W)) K

/-- Specialization to a commutative square of actual condensed coefficient rings.
The coefficient sheaves are literally `p_W^* Lambda`, and the scalar functors are
the existing total left-derived extensions on their module-object categories.
Exactness is required only of the two ordinary scalar functors, as for finite-free
coefficient extensions; there is no boundedness or flatness condition on an input complex.
Source: latest blueprint `fix-prop-adjunctions.proof.md`, Step 1, and
`def-weil-derived-pullback-tensor-hom`.
(blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purCondensedScalarModel
    {Γ Γ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Γ] [IsCommMonObj Γ] [MonObj Γ'] [IsCommMonObj Γ']
    (b : Γ ≅ Γ') [IsMonHom b.hom]
    (f : Λ ⟶ Γ) (g : Λ' ⟶ Γ') [IsMonHom f] [IsMonHom g]
    (sq : e.hom ≫ g = f ≫ b.hom)
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap f W))]
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap g W))] :
    (Mod.extendScalars (coefficientMap f W)).leftDerivedFunctor ⋙
        (Mod.comap (inv (coefficientMap b.hom W))).mapDerivedCategory ≅
      (Mod.comap (inv (coefficientMap e.hom W))).mapDerivedCategory ⋙
        (Mod.extendScalars (coefficientMap g W)).leftDerivedFunctor :=
  purCondensedScalarTransportModel (asIso (coefficientMap e.hom W)) (asIso (coefficientMap b.hom W))
    (coefficientMap f W) (coefficientMap g W) (by
      simpa only [asIso_hom, coefficientMap, Functor.map_comp] using
        congrArg (upperStarFromPoint W).map sq)

private theorem scalarExtension_exact (W : Scheme.{u}) :
    PreservesFiniteLimits (pbcExtend (pbcScalarCoefficientMap l E L ι W)) ∧
      PreservesFiniteColimits (pbcExtend (pbcScalarCoefficientMap l E L ι W)) := by
  let F := pbcExtend (pbcScalarCoefficientMap l E L ι W)
  let H := purOrdinaryCoefficientModel l L W
  have : H.IsEquivalence :=
    restriction_isEquivalence ((adicLisseForget W).mapIso (purCoefficientIso l L W).symm)
  have : PreservesFiniteLimits (F ⋙ H) :=
    preservesFiniteLimits_of_natIso (purOrdinaryScalarModel l E L ι W).symm
  have : PreservesFiniteColimits (F ⋙ H) :=
    preservesFiniteColimits_of_natIso (purOrdinaryScalarModel l E L ι W).symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F H,
    preservesFiniteColimits_of_reflects_of_preserves F H⟩

private theorem scalarDerivedComparison (W : Scheme.{u})
    [PreservesFiniteLimits (pbcExtend (pbcScalarCoefficientMap l E L ι W))]
    [PreservesFiniteColimits (pbcExtend (pbcScalarCoefficientMap l E L ι W))] :
    ∃ e : pbcEmbeddingAmbientTensor l E L ι W ≅
        (pbcExtend (pbcScalarCoefficientMap l E L ι W)).mapDerivedCategory,
      ∀ P : CochainComplex (pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E))) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (pbcExtend (pbcScalarCoefficientMap l E L ι W)).mapDerivedCategoryFactors.hom.app P =
            pbcComplexCounit (pbcScalarCoefficientMap l E L ι W) P := by
  have := (scalarExtension_exact l E L ι W).1
  have := (scalarExtension_exact l E L ι W).2
  let F := pbcExtend (pbcScalarCoefficientMap l E L ι W)
  let LF := pbcDerivedExtend (pbcScalarCoefficientMap l E L ι W)
  let ε := pbcExtensionCounit (pbcScalarCoefficientMap l E L ι W)
  let V := HomotopyCategory.quasiIso
    (pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E))) (.up ℤ)
  have : LF.IsLeftDerivedFunctor ε V := pbcDerivedExtension_universal _
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom V :=
    Functor.isLeftDerivedFunctor_of_inverts V _ F.mapDerivedCategoryFactorsh
  let e := Functor.leftDerivedNatIso LF F.mapDerivedCategory ε
    F.mapDerivedCategoryFactorsh.hom V (Iso.refl _)
  have he (P : HomotopyCategory
      (pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E))) (.up ℤ)) :
      e.hom.app (DerivedCategory.Qh.obj P) ≫
        F.mapDerivedCategoryFactorsh.hom.app P = ε.app P := by
    simpa only [e, Functor.leftDerivedNatIso_hom, Iso.refl_hom,
      NatTrans.id_app, Category.comp_id] using
      Functor.leftDerivedNatTrans_app LF F.mapDerivedCategory ε
        F.mapDerivedCategoryFactorsh.hom V (𝟙 _) P
  refine ⟨e, ?_⟩
  intro P
  unfold pbcComplexCounit
  rw [← he]
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  dsimp only [F, LF]
  simp only [Category.assoc, ← NatTrans.naturality_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app]
  exact congrArg (fun f ↦ e.hom.app (DerivedCategory.Q.obj P) ≫ f)
    (Category.comp_id (F.mapDerivedCategoryFactors.hom.app P)).symm

/-- Derived transport of the same scalar comparison, retaining the ordinary comparison
on every complex (finite-free scalar extension is exact).
Source: Stacks 06YY, 099N (blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: the model functors are exact identity-on-sections restrictions. Finite-free
scalar tensor is exact. On resolving complexes the universal derived tensor counit
is invertible, and the displayed conjugation of the ordinary tensor comparison
therefore gives the comparison. It descends through resolving quasi-isomorphisms.
Every object has a complex representative, so the result is invertible and unique. -/
theorem purScalarModel_existsUnique (W : Scheme.{u}) :
    ∃! e : pbcEmbeddingAmbientTensor l E L ι W ⋙ (purCoefficientModel l L W).functor ≅
        (purCoefficientModel l E W).functor ⋙ integralOrdinaryDerivedScalar l E L ι W,
      ∀ P : CochainComplex (pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E))) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (integralOrdinaryDerivedScalar l E L ι W).map
            ((purOrdinaryCoefficientModel l E W).mapDerivedCategoryFactors.hom.app P) ≫
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
            (((purOrdinaryCoefficientModel l E W).mapHomologicalComplex (.up ℤ)).obj P) =
        (purCoefficientModel l L W).functor.map
            (pbcComplexCounit (pbcScalarCoefficientMap l E L ι W) P) ≫
          (purOrdinaryCoefficientModel l L W).mapDerivedCategoryFactors.hom.app
            (((pbcExtend (pbcScalarCoefficientMap l E L ι W)).mapHomologicalComplex
              (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((purScalarModelComplexIso l E L ι W).hom.app P) := by
  have := (scalarExtension_exact l E L ι W).1
  have := (scalarExtension_exact l E L ι W).2
  obtain ⟨d, hd⟩ := scalarDerivedComparison l E L ι W
  let H := purOrdinaryCoefficientModel l L W
  let e := Functor.isoWhiskerRight d H.mapDerivedCategory ≪≫
    Functor.mapDerivedCategorySquareIso (purOrdinaryScalarModel l E L ι W)
  have hNorm (P : CochainComplex
      (pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E))) ℤ) :
      e.hom.app (DerivedCategory.Q.obj P) ≫
        (integralOrdinaryScalar l E L ι W).mapDerivedCategory.map
          ((purOrdinaryCoefficientModel l E W).mapDerivedCategoryFactors.hom.app P) ≫
        (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
          (((purOrdinaryCoefficientModel l E W).mapHomologicalComplex (.up ℤ)).obj P) =
      H.mapDerivedCategory.map (pbcComplexCounit (pbcScalarCoefficientMap l E L ι W) P) ≫
        H.mapDerivedCategoryFactors.hom.app
          (((pbcExtend (pbcScalarCoefficientMap l E L ι W)).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((purScalarModelComplexIso l E L ι W).hom.app P) := by
    change (H.mapDerivedCategory.map (d.hom.app (DerivedCategory.Q.obj P)) ≫
      (Functor.mapDerivedCategorySquareIso
        (purOrdinaryScalarModel l E L ι W)).hom.app (DerivedCategory.Q.obj P)) ≫ _ = _
    rw [Category.assoc]
    have h := congrArg
      (fun f ↦ H.mapDerivedCategory.map (d.hom.app (DerivedCategory.Q.obj P)) ≫ f)
      (legacyDerivedSquare_factors (purOrdinaryScalarModel l E L ι W) P)
    refine h.trans ?_
    rw [← Category.assoc, ← H.mapDerivedCategory.map_comp, hd]
    rfl
  refine ⟨e, hNorm, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E))) (.up ℤ))
  intro P
  exact (cancel_mono ((integralOrdinaryDerivedScalar l E L ι W).map
    ((purOrdinaryCoefficientModel l E W).mapDerivedCategoryFactors.hom.app P) ≫
    (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
      (((purOrdinaryCoefficientModel l E W).mapHomologicalComplex (.up ℤ)).obj P))).mp
        ((he' P).trans (hNorm P).symm)

/-- The actual derived balanced-tensor comparison between the coefficient models.
Source: Stacks 06YY (blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purScalarModel (W : Scheme.{u}) := (purScalarModel_existsUnique l E L ι W).exists.choose

end WeilConjectures
