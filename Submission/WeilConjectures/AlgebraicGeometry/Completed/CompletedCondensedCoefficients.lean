/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Category.Profinite.AsLimit
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Submission.WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Types.Filtered
import all Submission.WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all Submission.WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all Submission.WeilConjectures.ConstructibleSheaf.FreeLifting
import Submission.WeilConjectures.CategoryTheory.SheafTensor
import Submission.WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Submission.WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.EssentiallySmall
import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Submission.WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Submission.WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.Topology.Algebra.Ring.Compact
import all Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import all Submission.WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import Submission.WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
import all Submission.WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import all Submission.WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import all Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all Mathlib.Algebra.Ring.Subring.Basic
import all Mathlib.Algebra.Ring.Pi
import all Mathlib.Topology.Homeomorph.Defs
import all Mathlib.Topology.Connected.TotallyDisconnected
import all Mathlib.Topology.Compactness.Compact
import all Submission.WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.Topology.Homeomorph.Lemmas
import all Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all Submission.WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all Submission.WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import all Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import all Submission.WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Submission.WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all Submission.WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import all Mathlib.AlgebraicGeometry.Limits
import all Mathlib.CategoryTheory.FintypeCat
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Submission.WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.CategoryTheory.Limits.Presheaf
import all Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
import all Submission.WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all Submission.WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.CategoryTheory.Sites.LocallySurjective
import all Mathlib.CategoryTheory.Monoidal.Mon
public import Submission.WeilConjectures.SixFunctors.IntegralModelsGenerators

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Comparison with completed condensed coefficients

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-sfb-qlbar-colimit-x, the three comparisons and inverse-image compatibility
(blueprint: sk-prop-sfb-qlbar-colimit-x).

The comparisons are expressed by universal properties of the specified reduction maps
and localization cocone. Thus no choice of an unrelated isomorphism is involved.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar


/-- Pull back an actual condensed ring homomorphism, including all its ring structure.
Source: blueprint comparison with completed coefficients, its canonical maps
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedCoefficientMap (X : Scheme.{u})
    {R S : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}} (f : R ⟶ S) :
    completedCoefficient X R ⟶ completedCoefficient X S :=
  (sfbPullbackFromPoint X).mapMon.map
    (Mon.Hom.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map f))

/-- The usual constant ring sheaf, expressed in the existing ring-object encoding.
Source: blueprint comparison with completed coefficients, its finite constant coefficients
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable abbrev completedConstantRing (X : Scheme.{u}) (R : Type) [Ring R] :=
  Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
      (RingCat.of (ULift.{u + 1} R))))

/-- The map of constant ring sheaves induced by an actual ring homomorphism.
Source: blueprint comparison with completed coefficients, finite reduction transitions
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedConstantMap (X : Scheme.{u}) {R S : Type} [Ring R] [Ring S]
    (f : R →+* S) : completedConstantRing X R ⟶ completedConstantRing X S :=
  Mon.Hom.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).map
      (RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        (f.comp ULift.ringEquiv.toRingHom)))))

/-- The finite quotient, with its quotient topology; level `n` means exponent `n+1`.
Source: blueprint comparison with completed coefficients, first comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
abbrev completedResidue (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ) :=
  PadicAlgCl.integers l E ⧸ (Ideal.span {π}) ^ (n + 1)

/-- The actual reduction of continuous integer-valued functions modulo `π^(n+1)`.
Source: blueprint comparison with completed coefficients, first comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedReduction (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ) :
    Profinite.padicIntegersCondensedRing.{u} l E ⟶
      Profinite.continuousMapRingSheaf (completedResidue l E π n) :=
  Profinite.continuousMapRingSheafMap (Ideal.Quotient.mk _) continuous_quot_mk

/-- Transition between consecutive quotient rings, applied to continuous functions.
Source: blueprint comparison with completed coefficients, first comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedResidueTransition (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ) :
    Profinite.continuousMapRingSheaf.{u} (completedResidue l E π (n + 1)) ⟶
      Profinite.continuousMapRingSheaf (completedResidue l E π n) :=
  Profinite.continuousMapRingSheafMap
    (Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.le_succ (n + 1)))
    ((QuotientRing.isOpenQuotientMap_mk ((Ideal.span {π}) ^ (n + 2))).isQuotientMap
      |>.continuous_iff.mpr continuous_quot_mk)

/-- The regular integral module maps to the rational ring, restricted along its inclusion.
Source: blueprint comparison with completed coefficients, localization comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedRationalModule (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :=
  (Mod.comap (completedCoefficientMap X
    (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing l E)).hom).obj
    (Mod.regular (completedCoefficient X (Profinite.padicSubfieldCondensedRing l E)).X)

/-- The existing finite-field diagram, bundled with its ring homomorphisms.
Source: blueprint comparison with completed coefficients, third comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedPointSubfieldDiagram (l : ℕ) [Fact l.Prime] :
    PadicAlgCl.FiniteIntermediateField l ⥤
      Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) where
  obj E := Mon.mk (Profinite.continuousMapRingObj E)
  map f := Mon.Hom.mk (Profinite.padicSubfieldRingObjMap l (leOfHom f))
  map_id E := Mon.Hom.ext (Profinite.padicSubfieldRingObjMap_id l E)
  map_comp f g := Mon.Hom.ext (Profinite.padicSubfieldRingObjMap_comp l
    (leOfHom f) (leOfHom g))

/-- The existing canonical algebraic-closure cocone, bundled in ring objects.
Source: blueprint comparison with completed coefficients, third comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedPointSubfieldCocone (l : ℕ) [Fact l.Prime] :
    Cocone (completedPointSubfieldDiagram.{u} l) where
  pt := Mon.mk (Profinite.padicAlgClRingObj l)
  ι := {
    app E := Mon.Hom.mk (Profinite.padicSubfieldRingObjToPadicAlgCl l E)
    naturality _E _F f := Mon.Hom.ext
      ((Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl l (leOfHom f)).trans
        (Category.comp_id _).symm) }

/-- The canonical ring cocone on a scheme is the image of the point cocone under p_X^*.
Source: blueprint comparison with completed coefficients, third comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedSubfieldCocone (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] :=
  (sfbPullbackFromPoint X).mapMon.mapCocone (completedPointSubfieldCocone l)

open CategoryTheory.MonObj CategoryTheory.MonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def siftedRingCoconeIsColimit
    {C : Type*} [Category C] [MonoidalCategory C]
    {J : Type*} [Category J] [IsSifted J]
    {D : J ⥤ Mon C} (c : Cocone D)
    (hc : IsColimit ((Mon.forget C).mapCocone c))
    [PreservesColimit₂ (D ⋙ Mon.forget C) (D ⋙ Mon.forget C) (curriedTensor C)] :
    IsColimit c := by
  let desc (s : Cocone D) : c.pt ⟶ s.pt := by
    let d : c.pt.X ⟶ s.pt.X := hc.desc ((Mon.forget C).mapCocone s)
    have hd (j : J) : (c.ι.app j).hom ≫ d = (s.ι.app j).hom :=
      hc.fac ((Mon.forget C).mapCocone s) j
    have : IsMonHom d := by
      constructor
      · obtain ⟨j⟩ := IsSifted.nonempty (C := J)
        rw [← IsMonHom.one_hom (c.ι.app j).hom, Category.assoc, hd j]
        exact IsMonHom.one_hom (s.ι.app j).hom
      · apply (hc.tensor hc).hom_ext
        intro j
        change ((c.ι.app j).hom ⊗ₘ (c.ι.app j).hom) ≫ μ[c.pt.X] ≫ d =
          ((c.ι.app j).hom ⊗ₘ (c.ι.app j).hom) ≫ (d ⊗ₘ d) ≫ μ[s.pt.X]
        rw [← IsMonHom.mul_hom_assoc, hd j,
          tensorHom_comp_tensorHom_assoc, hd j]
        exact IsMonHom.mul_hom (s.ι.app j).hom
    exact Mon.Hom.mk d
  refine { desc := desc, fac := ?_, uniq := ?_ }
  · intro s j
    apply Mon.Hom.ext
    exact hc.fac ((Mon.forget C).mapCocone s) j
  · intro s m hm
    apply Mon.Hom.ext
    apply hc.hom_ext
    intro j
    exact (congrArg Mon.Hom.hom (hm j)).trans
      (hc.fac ((Mon.forget C).mapCocone s) j).symm


namespace CondensedRing
attribute [local irreducible] pointUpperStarLowerStarAdjunction
  ProEtale.upperStarLowerStarAdjunction
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

section

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

private noncomputable abbrev coefficientPresheaf (R : Type) [TopologicalSpace R]
    [Ring R] [IsTopologicalRing R] : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1} :=
  Profinite.continuousMapRingPresheaf R ⋙ forget₂ RingCat Ab

private noncomputable abbrev integralPresheafMap :
    coefficientPresheaf.{u} (continuousIntegers ℓ E) ⟶ coefficientPresheaf E :=
  Functor.whiskerRight
    (Profinite.continuousMapRingPresheafMap (continuousIntegers ℓ E).subtype
      continuous_subtype_val) (forget₂ RingCat Ab)

private noncomputable def localizationLegHom (n : ℕ) :
    coefficientPresheaf.{u} (continuousIntegers ℓ E) ⟶ coefficientPresheaf E where
  app S := AddCommGrpCat.ofHom
    { toFun x := ULift.up
        (⟨fun s ↦ (x.down s : E) / (ℓ : E) ^ n,
          (continuous_subtype_val.comp x.down.continuous).div_const _⟩ : C(S.unop, E))
      map_zero' := by apply ULift.ext; ext; simp
      map_add' x y := by
        apply ULift.ext
        ext s
        change ((x.down s : E) + (y.down s : E)) / (ℓ : E) ^ n =
          (x.down s : E) / (ℓ : E) ^ n + (y.down s : E) / (ℓ : E) ^ n
        exact add_div _ _ _ }
  naturality _ _ _ := rfl

private noncomputable def localizationLeg (n : ℕ) :
    Mod.regular (coefficientPresheaf.{u} (continuousIntegers ℓ E)) ⟶
      (Mod.comap (integralPresheafMap ℓ E)).obj (Mod.regular (coefficientPresheaf E)) :=
  Mod.homMk (localizationLegHom ℓ E n) (by
    ext S : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro a b
    apply ULift.ext
    ext x
    change ((a.down x : E) * (b.down x : E)) / (ℓ : E) ^ n =
      (a.down x : E) * ((b.down x : E) / (ℓ : E) ^ n)
    exact mul_div_assoc _ _ _)

private noncomputable abbrev localizationSequence :
    ℕ ⥤ Mod (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1})
      (coefficientPresheaf (continuousIntegers ℓ E)) :=
  Functor.ofSequence (fun _ ↦ ℓ • 𝟙 (Mod.regular
    (coefficientPresheaf (continuousIntegers ℓ E))))

private noncomputable def localizationCocone : Cocone (localizationSequence.{u} ℓ E) where
  pt := (Mod.comap (integralPresheafMap ℓ E)).obj (Mod.regular (coefficientPresheaf E))
  «ι» := NatTrans.ofSequence (localizationLeg ℓ E) (by
    intro n
    simp only [localizationSequence, Functor.ofSequence_map_homOfLE_succ,
      Functor.const_obj_map]
    apply Mod.hom_ext
    ext S x
    apply ULift.ext
    ext s
    change (continuousIntegers ℓ E).subtype (ℓ • x.down s) / (ℓ : E) ^ (n + 1) =
      (x.down s : E) / (ℓ : E) ^ n
    rw [map_nsmul, nsmul_eq_mul, pow_succ]
    field_simp [ell_ne_zero ℓ E]
    rfl)

private noncomputable def localizationCoconeIsColimit :
    IsColimit (localizationCocone.{u} ℓ E) := by
  let := Functor.functorCategoryMonoidalClosed Profinite.{u}ᵒᵖ Ab.{u + 1}
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget Ab.{u + 1})
  have : ReflectsColimitsOfShape ℕ (forget Ab.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  have : ReflectsColimitsOfShape ℕ
      (Mod.forget (D := Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1})
        (coefficientPresheaf (continuousIntegers ℓ E))) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (Mod.forget (D := Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1})
    (coefficientPresheaf (continuousIntegers ℓ E)))
  refine evaluationJointlyReflectsColimits _ fun S ↦
    isColimitOfReflects (forget Ab.{u + 1}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    let φ := (continuousIntegers ℓ E).subtype.compLeftContinuous S.unop continuous_subtype_val
    let := φ.toAlgebra
    have hloc := continuousIntegralFunctions_isLocalization ℓ E S.unop
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj
      (ContinuousMap.const S.unop (ℓ : continuousIntegers ℓ E)) x.down
    refine ⟨n, ULift.up a, ?_⟩
    apply ULift.ext
    ext s
    change x.down s = (a s : E) / (ℓ : E) ^ n
    have ha' := congrArg (fun f : C(S.unop, E) ↦ f s) ha
    change x.down s * (ℓ : E) ^ n = (a s : E) at ha'
    exact (eq_div_iff (pow_ne_zero n (ell_ne_zero ℓ E))).2 ha'
  · intro n x y h
    have hxy : x = y := by
      apply ULift.ext
      apply ContinuousMap.ext
      intro s
      apply Subtype.ext
      have h' := congrArg (fun f : ULift.{u + 1} C(S.unop, E) ↦ f.down s) h
      change (x.down s : E) / (ℓ : E) ^ n = (y.down s : E) / (ℓ : E) ^ n at h'
      exact (div_left_inj' (pow_ne_zero n (ell_ne_zero ℓ E))).mp h'
    subst y
    exact ⟨n, 𝟙 n, rfl⟩

private noncomputable def mappedRegularIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) [L.LaxMonoidal] (R : C) [MonObj R] :
    (L.mapMod R).obj (Mod.regular R) ≅ Mod.regular (L.obj R) :=
  Mod.isoMk (Iso.refl _) (by simp [Mod.act])

private noncomputable def restrictedRegularIso
    {C : Type*} [Category C] [MonoidalCategory C]
    {A B B' : C} [MonObj A] [MonObj B] [MonObj B']
    (φ : A ⟶ B) (φ' : A ⟶ B') [IsMonHom φ] [IsMonHom φ']
    (e : B ≅ B') [IsMonHom e.hom] (w : φ ≫ e.hom = φ') :
    (Mod.comap φ).obj (Mod.regular B) ≅ (Mod.comap φ').obj (Mod.regular B') :=
  Mod.isoMk e (by
    change (φ ▷ B ≫ μ[B]) ≫ e.hom = A ◁ e.hom ≫ φ' ▷ B' ≫ μ[B']
    rw [Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def, Category.assoc,
      ← comp_whiskerRight_assoc, w, whisker_exchange_assoc])

private noncomputable def pointCoefficientIso (R : Type) [TopologicalSpace R]
    [Ring R] [IsTopologicalRing R] :
    (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (coefficientPresheaf R) ≅ Profinite.continuousMapRingObj R :=
  Sheaf.sheafifyRingPresheafIso (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheaf R)

private noncomputable abbrev schemeCoefficientFunctor (X : Scheme.{u}) :=
  presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙ upperStarFromPoint X

private noncomputable def schemeCoefficientIso (X : Scheme.{u})
    (R : Type) [TopologicalSpace R] [Ring R] [IsTopologicalRing R] :
    (schemeCoefficientFunctor X).obj (coefficientPresheaf R) ≅
      condensedRingObj (Profinite.continuousMapRingObj R) X :=
  (upperStarFromPoint X).mapIso (pointCoefficientIso R)

private theorem schemeCoefficientIso_naturality (X : Scheme.{u}) :
    (schemeCoefficientFunctor X).map (integralPresheafMap ℓ E) ≫
        (schemeCoefficientIso X E).hom =
      (schemeCoefficientIso X (continuousIntegers ℓ E)).hom ≫
        coefficientMap (integralScalarMap ℓ E) X := by
  change (upperStarFromPoint X).map
      ((presheafToSheaf _ Ab).map (integralPresheafMap ℓ E)) ≫
        (upperStarFromPoint X).map (pointCoefficientIso E).hom =
    (upperStarFromPoint X).map (pointCoefficientIso (continuousIntegers ℓ E)).hom ≫
      (upperStarFromPoint X).map (integralScalarMap ℓ E)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [integralScalarMap, Sheaf.sheafCompose_map_eq]
  simp only [pointCoefficientIso, Iso.hom_inv_id_assoc]
  rfl


end

attribute [local irreducible] localizationCoconeIsColimit


private noncomputable def completedMappedRegularIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) [L.LaxMonoidal] (R : C) [MonObj R]
    (A : D) [MonObj A] (a : L.obj R ≅ A) [IsMonHom a.hom] :
    (L.mapMod R ⋙ Mod.comap a.inv).obj (Mod.regular R) ≅ Mod.regular A :=
  (Mod.comap a.inv).mapIso (mappedRegularIso L R) ≪≫
    restrictedRegularIso a.inv (𝟙 A) a (by exact a.inv_hom_id) ≪≫ (Mod.comapId A).app _

private noncomputable def completedMappedRestrictedIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) [L.LaxMonoidal] {R S : C} [MonObj R] [MonObj S]
    (φ : R ⟶ S) [IsMonHom φ] {A B : D} [MonObj A] [MonObj B]
    (a : L.obj R ≅ A) (b : L.obj S ≅ B) [IsMonHom a.hom] [IsMonHom b.hom]
    (ψ : A ⟶ B) [IsMonHom ψ] (h : L.map φ ≫ b.hom = a.hom ≫ ψ) :
    (L.mapMod R ⋙ Mod.comap a.inv).obj ((Mod.comap φ).obj (Mod.regular S)) ≅
      (Mod.comap ψ).obj (Mod.regular B) :=
  (Mod.comap a.inv).mapIso
    ((L.mapModComapIso φ).app (Mod.regular S) ≪≫
      (Mod.comap (L.map φ)).mapIso (mappedRegularIso L S)) ≪≫
    (Mod.comapComp a.inv (L.map φ)).symm.app (Mod.regular (L.obj S)) ≪≫
    restrictedRegularIso (a.inv ≫ L.map φ) ψ b (by
      rw [Category.assoc, h, Iso.inv_hom_id_assoc])


attribute [local irreducible] schemeCoefficientIso pointCoefficientIso


end CondensedRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- The underlying limit determines the unit and multiplication of every lift.
open scoped MonObj MonoidalCategory in
private noncomputable def completedRingLimit
    {C : Type*} [Category C] [MonoidalCategory C]
    {J : Type*} [Category J] {D : J ⥤ Mon C} (c : Cone D)
    (hc : IsLimit ((Mon.forget C).mapCone c)) : IsLimit c := by
  let lift (s : Cone D) : s.pt ⟶ c.pt := by
    let a : s.pt.X ⟶ c.pt.X := hc.lift ((Mon.forget C).mapCone s)
    have ha (j : J) : a ≫ (c.π.app j).hom = (s.π.app j).hom :=
      hc.fac ((Mon.forget C).mapCone s) j
    have : IsMonHom a := by
      constructor
      · apply hc.hom_ext
        intro j
        change (η[s.pt.X] ≫ a) ≫ (c.π.app j).hom = η[c.pt.X] ≫ (c.π.app j).hom
        rw [Category.assoc, ha j]
        exact (s.π.app j).isMonHom_hom.one_hom.trans
          (c.π.app j).isMonHom_hom.one_hom.symm
      · apply hc.hom_ext
        intro j
        change (μ[s.pt.X] ≫ a) ≫ (c.π.app j).hom =
          ((a ⊗ₘ a) ≫ μ[c.pt.X]) ≫ (c.π.app j).hom
        rw [Category.assoc, ha j, (s.π.app j).isMonHom_hom.mul_hom,
          Category.assoc, (c.π.app j).isMonHom_hom.mul_hom, ← Category.assoc,
          MonoidalCategory.tensorHom_comp_tensorHom, ha j]
    exact Mon.Hom.mk a
  refine { lift := lift, fac := ?_, uniq := ?_ }
  · intro s j
    apply Mon.Hom.ext
    exact hc.fac ((Mon.forget C).mapCone s) j
  · intro s m hm
    apply Mon.Hom.ext
    apply hc.hom_ext
    intro j
    exact (congrArg Mon.Hom.hom (hm j)).trans
      (hc.fac ((Mon.forget C).mapCone s) j).symm

private noncomputable abbrev completedProfinite (R : Type) [TopologicalSpace R]
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] : Profinite.{u} :=
  letI : TotallyDisconnectedSpace (ULift.{u} R) :=
    Homeomorph.ulift.isEmbedding.isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  Profinite.of (ULift.{u} R)

private noncomputable def completedPointRepresentation (R : Type) [TopologicalSpace R]
    [Ring R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    [TotallyDisconnectedSpace R] :
    (sheafCompose (coherentTopology Profinite.{u}) (forget Ab.{u + 1})).obj
        (Profinite.continuousMapRingObj R) ≅
      (coherentTopology Profinite.{u}).uliftYoneda.{u + 1}.obj (completedProfinite R) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun S ↦ Equiv.toIso
      { toFun := fun x ↦ ULift.up (show S.unop ⟶ completedProfinite R from
          ConcreteCategory.ofHom ⟨fun t ↦ ULift.up (x.down t),
            continuous_uliftUp.comp x.down.continuous⟩)
        invFun := fun x ↦ ULift.up
          (show C(S.unop, R) from
            ⟨fun t ↦ ((show S.unop ⟶ completedProfinite R from x.down).hom.hom t).down,
            continuous_uliftDown.comp
              (show S.unop ⟶ completedProfinite R from x.down).hom.hom.continuous⟩)
        left_inv := fun x ↦ by rfl
        right_inv := fun x ↦ by rfl }) (by intro S T f; rfl))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def completedRepresentation (X : Scheme.{u})
    (R : Type) [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] :
    ((completedCoefficient X (Profinite.continuousMapRingSheaf R)).X).obj ⋙
        forget Ab.{u + 1} ≅
      uliftYoneda.{u + 1}.obj ((profiniteToProEtOf X).obj (completedProfinite R)) := by
  let U := profiniteToProEtOf X
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology X
  let L := Functor.sheafPullbackConstruction.sheafPullback U (Type (u + 1)) J K
  exact (sheafToPresheaf K (Type (u + 1))).mapIso
    ((integralPullbackForgetIso X).app (Profinite.continuousMapRingObj R) ≪≫
      L.mapIso (completedPointRepresentation R) ≪≫
      representablePullbackIso J K U L
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U (Type (u + 1)) J K)
        (completedProfinite R))

private noncomputable def completedProfiniteMap
    {R S : Type} [TopologicalSpace R] [TopologicalSpace S]
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R]
    [CompactSpace S] [T2Space S] [TotallyDisconnectedSpace S]
    (f : R → S) (hf : Continuous f) : completedProfinite.{u} R ⟶ completedProfinite S :=
  ConcreteCategory.ofHom ⟨fun x ↦ ULift.up (f x.down),
    continuous_uliftUp.comp (hf.comp continuous_uliftDown)⟩

private theorem completedRepresentablePullbackNaturality
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [J.Subcanonical] [K.Subcanonical] (U : C ⥤ D) [U.IsContinuous J K]
    (L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1)))
    (adj : L ⊣ U.sheafPushforwardContinuous (Type (u + 1)) J K)
    {S T : C} (f : S ⟶ T) :
    L.map (J.uliftYoneda.{u + 1}.map f) ≫
        (representablePullbackIso J K U L adj T).hom =
      (representablePullbackIso J K U L adj S).hom ≫
        K.uliftYoneda.{u + 1}.map (U.map f) := by
  let t (V : C) : J.uliftYoneda.{u + 1}.obj V ⟶
      (U.sheafPushforwardContinuous (Type (u + 1)) J K).obj
        (K.uliftYoneda.{u + 1}.obj (U.obj V)) :=
    ⟨{ app := fun W ↦ ↾fun g ↦ ULift.up (U.map g.down)
       naturality := by
         intro W Z g
         ext h
         apply ULift.ext
         change U.map (g.unop ≫ h.down) = U.map g.unop ≫ U.map h.down
         exact U.map_comp _ _ }⟩
  have hm (V : C) : adj.homEquiv _ _
      (representablePullbackIso J K U L adj V).hom = t V :=
    (adj.homEquiv _ _).apply_symm_apply (t V)
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, hm, hm]
  ext V x
  change ULift.up (U.map (x.down ≫ f)) = ULift.up (U.map x.down ≫ U.map f)
  rw [U.map_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem completedRepresentation_naturality (X : Scheme.{u})
    {R S : Type} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R]
    [TopologicalSpace S] [Ring S] [IsTopologicalRing S]
    [CompactSpace S] [T2Space S] [TotallyDisconnectedSpace S]
    (f : R →+* S) (hf : Continuous f) :
    Functor.whiskerRight
        (completedCoefficientMap X (Profinite.continuousMapRingSheafMap f hf)).hom.hom
        (forget Ab.{u + 1}) ≫ (completedRepresentation X S).hom =
      (completedRepresentation X R).hom ≫
        uliftYoneda.{u + 1}.map ((profiniteToProEtOf X).map (completedProfiniteMap f hf)) := by
  let U := profiniteToProEtOf X
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology X
  let L := Functor.sheafPullbackConstruction.sheafPullback U (Type (u + 1)) J K
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    U (Type (u + 1)) J K
  let g := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (Profinite.continuousMapRingSheafMap f hf)
  have hp : (sheafCompose J (forget Ab.{u + 1})).map g ≫
        (completedPointRepresentation S).hom =
      (completedPointRepresentation R).hom ≫
        J.uliftYoneda.{u + 1}.map (completedProfiniteMap f hf) := by
    apply Sheaf.hom_ext
    ext V x
    apply ULift.ext
    change (show V.unop ⟶ completedProfinite S from _) = _
    ext t
    rfl
  have hn := (integralPullbackForgetIso X).hom.naturality g
  change (sheafCompose K (forget Ab.{u + 1})).map ((sfbPullbackFromPoint X).map g) ≫
      ((integralPullbackForgetIso X).app _).hom =
    ((integralPullbackForgetIso X).app _).hom ≫
      L.map ((sheafCompose J (forget Ab.{u + 1})).map g) at hn
  have hr := completedRepresentablePullbackNaturality J K U L adj (completedProfiniteMap f hf)
  apply (sheafToPresheaf K (Type (u + 1))).congr_map
    (f := (sheafCompose K (forget Ab.{u + 1})).map ((sfbPullbackFromPoint X).map g) ≫
      ((integralPullbackForgetIso X).app _ ≪≫ L.mapIso (completedPointRepresentation S) ≪≫
        representablePullbackIso J K U L adj (completedProfinite S)).hom)
    (g := ((integralPullbackForgetIso X).app _ ≪≫
      L.mapIso (completedPointRepresentation R) ≪≫
        representablePullbackIso J K U L adj (completedProfinite R)).hom ≫
      K.uliftYoneda.{u + 1}.map (U.map (completedProfiniteMap f hf))) ?_
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  erw [reassoc_of% hn]
  erw [← L.map_comp_assoc, hp, L.map_comp]
  simp only [Category.assoc]
  erw [hr]


-- Positive quotient levels avoid any special convention at the trivial level.
private noncomputable def completedProfiniteTowerCone
    (R : Type) [TopologicalSpace R] [CompactSpace R] [T2Space R]
    [TotallyDisconnectedSpace R]
    (Q : ℕ → Type) [∀ n, TopologicalSpace (Q n)] [∀ n, CompactSpace (Q n)]
    [∀ n, T2Space (Q n)] [∀ n, TotallyDisconnectedSpace (Q n)]
    (q : ∀ n, C(R, Q n)) (t : ∀ n, C(Q (n + 1), Q n))
    (hqt : ∀ n x, t n (q (n + 1) x) = q n x)
    : Cone (Functor.ofOpSequence
        (X := fun n ↦ completedProfinite.{u} (Q n))
        (fun n ↦ completedProfiniteMap (t n) (t n).continuous)) where
  pt := completedProfinite R
  π := NatTrans.ofOpSequence (fun n ↦ completedProfiniteMap (q n) (q n).continuous)
    (fun n ↦ by
      simp only [Functor.const_obj_map, Functor.ofOpSequence_map_homOfLE_succ]
      ext x
      exact congrArg ULift.up (hqt n x.down).symm)

-- Compact nested fibres give existence; joint injectivity gives uniqueness.
private noncomputable def completedProfiniteTowerLimit
    (R : Type) [TopologicalSpace R] [CompactSpace R] [T2Space R]
    [TotallyDisconnectedSpace R]
    (Q : ℕ → Type) [∀ n, TopologicalSpace (Q n)] [∀ n, CompactSpace (Q n)]
    [∀ n, T2Space (Q n)] [∀ n, TotallyDisconnectedSpace (Q n)]
    (q : ∀ n, C(R, Q n)) (t : ∀ n, C(Q (n + 1), Q n))
    (hqt : ∀ n x, t n (q (n + 1) x) = q n x)
    (hinj : ∀ x y : R, (∀ n, q n x = q n y) → x = y)
    (hsurj : ∀ n, Function.Surjective (q n)) :
    IsLimit (completedProfiniteTowerCone.{u} R Q q t hqt) := by
  let P := {b : ∀ n, Q n // ∀ n, t n (b (n + 1)) = b n}
  let f : R → P := fun x ↦ ⟨fun n ↦ q n x, fun n ↦ hqt n x⟩
  have hf : Continuous f := continuous_induced_rng.mpr (continuous_pi fun n ↦ (q n).continuous)
  have hi : Function.Injective f := fun x y h ↦ hinj x y
    (fun n ↦ congrArg (fun b : P ↦ b.val n) h)
  have hs : Function.Surjective f := by
    intro b
    let S (n : ℕ) : Set R := {x | q n x = b.val n}
    have hcl (n : ℕ) : IsClosed (S n) := isClosed_singleton.preimage (q n).continuous
    have hne (n : ℕ) : (S n).Nonempty := hsurj n (b.val n)
    have hstep (n : ℕ) : S (n + 1) ⊆ S n := by
      intro x hx
      exact (hqt n x).symm.trans ((congrArg (t n) hx).trans (b.property n))
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      S hstep hne (hcl 0).isCompact hcl
    exact ⟨x, Subtype.ext (funext fun n ↦ Set.mem_iInter.mp hx n)⟩
  let e : R ≃ₜ P := IsHomeomorph.homeomorph f
    (isHomeomorph_iff_continuous_bijective.mpr ⟨hf, hi, hs⟩)
  let D := Functor.ofOpSequence
    (X := fun n ↦ completedProfinite.{u} (Q n))
    (fun n ↦ completedProfiniteMap (t n) (t n).continuous)
  let b (s : Cone D) (x : s.pt) : P :=
    ⟨fun n ↦ (s.π.app (op n) x).down, fun n ↦ by
      have h := ConcreteCategory.congr_hom (s.w (homOfLE (Nat.le_succ n)).op) x
      dsimp only [D] at h
      simp only [Functor.ofOpSequence_map_homOfLE_succ] at h
      change ULift.up (t n ((s.π.app (op (n + 1)) x).down)) =
        s.π.app (op n) x at h
      exact congrArg ULift.down h⟩
  refine { lift := fun s ↦ ?_
           fac := ?_
           uniq := ?_ }
  · refine ConcreteCategory.ofHom
      (show C(s.pt, completedProfinite R) from
        ⟨fun x ↦ ULift.up (e.symm (b s x)), ?_⟩)
    apply continuous_uliftUp.comp
    apply e.symm.continuous.comp
    exact continuous_induced_rng.mpr
      (continuous_pi fun n ↦ continuous_uliftDown.comp (s.π.app (op n)).hom.hom.continuous)
  · intro s n
    ext x
    exact congrArg (fun a : P ↦ ULift.up (a.val n.unop)) (e.apply_symm_apply (b s x))
  · intro s m hm
    ext x
    apply congrArg ULift.up
    apply e.injective
    apply Subtype.ext
    funext n
    exact (congrArg (fun h : s.pt ⟶ D.obj (op n) ↦ (h x).down) (hm (op n))).trans
      (congrArg (fun a : P ↦ a.val n) (e.apply_symm_apply (b s x))).symm

private noncomputable def completedRingTowerCone
    (X : Scheme.{u}) (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (Q : ℕ → Type) [∀ n, CommRing (Q n)] [∀ n, TopologicalSpace (Q n)]
    [∀ n, IsTopologicalRing (Q n)] (q : ∀ n, R →+* Q n)
    (hq : ∀ n, Continuous (q n)) (t : ∀ n, Q (n + 1) →+* Q n)
    (ht : ∀ n, Continuous (t n)) (hqt : ∀ n x, t n (q (n + 1) x) = q n x) :
    Cone (Functor.ofOpSequence
      (X := fun n ↦ completedCoefficient X (Profinite.continuousMapRingSheaf (Q n)))
      (fun n ↦ completedCoefficientMap X (Profinite.continuousMapRingSheafMap (t n) (ht n))))
    where
  pt := completedCoefficient X (Profinite.continuousMapRingSheaf R)
  π := NatTrans.ofOpSequence
    (fun n ↦ completedCoefficientMap X (Profinite.continuousMapRingSheafMap (q n) (hq n)))
    (fun n ↦ by
      simp only [Functor.const_obj_map, Functor.ofOpSequence_map_homOfLE_succ]
      erw [Category.id_comp]
      change (sfbPullbackFromPoint X).mapMon.map _ =
        (sfbPullbackFromPoint X).mapMon.map _ ≫
        (sfbPullbackFromPoint X).mapMon.map _
      erw [← Functor.map_comp]
      congr 1
      apply Mon.Hom.ext
      apply Sheaf.hom_ext
      ext S x
      change ULift.up _ = ULift.up _
      congr 1
      ext y
      exact (hqt n (x.down y)).symm)

-- Preserve the represented tower, rather than arbitrary limits of inverse images.
set_option backward.isDefEq.respectTransparency false in
private noncomputable def completedRingTowerLimit
    (X : Scheme.{u}) (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R]
    (Q : ℕ → Type) [∀ n, CommRing (Q n)] [∀ n, TopologicalSpace (Q n)]
    [∀ n, IsTopologicalRing (Q n)] [∀ n, CompactSpace (Q n)] [∀ n, T2Space (Q n)]
    [∀ n, TotallyDisconnectedSpace (Q n)]
    (q : ∀ n, R →+* Q n) (hq : ∀ n, Continuous (q n))
    (t : ∀ n, Q (n + 1) →+* Q n) (ht : ∀ n, Continuous (t n))
    (hqt : ∀ n x, t n (q (n + 1) x) = q n x)
    (hinj : ∀ x y : R, (∀ n, q n x = q n y) → x = y)
    (hsurj : ∀ n, Function.Surjective (q n)) :
    IsLimit (completedRingTowerCone X R Q q hq t ht hqt) := by
  let a := completedProfiniteTowerCone.{u} R Q
    (fun n ↦ ⟨q n, hq n⟩) (fun n ↦ ⟨t n, ht n⟩) hqt
  let ha := completedProfiniteTowerLimit.{u} R Q
    (fun n ↦ ⟨q n, hq n⟩) (fun n ↦ ⟨t n, ht n⟩) hqt hinj hsurj
  let D := Functor.ofOpSequence
    (X := fun n ↦ completedProfinite.{u} (Q n))
    (fun n ↦ completedProfiniteMap (t n) (ht n))
  let U := profiniteToProEtOf X
  let : profiniteToCommRingCatOp.{u}.IsRightAdjoint :=
    profiniteToCommRingCatOp_isRightAdjoint
  let : (Over.forget specZ.{u}).IsEquivalence :=
    (Over.equivalenceOfIsTerminal specULiftZIsTerminal).isEquivalence_functor
  let : PreservesLimitsOfSize.{0, 0} profiniteToScheme.{u} := by
    unfold profiniteToScheme
    infer_instance
  let : PreservesLimit D
      ((profiniteToProEt.{u} ⋙ Scheme.ProEt.forget specZ) ⋙ Over.forget specZ) :=
    inferInstanceAs (PreservesLimit D profiniteToScheme.{u})
  let : PreservesLimit D (profiniteToProEt.{u} ⋙ Scheme.ProEt.forget specZ) :=
    preservesLimit_of_reflects_of_preserves _ (Over.forget specZ)
  let hOver := isLimitOfPreserves
    ((profiniteToProEt ⋙ Scheme.ProEt.forget specZ) ⋙ Over.pullback (toSpecZ X)) ha
  let hsch := isLimitOfPreserves (Over.forget X) hOver
  let hu : IsLimit (U.mapCone a) :=
    isLimitOfReflects (Scheme.ProEt.forget X)
      (isLimitOfReflects (Over.forget X) hsch)
  let hy := isLimitOfPreserves uliftYoneda.{u + 1} hu
  let T := Functor.ofOpSequence
    (X := fun n ↦ completedCoefficient X (Profinite.continuousMapRingSheaf (Q n)))
    (fun n ↦ completedCoefficientMap X (Profinite.continuousMapRingSheafMap (t n) (ht n)))
  let c := completedRingTowerCone X R Q q hq t ht hqt
  let W := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
    (Functor.whiskeringRight _ _ _).obj (forget Ab.{u + 1})
  let F := Mon.forget (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⋙ W
  let β : T ⋙ F ⟶ D ⋙ U ⋙ uliftYoneda.{u + 1} :=
    NatTrans.ofOpSequence (fun n ↦ (completedRepresentation X (Q n)).hom) (fun n ↦ by
      dsimp only [T, D, Functor.comp_map]
      simp only [Functor.ofOpSequence_map_homOfLE_succ]
      exact completedRepresentation_naturality X (t n) (ht n))
  have hβ (n : ℕᵒᵖ) : IsIso (β.app n) := by
    change IsIso (completedRepresentation X (Q n.unop)).hom
    infer_instance
  have : IsIso β := NatIso.isIso_of_isIso_app β
  have hw (n : ℕᵒᵖ) : F.map (c.π.app n) ≫ β.app n =
      (completedRepresentation X R).hom ≫
        (uliftYoneda.{u + 1}.mapCone (U.mapCone a)).π.app n := by
    exact completedRepresentation_naturality X (q n.unop) (hq n.unop)
  let h : IsLimit (F.mapCone c) :=
    (IsLimit.equivOfNatIsoOfIso (asIso β) (F.mapCone c)
      (uliftYoneda.{u + 1}.mapCone (U.mapCone a))
      (Cone.ext (completedRepresentation X R) hw)).symm hy
  let : ReflectsLimitsOfShape ℕᵒᵖ W := reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact completedRingLimit c (isLimitOfReflects W h)

-- Use the explicit constant-function map to retain naturality in coefficient maps.
private noncomputable def completedFinitePointIso (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology R] [Finite R] :
    Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
        ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} R))) ≅
      Profinite.continuousMapRingObj R := by
  let J := coherentTopology Profinite.{u}
  let φ := Functor.whiskerRight (Profinite.constantToContinuousRing.{u} R)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  have hφ : J.W (A := Ab.{u + 1}) φ := J.W_of_isLocallyBijective φ
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map φ) := (J.W_iff φ).mp hφ
  exact asIso ((presheafToSheaf J Ab.{u + 1}).map φ) ≪≫
    Sheaf.sheafifyRingPresheafIso.{u + 1, u, u + 1} J (Profinite.continuousMapRingSheaf R)

private instance completedFinitePointIso_isMonHom (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology R] [Finite R] :
    IsMonHom (completedFinitePointIso.{u} R).hom := by
  dsimp only [completedFinitePointIso, Iso.trans_hom, asIso_hom]
  infer_instance

private noncomputable def completedConstantPresentationIso (X : Scheme.{u})
    (R : Type) [Ring R] :
    Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} R))) ≅
      (completedConstantRing X R).X := by
  let K := Scheme.ProEt.topology X
  let P := (Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} R))
  let S := (constantSheaf K RingCat.{u + 1}).obj (RingCat.of (ULift.{u + 1} R))
  let φ := Functor.whiskerRight (toSheafify K P) (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let : K.PreservesSheafification (forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification K _
  have hφ : K.W (A := Ab.{u + 1}) φ :=
    K.W_of_preservesSheafification (forget₂ RingCat.{u + 1} Ab.{u + 1}) _
      (K.W_toSheafify P)
  have : IsIso ((presheafToSheaf K Ab.{u + 1}).map φ) := (K.W_iff φ).mp hφ
  exact asIso ((presheafToSheaf K Ab.{u + 1}).map φ) ≪≫
    Sheaf.sheafifyRingPresheafIso.{u + 1, u, u + 1} K S

private instance completedConstantPresentationIso_isMonHom (X : Scheme.{u})
    (R : Type) [Ring R] : IsMonHom (completedConstantPresentationIso X R).hom := by
  dsimp only [completedConstantPresentationIso, Iso.trans_hom, asIso_hom]
  infer_instance

private noncomputable def completedFiniteIso (X : Scheme.{u}) (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology R] [Finite R] :
    completedCoefficient X (Profinite.continuousMapRingSheaf R) ≅ completedConstantRing X R := by
  let e := (completedConstantPresentationIso X R).symm ≪≫
    finiteDiscreteSchemeRingIso R X (completedFinitePointIso R)
  have : IsMonHom e.hom := by dsimp only [e, Iso.trans_hom, Iso.symm_hom]; infer_instance
  exact (Mon.mkIso e (IsMonHom.one_hom e.hom) (IsMonHom.mul_hom e.hom)).symm


/-- The canonical finite-subextension cocone is a colimit in ring objects.
Source: blueprint comparison with completed coefficients, third display
(blueprint: sk-prop-sfb-qlbar-colimit-x).

Proof: A section of the condensed algebraic closure belongs to some finite subfield.
A compatible family of additive maps therefore glues uniquely, independently of the
chosen field because two fields lie in a common finite compositum. Pullback from the
point preserves this colimit, being a left adjoint. The descended map preserves the
unit at the base field. For multiplication, tensor preserves colimits in each variable;
compare on E_X tensor F_X and pass to a common finite compositum H. Both restrictions
are multiplicative there. Additive uniqueness then proves uniqueness as a ring map.
These are steps 3--5 of the node's proof.
-/
theorem completedCondensedAlgebraicClosure (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] :
    Nonempty (IsColimit (completedSubfieldCocone X l)) := by
  have : IsSifted (PadicAlgCl.FiniteIntermediateField l) := IsFiltered.isSifted
  refine ⟨siftedRingCoconeIsColimit _ ?_⟩
  change IsColimit (padicAlgClRingObjCocone X l)
  exact isColimitPadicAlgClRingObjCocone X l

/-- The usual continuous reduction of p-adic integers to Z/l^(n+1).
Source: blueprint comparison with completed coefficients, final paragraph
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedPadicReduction (l : ℕ) [Fact l.Prime] (n : ℕ) :=
  Profinite.continuousMapRingSheafMap.{u} (PadicInt.toZModPow (p := l) (n + 1))
    (PadicInt.continuous_toZModPow (n + 1))

/-- The specified p-adic rational ring as a module over the p-adic integral ring.
Source: blueprint comparison with completed coefficients, final paragraph
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedPadicRationalModule (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] :=
  (Mod.comap (completedCoefficientMap X
    (Profinite.padicIntCondensedRingToPadicCondensedRing l)).hom).obj
    (Mod.regular (completedCoefficient X (Profinite.padicCondensedRing l)).X)


end AlgebraicGeometry.ProEtale
