/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.CompletedPullback
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.CompletedCondensedCoefficients
public import Sheaf.Paper.CartesianCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.ContinuousCoefficientModuleEncoding
public import Sheaf.Paper.CompletedDirectImageLimits
public import Sheaf.Paper.RingedEtaleOriginWitness
public import Sheaf.CategoryTheory.ConstantScalarRestrictionTensor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparisonMap
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # Normalized integral coefficient presentation and quotient Roos completeness

Source: Bhatt--Scholze, Lemmas 6.5.9(2),(3) and 5.4.3
(blueprint: def-sfb-integral-ambient-coefficient-presentation).

The coefficient comparisons preserve quotient projections and local constant scalars.
The module transports retain the induced scalar action. Quotient Roos completeness
uses the actual augmented quotient tower and the canonical derived projections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

/-- Sheafification in the fixed module universe of the original small site.
Source: Stacks Tag 03DA (blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
instance (priority := 2400) quotientRoosAbSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} T

/-- The locally bijective criterion in that same coefficient universe.
Source: Stacks Tag 03DA (blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
instance (priority := 2400) quotientRoosAbLocallyBijective (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T

/-- The Roos-triangle condition for the actual augmented derived quotient tower.
The first map is the product of its specified quotient-unit legs. No map to a chosen
derived limit is selected. For the valuation-ring specialization this is exactly the
condition of the recorded global `IntegralOnSlice.IsComplete`, in adic coordinates.
Source: Bhatt--Scholze, Definition 3.5.2; Stacks Tag 08TC
(blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
def AdicCoefficientDatum.quotientRoosComplete {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (T : Scheme.{u}) (K : d.derived T) : Prop :=
  let B := (completedReductionTower T d).obj K
  ∃ hprod : HasProduct (completedTowerDerivedSequence T d B),
    letI := hprod
    ∃ δ : (∏ᶜ (completedTowerDerivedSequence T d B)) ⟶ K⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle (completedTowerDerivedStep T d B) K
        (d.completionUnit T K ≫ completedRlimRoosProjection T d B) δ

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.IntegralAmbientTower

variable (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)

/-- The existing valuation ring, lifted only to the small site's module universe.
Source: Bhatt--Scholze, Section 6.5
(blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
abbrev integers := ULift.{u + 1} (PadicAlgCl.integers l E.1)

/-- The two-term free complex, in degrees -1 and 0, with its specified differential.
Source: Bhatt--Scholze, Lemma 6.5.9(3)
(blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
def multiplication (π : PadicAlgCl.integers l E.1) (n : ℕ) :
    (CochainComplex.singleFunctor (ModuleCat.{u + 1} (integers.{u} l E)) 0).obj
        (ModuleCat.of (integers.{u} l E) (integers.{u} l E)) ⟶
      (CochainComplex.singleFunctor (ModuleCat.{u + 1} (integers.{u} l E)) 0).obj
        (ModuleCat.of (integers.{u} l E) (integers.{u} l E)) :=
  (CochainComplex.singleFunctor (ModuleCat.{u + 1} (integers.{u} l E)) 0).map
    (ModuleCat.ofHom ((LinearMap.lsmul (integers.{u} l E) (integers.{u} l E))
      ((ULift.up π : integers.{u} l E) ^ (n + 1))))

/-- The mapping cone puts the source in degree -1 and the target in degree zero.
Source: Bhatt--Scholze, Lemma 6.5.9(3)
(blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
def resolution (π : PadicAlgCl.integers l E.1) (n : ℕ) :=
  CochainComplex.mappingCone (multiplication.{u} l E π n)

/-- The actual positive quotient in degree zero, with its standard module structure.
Source: Bhatt--Scholze, Lemma 6.5.9(3)
(blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
def quotientComplex (π : PadicAlgCl.integers l E.1) (n : ℕ) :
    CochainComplex (ModuleCat.{u + 1} (integers.{u} l E)) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{u + 1} (integers.{u} l E)) 0).obj
    (ModuleCat.of (integers.{u} l E)
      (integers.{u} l E ⧸ (Ideal.span {ULift.up π}) ^ (n + 1)))

/-- Every term of the complex is a finite free module over its specified scalar ring.
Source: Bhatt--Scholze, Lemma 6.5.9(3)
(blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
def HasFiniteFreeTerms {R : Type v} [CommRing R]
    (C : CochainComplex (ModuleCat.{v} R) ℤ) : Prop :=
  ∀ i : ℤ, Module.Free R (C.X i) ∧ Module.Finite R (C.X i)

/-- Arithmetic hypotheses of the adic datum, with the actual principal ideal.
Source: Bhatt--Scholze, Lemma 6.5.9(3); Serre, Local Fields, Chapter II
(blueprint: def-sfb-integral-ambient-coefficient-presentation).
Proof: the valuation ring is a DVR by lem-weil-l-adic-extension-integers-dvr,
hence Noetherian. A principal ideal is finitely generated. The finite residue field
and lem-weil-valued-dvr-finite-quotients give finite positive quotients. The
nonzero uniformizer power is injective; its cokernel is the indicated quotient.
The length-one free resolution makes every positive quotient perfect. Since l
lies in the maximal ideal, l^(n+1) kills the nth quotient; its first quotient is
therefore additive torsion. Lifting the carrier preserves all these assertions. -/
theorem arithmetic (π : PadicAlgCl.integers l E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1)) :
    IsNoetherianRing (integers.{u} l E) ∧
      (Ideal.span ({ULift.up π} : Set (integers.{u} l E))).FG ∧
      (∀ x : integers.{u} l E ⧸ Ideal.span {ULift.up π},
        ∃ m : ℕ, 0 < m ∧ m • x = 0) ∧
      (∀ n : ℕ, Finite (integers.{u} l E ⧸
        (Ideal.span {ULift.up π}) ^ (n + 1))) ∧
      (∀ n : ℕ, 1 ≤ n → adicQuotientPerfect (integers.{u} l E)
        (Ideal.span {ULift.up π}) n) := by
  sorry

/-- The adic datum has real data: its only data field is the displayed principal ideal.
All other fields are the named arithmetic properties of that fixed object.
Source: Bhatt--Scholze, Lemma 6.5.9(3)
(blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
@[irreducible] def datum (π : PadicAlgCl.integers l E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1)) :
    AdicCoefficientDatum (integers.{u} l E) where
  ideal := Ideal.span {ULift.up π}
  noetherian := (arithmetic l E π hπ).1
  finitelyGenerated := (arithmetic l E π hπ).2.1
  quotientTorsion := (arithmetic l E π hπ).2.2.1
  quotientFinite := (arithmetic l E π hπ).2.2.2.1
  quotientPerfect := (arithmetic l E π hπ).2.2.2.2

/-- Reconstructed section ring of the pulled-back condensed integers.
Source: Bhatt--Scholze, Section 6.5
(blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
abbrev integralRing (T : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology T)
    (condensedRingObj (Profinite.padicIntegersRingObj.{u} l E.1) T)

/-- Reconstructed section ring of the pulled-back nth finite quotient.
Source: Bhatt--Scholze, Section 6.5
(blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
abbrev quotientRing (π : PadicAlgCl.integers l E.1) (T : Scheme.{u}) (n : ℕ) :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology T)
    (condensedRingObj
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) T)

/-- The specified reduction homomorphism, reconstructed without forgetting multiplication.
Source: Bhatt--Scholze, Section 6.5
(blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
def quotientProjection (π : PadicAlgCl.integers l E.1) (T : Scheme.{u}) (n : ℕ) :
    integralRing l E T ⟶ quotientRing l E π T n :=
  CondensedRing.sectionRingMap T (AlgebraicGeometry.ProEtale.completedCoefficientMap T
    (completedReduction.{u} l E π n)).hom

/-- The scalar quotient from the original valuation ring to the lifted adic quotient.
Source: Bhatt--Scholze, Lemma 6.5.9(3)
(blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
def quotientScalars (π : PadicAlgCl.integers l E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1)) (n : ℕ) :
    PadicAlgCl.integers l E.1 →+*
      integers.{u} l E ⧸ (datum.{u} l E π hπ).ideal ^ (n + 1) :=
  (Ideal.Quotient.mk _).comp ULift.ringEquiv.symm.toRingHom

/-- A normalized coefficient presentation: quotient scalars and all limit projections
are fixed. The finite normalization is tested on local constant sections through the
canonical continuous coefficient chart; these generate the finite sheaf locally.
Source: Bhatt--Scholze, Section 6.5; Stacks 09BT
(blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
structure CoefficientModel (π : PadicAlgCl.integers l E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
    (T : Scheme.{u}) where
  finite : ∀ n : ℕ, quotientRing l E π T n ≅ (datum.{u} l E π hπ).finiteRing T n
  completed : integralRing l E T ≅ (datum.{u} l E π hπ).completedRing T
  projection : ∀ n : ℕ,
    completed.hom ≫ (datum.{u} l E π hπ).projection T n =
      quotientProjection l E π T n ≫ (finite n).hom
  constants : ∀ (n : ℕ) (V : T.ProEtᵒᵖ) (a : PadicAlgCl.integers l E.1)
      (x : (quotientRing l E π T n).obj.obj V),
    HEq (((chartComparison T (completedResidue l E π n)).hom.app V) x)
        (ULift.up.{u + 1} (ContinuousMap.const V.unop.left
          (Ideal.Quotient.mk ((Ideal.span {π}) ^ (n + 1)) a))) →
      HEq ((finite n).hom.hom.app V x)
        ((finiteOriginConstantIso T
          (integers.{u} l E ⧸ (datum.{u} l E π hπ).ideal ^ (n + 1))).hom.hom.app V
            ((toSheafify (ProEt.topology T)
              ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
                (integers.{u} l E ⧸ (datum.{u} l E π hπ).ideal ^ (n + 1))))).app V
                  (quotientScalars.{u} l E π hπ n a)))


/-- The actual internal-module to adic-module equivalence is scalar restriction
along the normalized coefficient isomorphism, after the existing section encoding.
Source: Stacks 00YV; Bhatt--Scholze, Section 6.5
(blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
@[irreducible] def CoefficientModel.modules {π : PadicAlgCl.integers l E.1}
    {hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1)}
    {T : Scheme.{u}} (C : CoefficientModel l E π hπ T) :
    CategoryTheory.Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj.{u} l E.1) T) ≌
      reductionModules T ((datum.{u} l E π hπ).completedRing T) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology T)
    (condensedRingObj (Profinite.padicIntegersRingObj.{u} l E.1) T)).trans
      (CondensedRing.ringModuleEquivalenceOfIso.{u} T
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso C.completed.symm))

/-- The exact encoding preserves addition.
Source: Stacks 05RU (blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
instance CoefficientModel.modules_additive {π : PadicAlgCl.integers l E.1}
    {hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1)}
    {T : Scheme.{u}} (C : CoefficientModel l E π hπ T) :
    (C.modules.{u} l E).functor.Additive := by
  unfold CoefficientModel.modules
  exact ⟨fun {_ _ _ _} ↦ rfl⟩

/-- The inverse exact encoding preserves addition.
Source: Stacks 05RU (blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
instance CoefficientModel.modules_inverse_additive {π : PadicAlgCl.integers l E.1}
    {hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1)}
    {T : Scheme.{u}} (C : CoefficientModel l E π hπ T) :
    (C.modules.{u} l E).inverse.Additive :=
  Equivalence.inverse_additive _

/-- The section encoding is exact on the selected coefficient presentation.
Source: Stacks 05RU (blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
noncomputable def CoefficientModel.derived {π : PadicAlgCl.integers l E.1}
    {hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1)}
    {T : Scheme.{u}} (C : CoefficientModel l E π hπ T) :=
  (C.modules.{u} l E).mapDerivedCategory

/-- Exact finite coefficient encoding into fixed-scalar module sheaves.
It restricts along the canonical constants-to-functions map, then takes the
unchanged sheaf with its induced constant scalar action.
Source: Stacks 09BT and 03CY (blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
@[irreducible] def finiteFixed (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :=
  proEtaleRingRestrictScalars (finiteOriginConstantIso T Λ).hom ⋙
    ConstantScalarRestriction.restriction (ProEt.topology T) Λ

/-- The finite encoding is additive, as both restrictions keep additive maps.
Source: Stacks 03CY (blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
instance finiteFixed_additive (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] : (finiteFixed T Λ).Additive := by
  let := ConstantScalarRestriction.additive (ProEt.topology T) Λ
  unfold finiteFixed proEtaleRingRestrictScalars
  change (SheafOfModules.restrictScalars _ ⋙
    ConstantScalarRestriction.restriction (ProEt.topology T) Λ).Additive
  infer_instance

/-- Scalar restriction along a coefficient isomorphism is an equivalence.
Source: Stacks 03CY (blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
instance finiteFixed_preservesFiniteLimits (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] : PreservesFiniteLimits (finiteFixed T Λ) := by
  let := (proEtaleRingRestrictScalars_properties (finiteOriginConstantIso T Λ).hom).1
  let := ConstantScalarRestriction.isEquivalence (ProEt.topology T) Λ
  unfold finiteFixed
  exact inferInstanceAs (PreservesFiniteLimits
    (proEtaleRingRestrictScalars (finiteOriginConstantIso T Λ).hom ⋙
      ConstantScalarRestriction.restriction (ProEt.topology T) Λ))

/-- The same exact coefficient encoding preserves cokernels.
Source: Stacks 03CY (blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
instance finiteFixed_preservesFiniteColimits (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] : PreservesFiniteColimits (finiteFixed T Λ) := by
  let := (proEtaleRingRestrictScalars_properties (finiteOriginConstantIso T Λ).hom).2.1
  let := ConstantScalarRestriction.isEquivalence (ProEt.topology T) Λ
  unfold finiteFixed
  exact inferInstanceAs (PreservesFiniteColimits
    (proEtaleRingRestrictScalars (finiteOriginConstantIso T Λ).hom ⋙
      ConstantScalarRestriction.restriction (ProEt.topology T) Λ))

attribute [-instance] ConstantScalarRestriction.fixedAbelian
attribute [-instance] ConstantScalarRestriction.fixedPreadditive
attribute [-instance] ConstantScalarRestriction.fixedZeroMorphisms

/-- The same finite encoding on ordinary unbounded derived categories.
Source: Stacks 05RU (blueprint: def-sfb-integral-ambient-coefficient-presentation). -/
abbrev finiteDerivedFixed (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] :=
  (finiteFixed T Λ).mapDerivedCategory.{u + 2, u + 1}


end AlgebraicGeometry.Scheme.IntegralAmbientTower
