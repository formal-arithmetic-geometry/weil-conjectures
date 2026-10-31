/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerNormalized
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionWellDefined
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Exact field scalar extension of normalized strict quotient systems

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md, paragraph (1)
(blueprint: def-sp-field-scalar-system-data).

All tower values lie in the ordinary derived category of the recorded varying-ring
module category. The comparison below is a natural isomorphism in that category;
its normalization is imposed before localization, on entire complexes of strict towers.
Positive level n+1 is indexed by n : ℕ. The auxiliary records package conclusions,
not additional hypotheses. No functor is selected from their existence theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u a v w
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale.FieldScalar

/-- Finite powers as an actual functor, so the coordinate isomorphism retains all
morphisms and transitions. Source: paragraph (1), finite sums
(blueprint: def-sp-field-scalar-system-data). -/
def power {C : Type a} [Category.{v} C] [HasFiniteProducts C] (r : ℕ) : C ⥤ C :=
  Functor.pi' (fun _ : Fin r ↦ 𝟭 C) ⋙ Pi.functor (Fin r)

/-- Inclusion of a coordinate in a finite power in an additive category.
Source: paragraph (1), integral-basis columns
(blueprint: def-sp-field-scalar-system-data). -/
def column {C : Type a} [Category.{v} C] [HasFiniteProducts C] [HasZeroMorphisms C]
    (r : ℕ) (M : C) (i : Fin r) : M ⟶ (power r).obj M :=
  Pi.lift (fun j ↦ if i = j then 𝟙 M else 0)

variable (l : ℕ) [Fact l.Prime] (E F : Type u) [Field E] [Field F]
  [Algebra (Padic l) E] [Algebra (Padic l) F]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
  (ι : E →ₐ[Padic l] F) (T : Scheme.{u})

/-- The relative degree uses exactly the indicated inclusion.
Source: paragraph (1), r=[F:E] (blueprint: def-sp-field-scalar-system-data). -/
abbrev degree : ℕ :=
  @Module.finrank E F _ _ (Module.compHom F ι.toRingHom)

/-- The existing ring sheafification with its coefficient size fixed explicitly.
Source: the small-site convention (blueprint: def-sp-field-scalar-system-data). -/
instance (priority := 6000) ringSheafify :
    HasSheafify (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, u} T

/-- The small site is essentially small in its object universe.
Source: the small-site convention (blueprint: def-sp-field-scalar-system-data). -/
instance (priority := 6000) siteSmall : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The constant local section of the actual ell-power quotient sheaf.
Source: paragraph (1), reduction of a single integral basis
(blueprint: def-sp-field-scalar-system-data). -/
def constant (n : ℕ) (b : Padic.coefficientExtensionIntegers l E) (U : T.ProEtᵒᵖ) :
    ((spCoefficientCommRings.{u, u} l E T).obj (op n)).obj.obj U :=
  (spCoefficientConstantQuotient.{u, u} l E T n).hom.app U
    ((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))).app U
          (ULift.up b))

/-- The actual field inclusion at all ell-power quotients, and at the completed
coefficient sheaf, with their quotient normalizations. These are conclusions.
Source: paragraph (1), coefficient inclusions
(blueprint: def-sp-field-scalar-system-data). -/
structure Coefficients (DA : SpCoefficientTowersAbelian.{u, u} l E T)
    (DB : SpCoefficientTowersAbelian.{u, u} l F T)
    (RA : SpReductionTower l E T DA) (RB : SpReductionTower l F T DB) where
  /-- Algebraic quotient inclusion, determined on every residue class. -/
  quotient : ∀ n : ℕ,
    (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)) →+*
      (Padic.coefficientExtensionIntegers l F ⧸ spEllIdeal l F ^ (n + 1))
  quotient_mk : ∀ (n : ℕ) (x : Padic.coefficientExtensionIntegers l E),
    quotient n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (WeilConjectures.integralScalarIntegerInclusion l E F ι x)
  /-- A map of entire ring towers, including every quotient transition. -/
  tower : spCoefficientCommRings.{u, u} l E T ⟶ spCoefficientCommRings.{u, u} l F T
  tower_app : ∀ n : ℕ, tower.app (op n) =
    (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom ((ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).symm.toRingHom.comp
        ((quotient n).comp (ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).toRingHom)))
  /-- The map of the completed coefficient sheaves. -/
  integral : spIntegralSectionRing l E T ⟶ spIntegralSectionRing l F T
  integral_projection : ∀ n : ℕ,
    integral ≫ spIntegralReductionScalar l F T RB.coefficient n =
      spIntegralReductionScalar l E T RA.coefficient n ≫ tower.app (op n)

variable {l E F T ι}

/-- Restriction to a coefficient level along the actual field inclusion.
Source: paragraph (1), restricted underlying complex
(blueprint: def-sp-field-scalar-system-data). -/
abbrev restrictionLevel {DA : SpCoefficientTowersAbelian.{u, u} l E T}
    {DB : SpCoefficientTowersAbelian.{u, u} l F T}
    {RA : SpReductionTower l E T DA} {RB : SpReductionTower l F T DB}
    (c : Coefficients l E F ι T DA DB RA RB) (n : ℕ) :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (c.tower.app (op n)))

/-- An interval of cohomological support at every level, with no enlargement.
Source: paragraph (1), uniform cohomological bounds
(blueprint: def-sp-field-scalar-system-data). -/
def support (DA : SpCoefficientTowersAbelian.{u, u} l E T)
    (K : spDerivedCoefficientTowers l E T DA) (a b : ℤ) : Prop :=
  ∀ (n : ℕ) (i : ℤ), (i < a ∨ b < i) → IsZero
    ((@DerivedCategory.homologyFunctor
      (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T
        (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))
      _ _ (HasDerivedCategory.standard _) i).obj
      ((spDerivedCoefficientEvaluation l E T DA n).obj K))

/-- An interval of Tor amplitude common to all levels.
Source: paragraph (1), uniform Tor bounds
(blueprint: def-sp-field-scalar-system-data). -/
def tor (DA : SpCoefficientTowersAbelian.{u, u} l E T)
    (K : spDerivedCoefficientTowers l E T DA) (a b : ℤ) : Prop :=
  ∀ n : ℕ, Scheme.HasProEtaleTorAmplitude T
    (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
    ((spDerivedCoefficientEvaluation l E T DA n).obj K) a b

/-- The exact scalar functor and its canonical ordinary-derived realization.
All level identifications have their local tensor and transition normalizations.
Source: paragraph (1), finite-free exact extension of whole systems
(blueprint: def-sp-field-scalar-system-data). -/
structure ExactExtension (DA : SpCoefficientTowersAbelian.{u, u} l E T)
    (DB : SpCoefficientTowersAbelian.{u, u} l F T)
    (RA : SpReductionTower l E T DA) (RB : SpReductionTower l F T DB)
    (c : Coefficients l E F ι T DA DB RA RB) where
  /-- One integral basis for every positive quotient level. -/
  basis : Fin (degree l E F ι) → Padic.coefficientExtensionIntegers l F
  basis_expansion : ∀ x : Padic.coefficientExtensionIntegers l F,
    ∃! a : Fin (degree l E F ι) → Padic.coefficientExtensionIntegers l E,
      x = ∑ i, WeilConjectures.integralScalarIntegerInclusion l E F ι (a i) * basis i
  /-- Reduction of precisely that basis is a basis of each quotient. -/
  quotient_basis : ∀ (n : ℕ)
    (x : Padic.coefficientExtensionIntegers l F ⧸ spEllIdeal l F ^ (n + 1)),
    ∃! a : Fin (degree l E F ι) →
        (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)),
      x = ∑ i, c.quotient n (a i) * Ideal.Quotient.mk _ (basis i)
  /-- Scalar extension on the actual strict tower categories. -/
  ordinary : spCoefficientTowers.{u, u} l E T ⥤ spCoefficientTowers.{u, u} l F T
  [additive : ordinary.Additive]
  [limits : PreservesFiniteLimits ordinary]
  [colimits : PreservesFiniteColimits ordinary]
  /-- Its levels are the specified sheafified tensor functors. -/
  level : ∀ n : ℕ, ordinary ⋙ spCoefficientEvaluation.{u, u} l F T DB.equivalence n ≅
    spCoefficientEvaluation.{u, u} l E T DA.equivalence n ⋙ (DA.scalar (c.tower.app (op n))).model.E
  /-- Every transition is t(x) tensor q(b), including composite and equal indices. -/
  transition : ∀ (M : spCoefficientTowers.{u, u} l E T) {m n : ℕ} (h : m ≤ n)
    (U : T.ProEtᵒᵖ) (b : ((spCoefficientCommRings.{u, u} l F T).obj (op n)).obj.obj U)
    (x : ((DA.equivalence.functor.obj M).level n).val.obj U),
    ((level m).hom.app M).val.app U
      (spStrictTransitionSection.{u} T (spCoefficientCommRings.{u, u} l F T)
        (DB.equivalence.functor.obj (ordinary.obj M)) h U
        (((level n).inv.app M).val.app U
          (systemModelTmul (DA.scalar (c.tower.app (op n))).model _ U b x))) =
    systemModelTmul (DA.scalar (c.tower.app (op m))).model _ U
      (((spCoefficientCommRings.{u, u} l F T).map (homOfLE h).op).hom.app U b)
      (spStrictTransitionSection.{u} T (spCoefficientCommRings.{u, u} l E T)
        (DA.equivalence.functor.obj M) h U x)
  /-- Restriction along the inclusion, simultaneously at all levels. -/
  restriction : spCoefficientTowers.{u, u} l F T ⥤ spCoefficientTowers.{u, u} l E T
  [restrictionAdditive : restriction.Additive]
  [restrictionLimits : PreservesFiniteLimits restriction]
  [restrictionColimits : PreservesFiniteColimits restriction]
  restriction_level : ∀ n : ℕ,
    restriction ⋙ spCoefficientEvaluation.{u, u} l E T DA.equivalence n ≅
      spCoefficientEvaluation.{u, u} l F T DB.equivalence n ⋙ restrictionLevel c n
  restriction_sections : ∀ (M : spCoefficientTowers.{u, u} l F T) (n : ℕ) (U : T.ProEtᵒᵖ),
    HEq (fun x ↦ ((restriction_level n).hom.app M).val.app U x)
      (fun x : ((DA.equivalence.functor.obj (restriction.obj M)).level n).val.obj U ↦ x)
  restriction_transitions : ∀ (M : spCoefficientTowers.{u, u} l F T) {m n : ℕ} (h : m ≤ n)
    (U : T.ProEtᵒᵖ)
    (x : ((DA.equivalence.functor.obj (restriction.obj M)).level n).val.obj U),
    ((restriction_level m).hom.app M).val.app U
      (spStrictTransitionSection.{u} T (spCoefficientCommRings.{u, u} l E T)
        (DA.equivalence.functor.obj (restriction.obj M)) h U x) =
    spStrictTransitionSection.{u} T (spCoefficientCommRings.{u, u} l F T)
      (DB.equivalence.functor.obj M) h U
      (((restriction_level n).hom.app M).val.app U x)
  /-- The same finite coordinate decomposition on whole systems, natural in M. -/
  coordinates : power (degree l E F ι) ≅ ordinary ⋙ restriction
  /-- Each column tensors with the reduction of the one integral basis vector. -/
  coordinates_column : ∀ (M : spCoefficientTowers.{u, u} l E T) (i : Fin (degree l E F ι))
    (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : ((DA.equivalence.functor.obj M).level n).val.obj U),
    ((restriction_level n).hom.app (ordinary.obj M)).val.app U
      (((spCoefficientEvaluation.{u, u} l E T DA.equivalence n).map
        (column (degree l E F ι) M i ≫ coordinates.hom.app M)).val.app U x) =
    ((level n).inv.app M).val.app U
      (systemModelTmul (DA.scalar (c.tower.app (op n))).model _ U
        (constant l F T n (basis i) U) x)
  /-- Scalar extension on ordinary unbounded derived categories of whole towers. -/
  derived : spDerivedCoefficientTowers l E T DA ⥤ spDerivedCoefficientTowers l F T DB
  /-- The counit identifying its value with termwise extension. -/
  counit : spTowerLocalization l E T DA ⋙ derived ⟶
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ spTowerLocalization l F T DB
  universal : derived.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (spCoefficientTowers.{u, u} l E T) (.up ℤ))
  /-- Exactness makes this comparison invertible on every complex. -/
  computes_all : ∀ P : CochainComplex (spCoefficientTowers.{u, u} l E T) ℤ,
    IsIso (counit.app P)
  /-- The actual whole-system scalar extension evaluates to derived scalar extension. -/
  derived_level : ∀ n : ℕ,
    derived ⋙ spDerivedCoefficientEvaluation l F T DB n ≅
      spDerivedCoefficientEvaluation l E T DA n ⋙ (DA.scalar (c.tower.app (op n))).model.T
  /-- Normalization, constructibility, and existence of uniform bounds are retained. -/
  normalized : ∀ K : spDerivedCoefficientTowers l E T DA,
    spNormalizedConstructibleTorTowers l E T DA K →
      spNormalizedConstructibleTorTowers l F T DB (derived.obj K)
  /-- Every prescribed common cohomological interval is retained, without enlargement. -/
  support_preserved : ∀ (K : spDerivedCoefficientTowers l E T DA) (a b : ℤ),
    support DA K a b → support DB (derived.obj K) a b
  /-- Every prescribed common Tor interval is retained, without enlargement. -/
  tor_preserved : ∀ (K : spDerivedCoefficientTowers l E T DA) (a b : ℤ),
    tor DA K a b → tor DB (derived.obj K) a b

attribute [instance] SpReductionTower.additive ExactExtension.additive
  ExactExtension.restrictionAdditive ExactExtension.restrictionLimits
  ExactExtension.restrictionColimits

end AlgebraicGeometry.ProEtale.FieldScalar
