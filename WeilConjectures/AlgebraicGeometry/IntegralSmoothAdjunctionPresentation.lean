/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralAdjunctionBijection
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructibleLinear
public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.SfScalarExtensionComposition
public import WeilConjectures.Topology.ContinuousMapCondensedRingMap
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower
public import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingUniverses
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.RationalLocalizedHom
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionUniverses
public import WeilConjectures.CategoryTheory.SemilinearScalarLocalization
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.CategoryTheory.KInjectiveTotalDerivedLinear
import WeilConjectures.CategoryTheory.LinearRightAdjoint
import WeilConjectures.Algebra.Homology.OrdinaryLineDerivedScalarComparison
import WeilConjectures.Algebra.Homology.DerivedTensorAdditiveConstraints

/-! # Raw rationalization of the smooth adjunction diagrams

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension, sole proof
paragraph, final sentence; sk-prop-sp-rational/sk-prop-sp-rational-adjunction.proof.md,
part (1) (blueprint: def-pur-integral-smooth-adjunction-presentation).

The integral presentation retains the tower adjunction and its realized purity map.
Raw localization and the condensed realization remain different categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u r v w x y
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open WeilConjectures AlgebraicGeometry.ProEtale

attribute [instance] WeilConjectures.sfIntegralConstructibleLinear
  WeilConjectures.sfIntegralCoefficientLinear

namespace WeilConjectures.RationalizedSmoothAdjunction

section SingleCoefficient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)] (d : ℕ)

/-- The already supplied entire-tower adjunction and its normalized integral realization.
Every field is input data from det-sp-integral-adjunction-bijection, including the
comparison to the actual completed pullback, Tate tensor and shift.
Source: integral-adjunction-bijection, Normalization, Bijections and Purity
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
structure Presentation where
  base : ProEtale.SpTowerShriek.Base l E
  operations : ProEtale.SpTowerShriek.Operations l E base
  coordinates : ProEtale.SpTowerCalculus.Coordinates l E base
  twists : ProEtale.SpChartAdmissibility.Twists l E X
  reductionX : SpReductionTower l E X (coordinates.abelian X)
  normalizationX : SpNormalizedEquivalence l E X (coordinates.abelian X) reductionX
  reductionY : SpReductionTower l E Y (coordinates.abelian Y)
  normalizationY : SpNormalizedEquivalence l E Y (coordinates.abelian Y) reductionY
  supportClosed : ∀ M : ProEtale.SpTowerCalculus.C l E base coordinates X,
    spConstructibleTorTowers l E Y (coordinates.abelian Y)
      ((ProEtale.SpTowerCalculus.F l E base operations coordinates
        (ProEtale.SpTowerGamma.factorization j p)).obj M.obj)
  right : ProEtale.SpTowerCalculus.C l E base coordinates Y ⥤
    ProEtale.SpTowerCalculus.C l E base coordinates X
  adjunction : ProEtale.SpTowerGluing.support l E base operations coordinates
    (ProEtale.SpTowerGamma.factorization j p) supportClosed ⊣ right
  levels : ProEtale.SpTowerGluing.Levels l E base operations coordinates
    (ProEtale.SpTowerGamma.factorization j p) supportClosed right adjunction
  realization : ProEtale.SpIntegralAdjunction.Realization l E base operations coordinates
    j p d twists reductionX normalizationX reductionY normalizationY
    supportClosed right adjunction levels

variable (s : Presentation l E j p d)

/-- The actual completed compactification composite restricted to integral constructibles.
Source: integral adjunction Bijections; integral-direct-image-tower clause (2)
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
abbrev P : sfIntegralConstructibleCategory l E X ⥤
    sfIntegralConstructibleCategory l E Y := ProEtale.SpIntegralAdjunction.support l E
  (ProEtale.SpTowerGamma.factorization j p) s.realization.support_closed

/-- The actual integral right adjoint obtained by total limit of the tower right adjoint.
Source: integral adjunction Normalization
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
abbrev J : sfIntegralConstructibleCategory l E Y ⥤
    sfIntegralConstructibleCategory l E X :=
  ProEtale.SpIntegralAdjunction.right l E s.base s.coordinates
  s.reductionX s.normalizationX s.reductionY s.realization.reductionY
  s.right s.realization.closed

/-- Completed derived pullback, tensor by the signed Tate line, then shift by 2d.
Source: integral adjunction Purity; def-coefficient-twists-detailed
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
def H : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X :=
  ObjectProperty.lift _ (SpTwistedPullback.source l E (j ≫ p) (d : ℤ) (2 * (d : ℤ)))
    s.realization.source_complete

/-- The specified integral purity component, including the reconstruction unit and
entire-system gamma, rather than an arbitrary isomorphism of right adjoints.
Source: integral-adjunction-bijection, final Purity display
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
@[irreducible]
def gammaComponent (K : sfIntegralConstructibleCategory l E Y) :
    (H l E j p d s).obj K ⟶ (J l E j p d s).obj K :=
  letI := s.realization.noetherianX
  letI := s.realization.noetherianY
  ObjectProperty.homMk
    (s.normalizationX.adjunction.unit.app
        ((SpTwistedPullback.source l E (j ≫ p) (d : ℤ) (2 * (d : ℤ))).obj K) ≫
      (ProEtale.SpIntegralAdjunction.limit l E X (s.coordinates.abelian X)
        s.reductionX s.normalizationX).map
        ((ProEtale.SpTowerCalculus.realization l E s.base X
          (s.coordinates.abelian X)).unitIso.hom.app _ ≫
          (ProEtale.SpTowerCalculus.realization l E s.base X
            (s.coordinates.abelian X)).inverse.map
            (s.realization.sourceComparison.hom.app K ≫
              ProEtale.SpTowerGamma.gamma l E s.base s.operations s.coordinates
                (ProEtale.SpTowerGamma.factorization j p) s.twists d
                s.realization.purity.tensorX s.realization.purity.tensorY
                s.supportClosed s.right s.adjunction s.realization.purity.unit_mem
                s.realization.purity.orientation
                ((ProEtale.SpIntegralAdjunction.reduce l E Y (s.coordinates.abelian Y)
                  s.reductionY s.realization.reductionY).obj K)
                (s.realization.purity.tensor_mem _) (s.realization.purity.projection_iso _)) ≫
          (ProEtale.SpTowerCalculus.realization l E s.base X
            (s.coordinates.abelian X)).unitIso.inv.app _))

end SingleCoefficient

section CondensedRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The completed-to-internal equivalence specified by the normalized coefficient map.
Source: integral-direct-image-tower, section encoding and clause (2)
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
@[irreducible]
def internalization (W : Scheme.{u}) (A : SpCoefficientTowersAbelian l E W)
    (R : SpReductionTower l E W A) :
    DerivedCategory (scalarReductionSource l E W) ≌
      ProEtale.IntegralDirectImageTower.Integral l E W :=
  let e : SheafOfModules.{u + 1} (completedIntegralCoefficientSheafUnrestricted l E W) ≌
      spIntegralSectionModules l E W := CondensedRing.ringModuleEquivalenceOfIso W
    ((sheafCompose (Scheme.ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      R.coefficient)
  letI : e.functor.Additive := Functor.additive_of_preserves_binary_products e.functor
  letI : e.inverse.Additive := Functor.additive_of_preserves_binary_products e.inverse
  e.mapDerivedCategory.trans
    (ProEtale.IntegralDirectImageTower.sectionEquivalence l E W).symm

/-- The continuous coefficient field, with the spectral extension of the p-adic norm.
Source: coefficient conventions and rational-localized-hom
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
def rationalRing : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  letI := spectralNorm.normedField (Padic l) E
  { X := Profinite.continuousMapRingObjOfUniverse E
    mon := Profinite.continuousMapRingObjOfUniverseMonObj E }

/-- Commutativity is the pointwise commutativity of the continuous field.
Source: rational-localized-hom
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
instance rationalRingComm : IsCommMonObj (rationalRing l E).X :=
  letI := spectralNorm.normedField (Padic l) E
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse E

/-- The actual continuous integral inclusion, before inverse image to a scheme.
Source: rational-localized-hom, h maps to h[1/ell]
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
def invertMap : spIntegralCondensed l E ⟶ (rationalRing l E).X :=
  letI := spectralNorm.normedField (Padic l) E
  Profinite.continuousMapRingObjMapOfUniverse
    (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val

/-- The coefficient inclusion preserves the actual ring-object multiplication and unit.
Source: rational-localized-hom
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
instance invertMapMon : IsMonHom (invertMap l E) :=
  letI := spectralNorm.normedField (Padic l) E
  Profinite.isMonHom_continuousMapRingObjMapOfUniverse
    (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val

/-- The condensed rational ambient category, separate from raw scalar localization.
Source: rational-localized-hom
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
abbrev Condensed (W : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
    (condensedRingObj (rationalRing l E).X W))

/-- Inverting ell is the specified total derived extension of scalars.
Source: rational-localized-hom
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
@[irreducible]
def invert (W : Scheme.{u}) :
    ProEtale.IntegralDirectImageTower.Integral l E W ⥤ Condensed l E W :=
  (Mod.extendScalars (coefficientMap (invertMap l E) W)).leftDerivedFunctor

/-- The canonical rationalization of completed integral constructibles, using the
specified integral coefficient encoding, not an identification of category types.
Source: rational-localized-hom and integral-direct-image-tower clause (2)
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
@[irreducible]
def realize (W : Scheme.{u}) (A : SpCoefficientTowersAbelian l E W)
    (R : SpReductionTower l E W A) :
    sfIntegralConstructibleCategory l E W ⥤ Condensed l E W :=
  (sfIntegralConstructible l E W).ι ⋙
    (internalization l E W A R).functor ⋙ invert l E W

/-- Constant continuous scalar sections, in the same universe as the scheme.
Source: rational-localized-hom, scalar action on Hom
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
@[irreducible]
def fieldScalarSections (W : Scheme.{u}) :
    letI := spectralNorm.normedField (Padic l) E
    E →+* RingCat.sectionsSubring (continuousCoefficientRingSheaf W E).obj :=
  letI := spectralNorm.normedField (Padic l) E
  { toFun a := ⟨fun _ ↦ ULift.up (ContinuousMap.const _ a), fun _ ↦ rfl⟩
    map_one' := rfl
    map_mul' _ _ := rfl
    map_zero' := rfl
    map_add' _ _ := rfl }

/-- Continuous coefficient sections retaining commutativity before forgetting to rings.
Source: rational-localized-hom, constant-section scalar action
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
def fieldPresheaf (W : Scheme.{u}) : W.ProEtᵒᵖ ⥤ CommRingCat.{u + 1} :=
  letI := spectralNorm.normedField (Padic l) E
  { obj V := CommRingCat.of (ULift.{u + 1} C(V.unop.left, E))
    map f := CommRingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp
        (((ContinuousMap.compRightAlgHom ℤ E f.unop.left.base.hom).toRingHom).comp
          ULift.ringEquiv.toRingHom))
    map_id _ := rfl
    map_comp _ _ := rfl }

/-- The field action on the encoded ordinary module category.
Source: rational-localized-hom, constant-section scalar action
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
@[instance_reducible]
def fieldLinear (W : Scheme.{u}) :
    letI := spectralNorm.normedField (Padic l) E
    Linear E (SheafOfModules.{u + 1} (continuousCoefficientRingSheaf W E)) :=
  letI := spectralNorm.normedField (Padic l) E
  letI : Linear (RingCat.sectionsSubring (continuousCoefficientRingSheaf W E).obj)
      (SheafOfModules.{u + 1} (continuousCoefficientRingSheaf W E)) :=
    SheafOfModules.homLinear (fieldPresheaf l E W)
      (continuousCoefficientRingSheaf W E).property
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) (fieldScalarSections l E W)
    smul_comp := fun M N P a f g ↦
      Linear.smul_comp M N P (fieldScalarSections l E W a) f g
    comp_smul := fun M N P f a g ↦
      Linear.comp_smul M N P f (fieldScalarSections l E W a) g }

/-- The actual continuous section encoding of the rational internal derived category.
Source: rational-localized-hom, identification with completed coefficient coordinates
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
@[irreducible]
def fieldEncoding (W : Scheme.{u}) :
    letI := spectralNorm.normedField (Padic l) E
    Condensed l E W ≌ DerivedCategory
      (SheafOfModules.{u + 1} (continuousCoefficientRingSheaf W E)) :=
  letI := spectralNorm.normedField (Padic l) E
  letI := spectralNorm.normedAlgebra (Padic l) E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra (Padic l)
  let e := CondensedRing.continuousRingModuleEquivalenceUniverse W E
  letI : e.functor.Additive := Functor.additive_of_preserves_binary_products e.functor
  letI : e.inverse.Additive := Functor.additive_of_preserves_binary_products e.inverse
  e.mapDerivedCategory

/-- Derived encoding is additive because it is an equivalence of additive categories.
Source: rational-localized-hom, scalar action transported through encoding
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
instance fieldEncodingAdditive (W : Scheme.{u}) :
    (fieldEncoding l E W).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Hom scalar action transported through the actual section encoding.
Source: rational-localized-hom, B-linearity
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
@[instance_reducible]
def fieldHomModule (W : Scheme.{u}) (M N : Condensed l E W) : Module E (M ⟶ N) :=
  letI := spectralNorm.normedField (Padic l) E
  letI := fieldLinear l E W
  AddEquiv.module E
    { (fieldEncoding l E W).fullyFaithfulFunctor.homEquiv with
      map_add' := fun f g ↦ (fieldEncoding l E W).functor.map_add (f := f) (g := g) }

/-- Restrict the same field action along the canonical localized coefficient isomorphism.
Source: rational-localized-hom, pure tensors
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
instance localizedHomModule (W : Scheme.{u}) (M N : Condensed l E W) :
    Module (Localization.Away (Padic.coefficientExtensionUniformizer l E)) (M ⟶ N) :=
  letI := fieldHomModule l E W M N
  Module.compHom (M ⟶ N) (sfRationalCoefficientEquiv l E).toRingHom

variable {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (p : Z ⟶ Y) [IsProper p] [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
  (d : ℕ) (s : Presentation l E j p d)

/-- Realization of integral objects on X with its specified reduction coordinates.
Source: rational-localized-hom
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
abbrev realizeX := realize l E X (s.coordinates.abelian X) s.reductionX

/-- Realization of integral objects on Y with its specified reduction coordinates.
Source: rational-localized-hom
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
abbrev realizeY := realize l E Y (s.coordinates.abelian Y) s.reductionY

/-- The separately derived compactification composite over the continuous field.
Source: integral-direct-image-tower clause (2), then invert ell
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
abbrev condensedP : Condensed l E X ⥤ Condensed l E Y :=
  CondensedRing.rightDerivedLowerShriekOfCompactification (rationalRing l E).X
    (ProEtale.SpTowerGamma.factorization j p)

/-- The integral Tate line in the internal coefficient coordinates, then inverted.
Source: coefficient-twists-detailed; ordinary-line-derived-scalar-comparison
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
@[irreducible]
def rationalLine : Condensed l E X :=
  (invert l E X).obj ((internalization l E X (s.coordinates.abelian X)
    s.reductionX).functor.obj
      ((DerivedCategory.singleFunctor (scalarReductionSource l E X) 0).obj
        (integralTwistLine l E X (d : ℤ))))

/-- Actual rational derived pullback, tensor with the rational Tate line, and shift.
Source: rational-adjunction proof (1), last endpoint
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
@[irreducible]
def condensedH : Condensed l E Y ⥤ Condensed l E X :=
  CondensedRing.moduleObjectDerivedPullback (rationalRing l E).X (j ≫ p) ⋙
    (CondensedRing.derivedTensor (rationalRing l E).X X).flip.obj
      (rationalLine l E j p d s) ⋙ shiftFunctor _ (2 * (d : ℤ))

/-- The endpoint identifications used in the source's three Hom bijections.
The first is the canonical compactification/derived-limit comparison of clause (2).
The second is the canonical pullback scalar comparison, derived tensor associativity
and the shift comparison (the line has degree zero). These are comparisons of the
actual functors, not equalities of raw and condensed categories.
Source: rational-adjunction proof (1), first and third Hom bijections
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
structure Endpoints where
  compactSupport : P l E j p d s ⋙ realizeY l E j p d s ≅
    realizeX l E j p d s ⋙ condensedP l E j p
  twistedPullback : H l E j p d s ⋙ realizeX l E j p d s ≅
    realizeY l E j p d s ⋙ condensedH l E j p d s

/-- The prescribed Hom comparison, as supplied by rational-localized-hom, in the
completed integral coordinates. Its source is the actual raw tensor Hom, and its
normalization is the integral-to-rational functor on arrows. Linearity is recorded
in raw localized coefficient coordinates; sfRationalCoefficientEquiv identifies these
with E without changing objects or adjoining idempotents.
Source: rational-localized-hom, pure tensor formula
(blueprint: def-pur-integral-smooth-adjunction-presentation). -/
structure HomComparisons where
  rhoX : ∀ M N : sfIntegralConstructibleCategory l E X,
    ((sfRationalConstructibleLocalization l E X).obj M ⟶
      (sfRationalConstructibleLocalization l E X).obj N) ≃ₗ[
        Localization.Away (Padic.coefficientExtensionUniformizer l E)]
        ((realizeX l E j p d s).obj M ⟶ (realizeX l E j p d s).obj N)
  rhoY : ∀ M N : sfIntegralConstructibleCategory l E Y,
    ((sfRationalConstructibleLocalization l E Y).obj M ⟶
      (sfRationalConstructibleLocalization l E Y).obj N) ≃ₗ[
        Localization.Away (Padic.coefficientExtensionUniformizer l E)]
        ((realizeY l E j p d s).obj M ⟶ (realizeY l E j p d s).obj N)
  integralX : ∀ (M N : sfIntegralConstructibleCategory l E X) (f : M ⟶ N),
    rhoX M N ((sfRationalConstructibleLocalization l E X).map f) =
      (realizeX l E j p d s).map f
  integralY : ∀ (M N : sfIntegralConstructibleCategory l E Y) (f : M ⟶ N),
    rhoY M N ((sfRationalConstructibleLocalization l E Y).map f) =
      (realizeY l E j p d s).map f

end CondensedRealization

end WeilConjectures.RationalizedSmoothAdjunction
