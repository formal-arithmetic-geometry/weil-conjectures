/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.SixFunctors.GeneratorReductionStatement
public import Sheaf.Paper.SfCbcCompactSupportCompositionLimit
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-! # Constant semilinear comparison for a single proper or open operation

Source: Stacks Project, Tag 0E48, remark-compatible-with-diagram;
blueprint fix-lem-exchanges, Step 5
(blueprint: lem-sf-constant-semilinear-generator-comparison).

The constant tower is over the constant valuation-ring sheaf, rather than the completed
ring sheaf. All derived categories localize strict diagrams before taking evaluations.
Proper and open operations are single letters, not structural `GeneratorKind` values.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i vB vC wB wC dB dC a₁ a₂ a₃ a₄ h₁ h₂ h₃ h₄ d₁ d₂ d₃ d₄
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace WeilConjectures.GeneratorReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual valuation ring. Source: blueprint coefficient convention
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
abbrev constantRing := Padic.coefficientExtensionIntegers l E

/-- The uniformizer ideal, without an additional coefficient choice.
Source: blueprint coefficient convention
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
abbrev constantIdeal : Ideal (constantRing l E) :=
  Ideal.span {Padic.coefficientExtensionUniformizer l E}

/-- Properties of the fixed DVR needed by the existing constant-tower calculus.
Source: Serre, Local Fields II.2; Stacks 099M
(blueprint: lem-sf-constant-semilinear-generator-comparison).
Proof: the valuation ring is a Noetherian DVR with finite residue field. Its uniformizer
ideal is principal. The residue ring is finite and hence additively torsion; the two-term
resolution by multiplication by the nonzero uniformizer power proves perfectness of each
positive quotient. Finiteness is finite_coefficientExtensionRing. -/
theorem constantCoefficientProperties :
    IsNoetherianRing (constantRing l E) ∧ (constantIdeal l E).FG ∧
    (∀ x : constantRing l E ⧸ constantIdeal l E,
      ∃ m : ℕ, 0 < m ∧ m • x = 0) ∧
    (∀ n : ℕ, 1 ≤ n → adicQuotientPerfect (constantRing l E) (constantIdeal l E) n) ∧
    (∀ n : ℕ, Finite (constantRing l E ⧸ (constantIdeal l E) ^ (n + 1))) := by
  sorry

/-- The fixed coefficient datum, with real ideal data and only postponed proofs.
Source: Stacks 099M (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def constantDatum : CompleteCoefficientDatum (constantRing l E) where
  ideal := constantIdeal l E
  noetherian := (constantCoefficientProperties l E).1
  finitelyGenerated := (constantCoefficientProperties l E).2.1
  quotientTorsion := (constantCoefficientProperties l E).2.2.1
  quotientPerfect := (constantCoefficientProperties l E).2.2.2.1

/-- The reduction of the completion unit is invertible, as already stated by the CBC node.
Source: blueprint fix-lem-exchanges, Step 2
(blueprint: lem-sf-constant-semilinear-generator-comparison).
Proof: apply sfCbcCompactSupportCompositionLimit to constantDatum. The positive
quotients are finite by constantCoefficientProperties. Its first existential
conclusion is exactly the invertibility of reduction of the completion unit. -/
theorem constantReducedUnits : SfCbcReducedUnitsInvertible (constantDatum l E) := by
  sorry

/-- Ordinary restriction from completed scalars, followed by the published small-site model.
Source: Stacks 099I and 00VC
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
@[irreducible] def ordinaryH (T : Scheme.{u}) :
    scalarReductionSource l E T ⥤ ConstantCompletion.Mod (sfCbcModelRing T (constantRing l E)) :=
  SheafOfModules.restrictScalars (integralConstantToCompletionOfUniverses l E T) ⋙
    sfCbcModelModules T (constantRing l E)

/-- Restriction is exact and small-site transport is an exact additive equivalence.
Source: Stacks 099I and 00VC
(blueprint: lem-sf-constant-semilinear-generator-comparison).
Proof: the composite of restriction with the faithful forgetful functor is the original
underlying abelian sheaf; it preserves kernels and cokernels. Transport by AsSmall.down
and the canonical constant-ring comparison is an additive equivalence and is exact. -/
theorem ordinaryH_exact (T : Scheme.{u}) :
    (ordinaryH l E T).Additive ∧ PreservesFiniteLimits (ordinaryH l E T) ∧
      PreservesFiniteColimits (ordinaryH l E T) := by
  sorry

/-- Additivity of the canonical ordinary scalar restriction. Source: Stacks 099I
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
instance ordinaryH_additive (T : Scheme.{u}) : (ordinaryH l E T).Additive :=
  (ordinaryH_exact l E T).1

/-- Exact scalar restriction preserves finite limits. Source: Stacks 099I
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
instance ordinaryH_limits (T : Scheme.{u}) : PreservesFiniteLimits (ordinaryH l E T) :=
  (ordinaryH_exact l E T).2.1

/-- Exact scalar restriction preserves finite colimits. Source: Stacks 099I
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
instance ordinaryH_colimits (T : Scheme.{u}) : PreservesFiniteColimits (ordinaryH l E T) :=
  (ordinaryH_exact l E T).2.2

/-- `H_T`, exact derived restriction along constant-to-completed coefficients.
Source: Stacks 099I (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def H (T : Scheme.{u}) : DerivedCategory (scalarReductionSource l E T) ⥤
    (sfCbcSite T).derived (ULift.{u + 1} (constantRing l E)) := (ordinaryH l E T).mapDerivedCategory

/-- `T_T`, the strict constant-ring tower, in the published equivalent small model.
Source: Stacks 0941 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
abbrev constantTowerCategory (T : Scheme.{u}) :=
  ℕᵒᵖ ⥤ ConstantCompletion.Mod (sfCbcModelRing T (constantRing l E))

/-- The actual termwise restriction from varying-ring systems to constant-ring towers.
Source: Stacks 0941 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def ordinaryU (T : Scheme.{u}) : coefficientSequenceModules l E T ⥤
    constantTowerCategory l E T :=
  coefficientSequenceRestriction l E T ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (ordinaryH l E T)

/-- Additivity of the termwise scalar restriction. Source: Stacks 0941
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
instance ordinaryU_additive (T : Scheme.{u}) : (ordinaryU l E T).Additive := by
  dsimp [ordinaryU]
  infer_instance

/-- Exactness of termwise scalar restriction in the strict diagram category.
Source: Stacks 0941 (blueprint: lem-sf-constant-semilinear-generator-comparison).
Proof: kernels and cokernels of strict diagrams are computed at every index.
The completed-scalar restriction and ordinaryH are exact on each such component,
so their composite preserves both finite limits and finite colimits. -/
theorem ordinaryU_exact (T : Scheme.{u}) :
    PreservesFiniteLimits (ordinaryU l E T) ∧
      PreservesFiniteColimits (ordinaryU l E T) := by
  sorry

/-- Left exactness of strict scalar restriction. Source: Stacks 0941
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
instance ordinaryU_limits (T : Scheme.{u}) : PreservesFiniteLimits (ordinaryU l E T) :=
  (ordinaryU_exact l E T).1

/-- Right exactness of strict scalar restriction. Source: Stacks 0941
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
instance ordinaryU_colimits (T : Scheme.{u}) : PreservesFiniteColimits (ordinaryU l E T) :=
  (ordinaryU_exact l E T).2

/-- `U_T`, derived termwise scalar restriction on the strict diagram.
Source: Stacks 0941 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def U (T : Scheme.{u}) : coefficientSequenceDerived l E T ⥤
    (sfCbcSite T).towerDerived (ULift.{u + 1} (constantRing l E)) :=
  (ordinaryU l E T).mapDerivedCategory

/-- The constant-tower reduction fixed by one strict quotient diagram.
Source: blueprint fix-lem-exchanges, Step 5
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
abbrev constantReduction (T : Scheme.{u}) :=
  (sfCbcSite T).reduction _ (sfCbcModelIdeal (constantDatum l E))

/-- Total right derived limit in the constant tower.
Source: Stacks 0941 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
abbrev constantLimit (T : Scheme.{u}) := (sfCbcSite T).rlim (ULift.{u + 1} (constantRing l E))

/-- Termwise exact restriction between completed and constant coefficient towers.
Source: Stacks 0941 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
abbrev towerH (T : Scheme.{u}) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (ordinaryH l E T)

/-- The ordinary strict quotient diagram over completed coefficients.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
abbrev ordinaryCompletedReduction (T : Scheme.{u}) :=
  (Functor.ofOpSequence (sfReductionTransition l E T)).flip

/-- Additivity holds componentwise for the strict completed quotient diagram.
Source: Stacks 0941 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
instance ordinaryCompletedReduction_additive (T : Scheme.{u}) :
    (ordinaryCompletedReduction l E T).Additive := by
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  exact (sfReductionRestricted l E T n.unop).map_add

/-- The ordinary quotient diagram over constant coefficients, before localization.
Source: Stacks 099M (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
abbrev ordinaryConstantReduction (T : Scheme.{u}) :=
  ConstantCompletion.reductionTower (proEtaleModelTopology T)
    (ULift.{u + 1} (constantRing l E)) (sfCbcModelIdeal (constantDatum l E)) false

/-- Scalar extension and restriction preserve addition, level by level.
Source: Stacks 0941 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
instance ordinaryConstantReduction_additive (T : Scheme.{u}) :
    (ordinaryConstantReduction l E T).Additive := by
  dsimp [ordinaryConstantReduction]
  infer_instance

/-- The composite ordinary constant reduction preserves zero maps.
Source: Stacks 0941 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
instance ordinaryHReduction_zero (T : Scheme.{u}) :
    (ordinaryH l E T ⋙ ordinaryConstantReduction l E T).PreservesZeroMorphisms := by
  have : (ordinaryConstantReduction l E T).Additive :=
    ordinaryConstantReduction_additive l E T
  infer_instance

/-- The strict scalar comparison is uniquely fixed by the scalar-extension units.
Source: Stacks 07A4, 06YY; node proof Step 5
(blueprint: lem-sf-constant-semilinear-generator-comparison).
Proof: tensor reassociation identifies both towers with the same quotient complex.
The comparison sends the class of an input section to itself. The displayed unit
condition determines the maps from the quotient modules, by the scalar adjunction.
It also proves naturality and compatibility with every quotient transition. -/
theorem ordinaryRho_existsUnique (T : Scheme.{u}) :
    ∃! e : ordinaryCompletedReduction l E T ⋙ towerH l E T ≅
        ordinaryH l E T ⋙ ordinaryConstantReduction l E T,
      ∀ (M : scalarReductionSource l E T) (n : ℕ),
        (ordinaryH l E T).map
            ((scalarReductionExtension_adjunction l E T n).choose.unit.app M) ≫
          (e.hom.app M).app (op n) =
        ((ConstantCompletion.reductionUnit (proEtaleModelTopology T)
          (ULift.{u + 1} (constantRing l E)) (sfCbcModelIdeal (constantDatum l E)) false).app
            ((ordinaryH l E T).obj M)).app (op n) := by
  sorry

/-- The unique unit-normalized ordinary scalar comparison, on the whole strict tower.
Source: node proof Step 5
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def ordinaryRho (T : Scheme.{u}) := (ordinaryRho_existsUnique l E T).exists.choose

/-- Evaluation of scalar restriction uses the recorded ordinary evaluation identity.
Source: Stacks 0941 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def ordinaryUEvaluation (T : Scheme.{u}) (n : ℕ) :
    ordinaryU l E T ⋙ (evaluation ℕᵒᵖ _).obj (op n) ≅
      coefficientSequenceEvaluation l E T n ⋙
        scalarReductionRestriction l E T n ⋙ ordinaryH l E T :=
  NatIso.ofComponents (fun M ↦ (ordinaryH l E T).mapIso
    ((eqToIso (coefficientSequenceRestriction_evaluation l E T n)).app M))
      (fun f ↦ (isoWhiskerRight
        (eqToIso (coefficientSequenceRestriction_evaluation l E T n))
        (ordinaryH l E T)).hom.naturality f)


/-- The same uniquely normalized comparison on cochain complexes.
Source: Stacks 06YY (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def ordinaryRhoComplex (T : Scheme.{u}) :=
  letI := ordinaryHReduction_zero l E T
  NatIso.mapHomologicalComplex (ordinaryRho l E T) (.up ℤ)

/-- Representative normalization of rho: one strict chain isomorphism, with every
component induced by the ordinary scalar-unit comparison. The final equation is in
D(strict towers), not a test of equality after derived evaluation.
Source: node proof Step 5, Stacks 06YY
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def RhoNormalized (T : Scheme.{u})
    (ρ : (IntegralSystemRealization.calculus l E T).reduction ⋙ U l E T ≅
      H l E T ⋙ constantReduction l E T) : Prop :=
  ∀ (P : CochainComplex (scalarReductionSource l E T) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology T) (R := completedIntegralCommRingSheafUnrestricted l E T) P),
    (∀ k : ℤ, SheafOfModules.IsFlatOnSite
      (J := ProEt.topology T) (R := completedIntegralCommRingSheafUnrestricted l E T)
      (P.X k)) →
    ∃ (C : CochainComplex (coefficientSequenceModules l E T) ℤ)
      (e : (IntegralSystemRealization.calculus l E T).reduction.obj
        (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
      (κ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E T n).mapHomologicalComplex (.up ℤ)).obj C ≅
          ((scalarReductionExtension l E T n).mapHomologicalComplex (.up ℤ)).obj P)
      (a : ((ordinaryU l E T).mapHomologicalComplex (.up ℤ)).obj C ≅
        (((ordinaryCompletedReduction l E T ⋙ towerH l E T).mapHomologicalComplex
          (.up ℤ)).obj P)),
      CoefficientReductionPresentation l E T
        (IntegralSystemRealization.calculus l E T).toCoefficientDerivedSystemReduction
        P hP C e κ ∧
      (∀ (k : ℤ) (n : ℕ),
        (a.hom.f k).app (op n) =
          (ordinaryUEvaluation l E T n).hom.app (C.X k) ≫
            (ordinaryH l E T).map
              ((scalarReductionRestriction l E T n).map ((κ n).hom.f k))) ∧
      ρ.hom.app (DerivedCategory.Q.obj P) ≫
          (constantReduction l E T).map ((ordinaryH l E T).mapDerivedCategoryFactors.hom.app P) ≫
          (ConstantCompletion.quotientPresentation (proEtaleModelTopology T)
            (ULift.{u + 1} (constantRing l E))
            (sfCbcModelIdeal (constantDatum l E)) false).comparison.app
              (((ordinaryH l E T).mapHomologicalComplex (.up ℤ)).obj P) =
        (U l E T).map e.hom ≫ (ordinaryU l E T).mapDerivedCategoryFactors.hom.app C ≫
          DerivedCategory.Q.map a.hom ≫ DerivedCategory.Q.map
            ((ordinaryRhoComplex l E T).hom.app P)

/-- The canonical derived scalar reduction comparison, with its strict representative
characterization retained. Source: node proof Step 5, Stacks 06YY, 07A4
(blueprint: lem-sf-constant-semilinear-generator-comparison).
Proof: restrict a flat-term K-flat completed representative to constant scalars.
Flatness of the completed ring makes it K-flat over the constant ring. Both quotient
constructions are the same strict complex modulo the uniformizer powers. The ordinary
unit-normalized comparison descends by localization, giving the displayed chain-map
identity. Every object admits such a representative; localization gives uniqueness. -/
theorem rho_existsUnique (T : Scheme.{u}) :
    ∃! ρ : (IntegralSystemRealization.calculus l E T).reduction ⋙ U l E T ≅
        H l E T ⋙ constantReduction l E T,
      RhoNormalized l E T ρ := by
  sorry

/-- The canonical rho, selected by its strict representative identity, not by bare existence.
Source: node proof Step 5 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def rho (T : Scheme.{u}) := (rho_existsUnique l E T).exists.choose

/-- The right adjoint's underlying geometric direct image, fixed by the original
module Hom bijection. Source: Stacks 03D7
(blueprint: lem-sf-constant-semilinear-generator-comparison).
Proof: forget a module adjunct. Its underlying arrow is the geometric adjunct of
the algebraic inverse-image insertion followed by the given arrow. The resulting
Hom representation determines this natural isomorphism uniquely by Yoneda. -/
theorem constantDirectUnderlying_existsUnique {V T : Scheme.{u}} (f : V ⟶ T) :
    ∃! e : (sfCbcMorphism f).modulePush
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⋙
        ConstantCompletion.underlying (sfCbcModelRing T (constantRing l E)) ≅
      ConstantCompletion.underlying (sfCbcModelRing V (constantRing l E)) ⋙ sfCbcModelDirect f,
      ∀ (M : ConstantCompletion.Mod (sfCbcModelRing T (constantRing l E)))
        (N : ConstantCompletion.Mod (sfCbcModelRing V (constantRing l E)))
        (a : ((sfCbcMorphism f).modulePull
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj M ⟶ N),
        (ConstantCompletion.underlying (sfCbcModelRing T (constantRing l E))).map
            (((sfCbcMorphism f).moduleAdjunction
              (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))).homEquiv M N a) ≫
          e.hom.app N =
        (sfCbcModelAdjunction f).homEquiv _ _
          (ConstantCompletion.pullInsertion (sfCbcMorphism f).algebra
              (ConstantCompletion.constantMap (sfCbcMorphism f).algebra
                (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) M ≫
            (ConstantCompletion.underlying (sfCbcModelRing V (constantRing l E))).map a) := by
  sorry

/-- The unique underlying direct-image comparison used to state identity on sections.
Source: Stacks 03D7 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def constantDirectUnderlying {V T : Scheme.{u}} (f : V ⟶ T) :=
  (constantDirectUnderlying_existsUnique l E f).exists.choose

/-- The underived system/direct-image scalar comparison, fixed on every section.
Source: Stacks 03D7, 0941
(blueprint: lem-sf-constant-semilinear-generator-comparison).
Proof: the sequence-site direct image is precomposition. Restriction leaves the
sections unchanged. Apply the canonical underlying direct-image comparison at each
index; identity on those sections determines a unique linear natural isomorphism,
and the same identities commute with every integer-direction transition. -/
theorem ordinarySystemDirectIso_existsUnique {V T : Scheme.{u}} (f : V ⟶ T) :
    ∃! b : pullbackTensorSequenceDirect l E f ⋙ ordinaryU l E T ≅
      ordinaryU l E V ⋙ (sfCbcMorphism f).towerModulePush
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)),
      ∀ (M : coefficientSequenceModules l E V) (n : ℕ)
        (W : (proEtaleSiteModel T)ᵒᵖ)
        (x : (((ordinaryU l E T).obj
          ((pullbackTensorSequenceDirect l E f).obj M)).obj (op n)).val.obj W),
        HEq (((constantDirectUnderlying l E f).hom.app
            (((ordinaryU l E V).obj M).obj (op n))).hom.app W
          (((b.hom.app M).app (op n)).val.app W x)) x := by
  sorry

/-- The fixed ordinary system comparison; its data is determined by unchanged sections.
Source: Stacks 0941 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def ordinarySystemDirectIso {V T : Scheme.{u}} (f : V ⟶ T) :=
  (ordinarySystemDirectIso_existsUnique l E f).exists.choose

/-- The underived completed-ring/direct-image scalar comparison, fixed on sections.
Source: Stacks 03D7 (blueprint: lem-sf-constant-semilinear-generator-comparison).
Proof: the projection-normalized constant-to-completed map commutes with geometric
inverse image. The ordinary coefficient/direct-image comparison is identity on
sections. Transport through the small-model equivalence and the Hom-normalized
constantDirectUnderlying; sections determine it uniquely. -/
theorem ordinaryIntegralDirectIso_existsUnique {V T : Scheme.{u}} (f : V ⟶ T) :
    ∃! b : proEtaleRingModuleDirectImage f
        ((PurCompactSupport.completed l E).ring T)
        ((PurCompactSupport.completed l E).ring V)
        ((PurCompactSupport.completed l E).pull f) ⋙ ordinaryH l E T ≅
      ordinaryH l E V ⋙ (sfCbcMorphism f).modulePush
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)),
      ∀ (M : scalarReductionSource l E V) (W : (proEtaleSiteModel T)ᵒᵖ)
        (x : ((ordinaryH l E T).obj
          ((proEtaleRingModuleDirectImage f
            ((PurCompactSupport.completed l E).ring T)
            ((PurCompactSupport.completed l E).ring V)
            ((PurCompactSupport.completed l E).pull f)).obj M)).val.obj W),
        HEq (((constantDirectUnderlying l E f).hom.app
            ((ordinaryH l E V).obj M)).hom.app W
          ((b.hom.app M).val.app W x)) x := by
  sorry

/-- The unique ordinary completed-ring scalar comparison.
Source: Stacks 03D7 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def ordinaryIntegralDirectIso {V T : Scheme.{u}} (f : V ⟶ T) :=
  (ordinaryIntegralDirectIso_existsUnique l E f).exists.choose

/-- The canonical right-derived unit on complexes, with the localization transports.
Source: Stacks 0D6E (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def directCochainUnit {B : Type vB} {C : Type vC} [Category.{wB} B] [Category.{wC} C]
    [Abelian B] [Abelian C] [HasDerivedCategory.{dB} B]
    [HasDerivedCategory.{dC} C] [Abelian.HasKInjectiveResolutions B]
    (G : B ⥤ C) [G.Additive] (P : CochainComplex B ℤ) :
    DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj P) ⟶
      G.rightDerivedFunctor.obj (DerivedCategory.Q.obj P) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj P) ≫
    G.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app P)



/-- Universal-unit normalization of a derived coefficient/direct-image square.
Source: Stacks 0D6E (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def DirectSquareNormalization
    {A : Type a₁} {B : Type a₂} {C : Type a₃} {D : Type a₄}
    [Category.{h₁} A] [Category.{h₂} B]
    [Category.{h₃} C] [Category.{h₄} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{d₁} A] [HasDerivedCategory.{d₂} B]
    [HasDerivedCategory.{d₃} C] [HasDerivedCategory.{d₄} D]
    (F : A ⥤ B) [F.Additive] (G : C ⥤ D) [G.Additive]
    (P : A ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (Q : B ⥤ D) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (RG : DerivedCategory C ⥤ DerivedCategory D)
    (etaF : ∀ K : CochainComplex A ℤ,
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
        RF.obj (DerivedCategory.Q.obj K))
    (etaG : ∀ K : CochainComplex C ℤ,
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj K) ⟶
        RG.obj (DerivedCategory.Q.obj K))
    (b : F ⋙ Q ≅ P ⋙ G)
    (d : RF ⋙ Q.mapDerivedCategory ≅ P.mapDerivedCategory ⋙ RG) : Prop :=
  ∀ K : CochainComplex A ℤ,
    Q.mapDerivedCategory.map (etaF K) ≫ d.hom.app (DerivedCategory.Q.obj K) ≫
        RG.map (P.mapDerivedCategoryFactors.hom.app K) =
      Q.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app K) ≫
        etaG ((P.mapHomologicalComplex (.up ℤ)).obj K)

/-- The derived scalar comparison is normalized by the universal derived units.
Source: Stacks 0D6E (blueprint: lem-sf-constant-semilinear-generator-comparison).
Proof: identify both factorizations of the common ringed sequence-topos map.
The ordinary square is identity on sections. Derived composition gives the
invertible comparison with the stated unit equation; the universal property
of total right derivation determines it uniquely, without assuming restriction
preserves K-injective complexes. -/
theorem systemDirectScalarIso_existsUnique (o : Operations l E)
    {V T : Scheme.{u}} (f : V ⟶ T) :
    ∃! d : IntegralSystemRealization.Operations.push l E o.system f ⋙
        U l E T ≅ U l E V ⋙
          (sfCbcMorphism f).towerPush
            (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)),
      DirectSquareNormalization
        (A := coefficientSequenceModules l E V)
        (B := coefficientSequenceModules l E T)
        (C := constantTowerCategory l E V) (D := constantTowerCategory l E T)
        (pullbackTensorSequenceDirect l E f)
        ((sfCbcMorphism f).towerModulePush
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))
        (ordinaryU l E V) (ordinaryU l E T)
        (IntegralSystemRealization.Operations.push l E o.system f)
        ((sfCbcMorphism f).towerPush
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))
        (o.system.direct f).model.directUnit.app
        (directCochainUnit ((sfCbcMorphism f).towerModulePush
            (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))
        (ordinarySystemDirectIso l E f) d := by
  sorry

/-- The universal-unit-normalized proper system comparison.
Source: Stacks 0D6E (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def systemDirectScalarIso (o : Operations l E) {V T : Scheme.{u}} (f : V ⟶ T) :=
  (systemDirectScalarIso_existsUnique l E o f).exists.choose

/-- Exact inverse image and scalar restriction, as the mate of the identity on
ordinary direct-image sections. This fixes the comparison before deriving it.
Source: Stacks 07A4 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def ordinarySystemPullMap {V T : Scheme.{u}} (f : V ⟶ T) :
    ordinaryU l E T ⋙ (sfCbcMorphism f).towerModulePull
        (ULift.{u + 1} (constantRing l E)) ⟶
      pullbackTensorSequenceInverse l E f ⋙ ordinaryU l E V :=
  ((mateEquiv (pullbackTensorSequenceAdjunction l E f)
    (Adjunction.whiskerRight ℕᵒᵖ ((sfCbcMorphism f).moduleAdjunction
      (ULift.{u + 1} (constantRing l E))))).symm
    (TwoSquare.mk _ _ _ _ (ordinarySystemDirectIso l E f).hom)).natTrans

/-- The ordinary inverse-image scalar mate is invertible.
Source: Stacks 07A4 (blueprint: lem-sf-constant-semilinear-generator-comparison).
Proof: on the sequence site inverse image has the same underlying sheaf after
restriction; its scalar tensor insertion is 1 tensor m. The mate formula sends
this insertion to itself. Tensor generation gives the inverse and its two laws. -/
theorem ordinarySystemPullMap_isIso {V T : Scheme.{u}} (f : V ⟶ T) :
    IsIso (ordinarySystemPullMap l E f) := by
  sorry

/-- The canonical exact derived inverse-image scalar identification.
Source: Stacks 07A4 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def systemPullScalarIso {V T : Scheme.{u}} (f : V ⟶ T) :
    U l E T ⋙ (sfCbcMorphism f).towerPull
        (ULift.{u + 1} (constantRing l E)) ≅
      IntegralSystemRealization.pull l E f ⋙ U l E V :=
  letI := ordinarySystemPullMap_isIso l E f
  letI := ordinaryU_additive l E V
  letI := ordinaryU_additive l E T
  letI := ordinaryU_limits l E V
  letI := ordinaryU_limits l E T
  letI := ordinaryU_colimits l E V
  letI := ordinaryU_colimits l E T
  letI := (sfCbcMorphism f).towerModulePull_finiteLimits
    (ULift.{u + 1} (constantRing l E))
  letI := (sfCbcMorphism f).towerModulePull_finiteColimits
    (ULift.{u + 1} (constantRing l E))
  Functor.mapDerivedCategorySquareIso (asIso (ordinarySystemPullMap l E f))

/-- Proper system unit and counit intertwining on all ordinary derived systems.
Source: Stacks 07A6, 0FPI (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def ProperAdjunctionEquations (o : Operations l E) {V T : Scheme.{u}} (f : V ⟶ T) : Prop :=
  (∀ X : coefficientSequenceDerived l E T,
    (U l E T).map ((o.system.direct f).adj.unit.app X) ≫
        (systemDirectScalarIso l E o f).hom.app
          ((IntegralSystemRealization.pull l E f).obj X) =
      ((sfCbcMorphism f).towerAdjunction
        (ULift.{u + 1} (constantRing l E))).unit.app ((U l E T).obj X) ≫
        ((sfCbcMorphism f).towerPush (ULift.{u + 1} (constantRing l E))).map
          ((systemPullScalarIso l E f).hom.app X)) ∧
  (∀ Y : coefficientSequenceDerived l E V,
    ((sfCbcMorphism f).towerPull (ULift.{u + 1} (constantRing l E))).map
        ((systemDirectScalarIso l E o f).hom.app Y) ≫
      ((sfCbcMorphism f).towerAdjunction
        (ULift.{u + 1} (constantRing l E))).counit.app ((U l E V).obj Y) =
    (systemPullScalarIso l E f).hom.app
        ((IntegralSystemRealization.Operations.push l E o.system f).obj Y) ≫
      (U l E V).map ((o.system.direct f).adj.counit.app Y))

/-- Universal-unit normalization of the completed-ring proper scalar comparison.
Source: Stacks 0D6E (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def IntegralDirectNormalized {V T : Scheme.{u}} (f : V ⟶ T)
    (d : IntegralSystemRealization.ringedPush l E f ⋙ H l E T ≅
      H l E V ⋙ (sfCbcMorphism f).push (ULift.{u + 1} (constantRing l E))) : Prop :=
  letI := ordinaryH_additive l E V
  letI := ordinaryH_additive l E T
  letI := ordinaryH_limits l E V
  letI := ordinaryH_limits l E T
  letI := ordinaryH_colimits l E V
  letI := ordinaryH_colimits l E T
  DirectSquareNormalization
        (proEtaleRingModuleDirectImage f
          ((PurCompactSupport.completed l E).ring T)
          ((PurCompactSupport.completed l E).ring V)
          ((PurCompactSupport.completed l E).pull f))
        ((sfCbcMorphism f).modulePush (ULift.{u + 1} (constantRing l E)))
        (ordinaryH l E V) (ordinaryH l E T)
        (IntegralSystemRealization.ringedPush l E f)
        ((sfCbcMorphism f).push (ULift.{u + 1} (constantRing l E)))
        (directCochainUnit (proEtaleRingModuleDirectImage f
          ((PurCompactSupport.completed l E).ring T)
          ((PurCompactSupport.completed l E).ring V)
          ((PurCompactSupport.completed l E).pull f)))
        (directCochainUnit ((sfCbcMorphism f).modulePush
          (ULift.{u + 1} (constantRing l E))))
        (ordinaryIntegralDirectIso l E f) d

/-- The integral proper scalar comparison has the universal derived-unit normalization.
Source: Stacks 0D6E (blueprint: lem-sf-constant-semilinear-generator-comparison).
Proof: compare the two factorizations of the common ringed-topos direct image.
The ordinary identity on sections is ordinaryIntegralDirectIso. The universal
right-derived units determine its derived comparison uniquely, and derived
composition proves it invertible even for unbounded complexes. -/
theorem integralDirectScalarIso_existsUnique {V T : Scheme.{u}} (f : V ⟶ T) :
    ∃! d : IntegralSystemRealization.ringedPush l E f ⋙ H l E T ≅
      H l E V ⋙ (sfCbcMorphism f).push (ULift.{u + 1} (constantRing l E)),
      IntegralDirectNormalized l E f d := by
  sorry

/-- The canonical integral proper comparison, fixed independently of r and q.
Source: Stacks 0D6E (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def integralDirectScalarIso {V T : Scheme.{u}} (f : V ⟶ T) :=
  (integralDirectScalarIso_existsUnique l E f).exists.choose

/-- The completion unit of an admissible input is invertible.
Source: generator coherence domain; normalized DVR effectivity
(blueprint: lem-sf-constant-semilinear-generator-comparison).
Proof: finiteTorConstructibleIntegral includes derived completeness. The actual
quotient-tower reconstruction theorem identifies its unit with the completion
unit and proves it invertible, without a new effectivity assumption. -/
theorem admissibleUnit_isIso {V : Scheme.{u}}
    (M : DerivedCategory (scalarReductionSource l E V)) (lo hi torLo torHi : ℤ)
    (_h : Admissible l E (IntegralSystemRealization.calculus l E V) M lo hi torLo torHi) :
    IsIso ((IntegralSystemRealization.calculus l E V).adjunction.unit.app M) := by
  sorry

/-- The specified proper integral object, in the tower coordinates of pushR.
Source: blueprint coherence Step 2
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
abbrev properIntegral (o : Operations l E) {V T : Scheme.{u}} (p : V ⟶ T) :=
  integralPush l E o p

/-- The canonical proper scalar identification: first identify the defining total
limit with completed-ring direct image, then restrict scalars. The last factor
is independently normalized by the ordinary direct-image sections.
Source: node proof Steps 8--9
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def properSigmaHom (o : Operations l E) {V T : Scheme.{u}} (p : V ⟶ T)
    (M : DerivedCategory (scalarReductionSource l E V)) :=
  (H l E T).map ((o.realization.push l E p).hom.app
    ((IntegralSystemRealization.calculus l E V).reduction.obj M)) ≫
  (H l E T).map ((IntegralSystemRealization.ringedPush l E p).map
    (inverseOrZero ((IntegralSystemRealization.calculus l E V).adjunction.unit.app M))) ≫
  (integralDirectScalarIso l E p).hom.app M

/-- The ordinary constant-coefficient open adjunction exists on the published small
model. No adjunction is selected from this existence statement: the comparisons below
are defined for every adjunction presentation, and the final theorem includes existence.
Source: Stacks 03DI, 03DJ; node proof Step 11
(blueprint: lem-sf-constant-semilinear-generator-comparison).
Proof: sfCbcConstantModuleToSlice is the ringed weakly-etale localization equivalence.
Compose its adjunction with localizedModuleAdjunctionIndependent, then transport by
sfCbcModelModules. The restriction is canonically modulePull by the inverse-image
universal property. Transport the right side by that canonical isomorphism. -/
theorem constantOpenAdjunction_nonempty {V T : Scheme.{u}} (j : V ⟶ T)
    [IsOpenImmersion j] :
    Nonempty (sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E))) := by
  sorry

/-- The exact tower open adjunction, obtained from the same ordinary unit and counit.
Source: Stacks 03DI, 0941
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def constantTowerOpenAdj {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E))) :
    sfCbcDerivedTowerExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).towerPull (ULift.{u + 1} (constantRing l E)) :=
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      ((sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E)))) :=
    (sfCbcMorphism j).towerModulePull_finiteLimits _
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      ((sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E)))) :=
    (sfCbcMorphism j).towerModulePull_finiteColimits _
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    (Adjunction.whiskerRight ℕᵒᵖ a)

/-- The open scalar map is the inverse-direction adjunction mate of the already fixed
inverse-image scalar comparison. It is defined before any normalized-system restriction.
Source: node proof Step 11; Stacks 03DI
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def systemOpenScalarMap (o : Operations l E) {V T : Scheme.{u}} (j : V ⟶ T)
    [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E))) :
    U l E V ⋙ sfCbcDerivedTowerExtension j (constantRing l E) ⟶
      IntegralSystemRealization.Operations.shriek l E o.system j ⋙ U l E T :=
  ((mateEquiv (o.system.extension j).adj (constantTowerOpenAdj l E j a)).symm
    (TwoSquare.mk _ _ _ _ (systemPullScalarIso l E j).inv)).natTrans

/-- Restricting the scalar action leaves the ordinary open generators unchanged.
Source: Stacks 03DI, 03DJ; node proof Step 11
(blueprint: lem-sf-constant-semilinear-generator-comparison).
Proof: compute the mate on the localized site. It carries each extension generator
to the identical section, with the restricted action. This is invertible on the open
and both extensions vanish on its complement. The formula respects all integer
transitions before deriving, hence gives an isomorphism of strict derived towers. -/
theorem systemOpenScalarMap_isIso (o : Operations l E) {V T : Scheme.{u}} (j : V ⟶ T)
    [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E))) :
    IsIso (systemOpenScalarMap l E o j a) := by
  sorry

/-- The open operation identification, fixed by the inverse-image mate and its unique
inverse, rather than by the reduction square that the main theorem asserts.
Source: node proof Step 11
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def systemOpenScalarIso (o : Operations l E) {V T : Scheme.{u}} (j : V ⟶ T)
    [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E))) :
    IntegralSystemRealization.Operations.shriek l E o.system j ⋙ U l E T ≅
      U l E V ⋙ sfCbcDerivedTowerExtension j (constantRing l E) :=
  (@asIso _ _ _ _ (systemOpenScalarMap l E o j a)
    (systemOpenScalarMap_isIso l E o j a)).symm

/-- Ordinary completed-ring inverse image commutes with scalar restriction by the mate
of the independently fixed identity on direct-image sections.
Source: Stacks 07A4; node proof Steps 2--3
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def ordinaryIntegralPullMap {V T : Scheme.{u}} (f : V ⟶ T) :
    ordinaryH l E T ⋙ (sfCbcMorphism f).modulePull
        (ULift.{u + 1} (constantRing l E)) ⟶
      proEtaleRingModulePullback f ((PurCompactSupport.completed l E).ring T)
        ((PurCompactSupport.completed l E).ring V) ((PurCompactSupport.completed l E).pull f) ⋙
          ordinaryH l E V :=
  ((mateEquiv
    (proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring T)
      ((PurCompactSupport.completed l E).ring V) ((PurCompactSupport.completed l E).pull f))
    ((sfCbcMorphism f).moduleAdjunction (ULift.{u + 1} (constantRing l E)))).symm
    (TwoSquare.mk _ _ _ _ (ordinaryIntegralDirectIso l E f).hom)).natTrans

/-- The scalar pullback mate for an open immersion is invertible.
Source: Stacks 07A4; node proof Step 3
(blueprint: lem-sf-constant-semilinear-generator-comparison).
Proof: restriction to an open commutes with the coefficient inverse limit. Thus
the pulled completed ring is the completed ring on the open, and the coefficient
square identifies the scalar actions. The mate sends 1 tensor m to itself;
tensor-unit reassociation gives its inverse. -/
theorem ordinaryIntegralPullMap_isIso {V T : Scheme.{u}} (f : V ⟶ T)
    [IsOpenImmersion f] :
    IsIso (ordinaryIntegralPullMap l E f) := by
  sorry

/-- Exact derivation of the normalized ordinary scalar pullback comparison.
Source: Stacks 07A4 (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def integralPullScalarIso {V T : Scheme.{u}} (f : V ⟶ T) [IsOpenImmersion f] :
    H l E T ⋙ (sfCbcMorphism f).pull (ULift.{u + 1} (constantRing l E)) ≅
      IntegralSystemRealization.ringedPull l E f ⋙ H l E V :=
  letI : (ordinaryH l E V).Additive := ordinaryH_additive l E V
  letI : (ordinaryH l E T).Additive := ordinaryH_additive l E T
  letI := ordinaryH_limits l E V
  letI := ordinaryH_limits l E T
  letI := ordinaryH_colimits l E V
  letI := ordinaryH_colimits l E T
  letI := ordinaryIntegralPullMap_isIso l E f
  letI := (sfCbcMorphism f).modulePull_finiteLimits (ULift.{u + 1} (constantRing l E))
  letI := (sfCbcMorphism f).modulePull_finiteColimits (ULift.{u + 1} (constantRing l E))
  Functor.mapDerivedCategorySquareIso (asIso (ordinaryIntegralPullMap l E f))

/-- The constant ordinary open adjunction descended to complexes and localization.
Source: Stacks 03DI (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def constantDerivedOpenAdj {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E))) :
    sfCbcModelDerivedExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).pull (ULift.{u + 1} (constantRing l E)) :=
  letI := (sfCbcMorphism j).modulePull_finiteLimits (ULift.{u + 1} (constantRing l E))
  letI := (sfCbcMorphism j).modulePull_finiteColimits (ULift.{u + 1} (constantRing l E))
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction a

/-- The integral open scalar mate, on all ordinary derived complexes.
Source: Stacks 03DI; node proof Step 11
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def integralOpenScalarMap {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E))) :
    H l E V ⋙ sfCbcModelDerivedExtension j (constantRing l E) ⟶
      IntegralSystemRealization.ringedOpen l E j ⋙ H l E T :=
  ((mateEquiv (IntegralSystemRealization.ringedOpenAdj l E j)
    (constantDerivedOpenAdj l E j a)).symm
      (TwoSquare.mk _ _ _ _ (integralPullScalarIso l E j).inv)).natTrans

/-- The integral open scalar mate is invertible on the ambient derived category.
Source: Stacks 03DI; node proof Step 11
(blueprint: lem-sf-constant-semilinear-generator-comparison).
Proof: on the localized site restriction of scalars changes neither the extension
summands nor their maps. The inverse identity on the summands sheafifies and
passes termwise to complexes and their derived localization. -/
theorem integralOpenScalarMap_isIso {V T : Scheme.{u}} (j : V ⟶ T)
    [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E))) :
    IsIso (integralOpenScalarMap l E j a) := by
  sorry

/-- The integral open scalar isomorphism, fixed by its ordinary inverse-image mate.
Source: Stacks 03DI (blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def integralOpenScalarIso {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E))) :
    IntegralSystemRealization.ringedOpen l E j ⋙ H l E T ≅
      H l E V ⋙ sfCbcModelDerivedExtension j (constantRing l E) :=
  (@asIso _ _ _ _ (integralOpenScalarMap l E j a)
    (integralOpenScalarMap_isIso l E j a)).symm

/-- The open sigma is the ordinary scalar comparison followed by exactly the
quotient-tower completion unit, with no inverse chosen for an unrelated arrow.
Source: node proof Step 11
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def openSigmaHom {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E)))
    (M : DerivedCategory (scalarReductionSource l E V)) :=
  (integralOpenScalarIso l E j a).hom.app M ≫
    ((sfCbcSite T).unit _ (sfCbcModelIdeal (constantDatum l E))).app
      ((sfCbcModelDerivedExtension j (constantRing l E)).obj ((H l E V).obj M))

/-- The two open adjunction equations hold on every ordinary strict derived system.
Source: Stacks 03DI; node proof Step 11
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def OpenAdjunctionEquations (o : Operations l E) {V T : Scheme.{u}} (j : V ⟶ T)
    [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E))) : Prop :=
  (∀ X : coefficientSequenceDerived l E V,
    (U l E V).map ((o.system.extension j).adj.unit.app X) ≫
      (systemPullScalarIso l E j).inv.app
        ((IntegralSystemRealization.Operations.shriek l E o.system j).obj X) ≫
      ((sfCbcMorphism j).towerPull (ULift.{u + 1} (constantRing l E))).map
        ((systemOpenScalarIso l E o j a).hom.app X) =
      (constantTowerOpenAdj l E j a).unit.app ((U l E V).obj X)) ∧
  (∀ Y : coefficientSequenceDerived l E T,
    (systemOpenScalarIso l E o j a).hom.app ((IntegralSystemRealization.pull l E j).obj Y) ≫
      (sfCbcDerivedTowerExtension j (constantRing l E)).map
        ((systemPullScalarIso l E j).inv.app Y) ≫
      (constantTowerOpenAdj l E j a).counit.app ((U l E T).obj Y) =
      (U l E T).map ((o.system.extension j).adj.counit.app Y))

/-- The input and output systems in the single proper generator's common windows.
Source: generator coherence Step 1
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def ProperDomain (o : Operations l E) {V T : Scheme.{u}} (p : V ⟶ T)
    (lo hi torLo torHi : ℤ) (M : DerivedCategory (scalarReductionSource l E V)) : Prop :=
  Admissible l E (IntegralSystemRealization.calculus l E V) M lo hi torLo torHi ∧
    SystemAdmissible l E T
      ((IntegralSystemRealization.Operations.push l E o.system p).obj
        ((IntegralSystemRealization.calculus l E V).reduction.obj M)) lo hi torLo torHi

/-- The common-window domain for the one open extension generator.
Source: generator coherence Step 1
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def OpenDomain (o : Operations l E) {V T : Scheme.{u}} (j : V ⟶ T)
    [IsOpenImmersion j] (lo hi torLo torHi : ℤ)
    (M : DerivedCategory (scalarReductionSource l E V)) : Prop :=
  Admissible l E (IntegralSystemRealization.calculus l E V) M lo hi torLo torHi ∧
    SystemAdmissible l E T
      ((IntegralSystemRealization.Operations.shriek l E o.system j).obj
        ((IntegralSystemRealization.calculus l E V).reduction.obj M)) lo hi torLo torHi

/-- The left route of the proper scalar-restriction square uses the basic pushR,
the universal-unit-normalized operation comparison, and the strict quotient rho.
Source: node statement, displayed equality
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def properComparisonHom (o : Operations l E) {V T : Scheme.{u}} (p : V ⟶ T)
    (M : DerivedCategory (scalarReductionSource l E V)) :=
  (U l E T).map (pushR l E o p M) ≫
    (systemDirectScalarIso l E o p).hom.app
      ((IntegralSystemRealization.calculus l E V).reduction.obj M) ≫
    ((sfCbcMorphism p).towerPush (ULift.{u + 1} (constantRing l E))).map
      ((rho l E V).hom.app M)

/-- The right route uses precisely SfCbcLetter.q for the single proper letter.
Source: node statement, displayed equality
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def ProperSquare (o : Operations l E) {V T : Scheme.{u}} (p : V ⟶ T)
    (M : DerivedCategory (scalarReductionSource l E V)) : Prop :=
  properComparisonHom l E o p M =
    (rho l E T).hom.app ((properIntegral l E o p).obj M) ≫
      (constantReduction l E T).map (properSigmaHom l E o p M) ≫
      ((SfCbcLetter.directImage p).q (constantDatum l E)
        (constantReducedUnits l E)).app ((H l E V).obj M)

/-- The left route for the single open generator uses exactly openR.
Source: node statement, displayed equality
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def openComparisonHom (o : Operations l E) {V T : Scheme.{u}} (j : V ⟶ T)
    [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E)))
    (M : DerivedCategory (scalarReductionSource l E V)) :=
  (U l E T).map (openR l E o j M) ≫
    (systemOpenScalarIso l E o j a).hom.app
      ((IntegralSystemRealization.calculus l E V).reduction.obj M) ≫
    (sfCbcDerivedTowerExtension j (constantRing l E)).map ((rho l E V).hom.app M)

/-- The right open route uses the actual completion-unit sigma and the one-letter q.
Source: node statement, displayed equality
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def OpenSquare (o : Operations l E) {V T : Scheme.{u}} (j : V ⟶ T)
    [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E)))
    (M : DerivedCategory (scalarReductionSource l E V)) : Prop :=
  openComparisonHom l E o j a M =
    (rho l E T).hom.app ((IntegralSystemRealization.ringedOpen l E j).obj M) ≫
      (constantReduction l E T).map (openSigmaHom l E j a M) ≫
      ((SfCbcLetter.openExtension j inferInstance).q (constantDatum l E)
        (constantReducedUnits l E)).app ((H l E V).obj M)

/-- Naturality of the proper scalar identification and of the common square, in the
ordinary derived strict-tower category on the stated domain.
Source: node proof Step 13
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def ProperNaturality (o : Operations l E) {V T : Scheme.{u}} (p : V ⟶ T)
    (lo hi torLo torHi : ℤ) : Prop :=
  ∀ (M N : DerivedCategory (scalarReductionSource l E V)),
    ProperDomain l E o p lo hi torLo torHi M →
    ProperDomain l E o p lo hi torLo torHi N → ∀ m : M ⟶ N,
    (H l E T).map ((properIntegral l E o p).map m) ≫ properSigmaHom l E o p N =
      properSigmaHom l E o p M ≫
        ((sfCbcMorphism p).push (ULift.{u + 1} (constantRing l E))).map
          ((H l E V).map m) ∧
    (U l E T).map ((IntegralSystemRealization.calculus l E T).reduction.map
        ((properIntegral l E o p).map m)) ≫ properComparisonHom l E o p N =
      properComparisonHom l E o p M ≫
        ((sfCbcMorphism p).towerPush (ULift.{u + 1} (constantRing l E))).map
          ((constantReduction l E V).map ((H l E V).map m))

/-- Naturality of the completion-normalized open sigma and of the common strict square.
Source: node proof Steps 11--13
(blueprint: lem-sf-constant-semilinear-generator-comparison). -/
def OpenNaturality (o : Operations l E) {V T : Scheme.{u}} (j : V ⟶ T)
    [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E)))
    (lo hi torLo torHi : ℤ) : Prop :=
  ∀ (M N : DerivedCategory (scalarReductionSource l E V)),
    OpenDomain l E o j lo hi torLo torHi M →
    OpenDomain l E o j lo hi torLo torHi N → ∀ m : M ⟶ N,
    (H l E T).map ((IntegralSystemRealization.ringedOpen l E j).map m) ≫
        openSigmaHom l E j a N =
      openSigmaHom l E j a M ≫
        ((SfCbcLetter.openExtension j inferInstance).complete (constantDatum l E)).map
          ((H l E V).map m) ∧
    (U l E T).map ((IntegralSystemRealization.calculus l E T).reduction.map
        ((IntegralSystemRealization.ringedOpen l E j).map m)) ≫
        openComparisonHom l E o j a N =
      openComparisonHom l E o j a M ≫
        (sfCbcDerivedTowerExtension j (constantRing l E)).map
          ((constantReduction l E V).map ((H l E V).map m))

/-- Scalar restriction identifies exactly the basic proper and quasi-compact-open
reduction generators, with their adjunctions and strict naturality.
Source: Stacks 0E48, remark-compatible-with-diagram; blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-constant-semilinear-generator-comparison).

Proof, Step 1: identify strict varying-ring systems with modules on the sequence site,
and constant towers with modules over its constant valuation-ring sheaf. Restriction
along their coefficient map is ordinaryU, and exact localization is U. The geometric
inverse image and direct image are the ordinary adjoint functors on all systems.
Step 2: apply ringed-topos derived pushforward composition to the two factorizations
of the scalar/geometric square; universal derived units fix systemDirectScalarIso.
Step 3: compute the inverse-image scalar mate on flat-term K-flat resolutions:
the scalar counit sends b tensor q to bq, hence its mate is systemPullScalarIso.
Step 4: the coefficient-restriction counit identity gives ProperAdjunctionEquations;
transpose once more and use the triangle identity for the unit equation.
Step 5: flatness of the completed ring over constant scalars and the quotient-ring
identifications identify both reduction complexes with the one strict quotient diagram.
The ordinary scalar units fix ordinaryRho; RhoNormalized descends that chain isomorphism.
Step 6: the constant-tower/direct-image comparison is represented by the same constant
K-injective tower. Its counit is the ordinary counit on that representative, including
all transitions; it is not deduced from faithfulness of finite evaluation.
Step 7: transpose the counit-tensor-identity composite on the diagram site. After scalar
restriction and the operation comparison this is exactly the proper SfCbcLetter.q.
Step 8: apply the actual total limit to this whole-tower identity. The quotient unit and
constant-tower/direct-image normalization identify its adjunct with push of that unit.
Step 9: the canonical completed-coefficient pushforward comparison identifies the defining
integral total limit with completed-ring direct image. Restrict it, then invert the input
reconstruction unit: this is properSigmaHom, whose factors are invertible on the domain.
Step 10: the reduction/limit adjunct of the lifted proper arrow is the identity of the
integral total limit. Faithfulness of H on complete objects and the actual adjunction
therefore identify it with pushR. This proves ProperSquare.
Step 11: form the constant open adjunction by the localized module summand adjunction,
transported through the small-model equivalences. Scalar restriction leaves the summand
insertion and evaluation unchanged. Their mates give the two open operation comparisons
and OpenAdjunctionEquations. The integral open output is complete; its scalar comparison
followed by the quotient completion unit is exactly openSigmaHom and is invertible.
Step 12: on one flat-term representative both open comparisons send each extension
generator x tensor r to itself, before localization and along every quotient transition.
The constant open q is this tensor map preceded by inverse reduction of the completion
unit; substituting openSigmaHom cancels that inverse and proves OpenSquare.
Step 13: all constructions are natural transformations of ordinary derived strict diagrams.
Restricting their naturality to the common-window domain gives ProperNaturality and
OpenNaturality, including the quotient transitions. The hypotheses serve only to remain
in the recorded generator domain. Proper/open are Word.push and Word.open, respectively;
no GeneratorKind, word-length restriction, or compactification comparison is asserted. -/
theorem constantSemilinearGeneratorComparison
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (o : Operations C.l E)
    (V T : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (f : V ⟶ T) (lo hi torLo torHi : ℤ) :
    (IsProper f.left →
      ProperAdjunctionEquations C.l E o f.left ∧
      ProperNaturality C.l E o f.left lo hi torLo torHi ∧
      ∀ M : DerivedCategory (scalarReductionSource C.l E V.left),
        ProperDomain C.l E o f.left lo hi torLo torHi M →
        IsIso (properSigmaHom C.l E o f.left M) ∧ ProperSquare C.l E o f.left M) ∧
    (∀ [IsOpenImmersion f.left] [QuasiCompact f.left],
      ∃ a : sfCbcModelExtension f.left (constantRing C.l E) ⊣
          (sfCbcMorphism f.left).modulePull (ULift.{u + 1} (constantRing C.l E)),
        OpenAdjunctionEquations C.l E o f.left a ∧
        OpenNaturality C.l E o f.left a lo hi torLo torHi ∧
        ∀ M : DerivedCategory (scalarReductionSource C.l E V.left),
          OpenDomain C.l E o f.left lo hi torLo torHi M →
          IsIso (openSigmaHom C.l E f.left a M) ∧ OpenSquare C.l E o f.left a M) := by
  sorry

end WeilConjectures.GeneratorReduction
