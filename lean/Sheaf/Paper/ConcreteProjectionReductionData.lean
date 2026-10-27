/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.SixFunctors.OpenScalarTensorData
public import Sheaf.Paper.IntegralCompactSupportCoefficientData
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison

/-! # The specified finite coefficient projection comparisons

Source: Stacks Tags 07A4, 0GL1, 0GL6 and 0D6D.
(blueprint: def-sf-concrete-projection-reduction-data).

These are the unchanged comparison definitions extracted from
ConcreteProjectionReductionSquare so that normalization lemmas can state their
properties without importing the theorem which uses them. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.ConcreteProjectionReduction
open AlgebraicGeometry.ProEtale.OpenScalarTensor

/-- The constant coefficient system with its specified inverse-image identifications.
Source: Stacks 03EL (blueprint: def-sf-concrete-projection-reduction-data). -/
@[reducible] def coefficients (A : Type u) [CommRing A] : PurCompactSupport.Coefficients.{u} where
  ring T := proEtaleConstantRing T A
  pull f := proEtaleConstantRingComparison f A

/-- The actual map of constant coefficient systems, including its naturality square.
Source: Stacks 03EL (blueprint: def-sf-concrete-projection-reduction-data). -/
@[reducible] def coefficientChange {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    PurCompactSupport.Change (coefficients A) (coefficients B) where
  map T := proEtaleConstantRingMap (T := T) φ
  square f := (proEtaleConstantInverseImageMap_naturality f
    (CommRingCat.ofHom (RingHom.ulift φ))).symm

/-- The chosen proper/open compact-support candidate, in ringed constant coordinates.
Source: Stacks 0GL6 (blueprint: def-sf-concrete-projection-reduction-data). -/
abbrev support (A : Type u) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) := PurCompactSupport.image (coefficients A) c

variable (m : Models.{u}) (choices : Choices m)

/-- The prescribed tensor input H = K tensor Lf*L.
Source: Stacks 07A4 (blueprint: def-sf-concrete-projection-reduction-data). -/
abbrev input (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : proEtaleDerivedCategory X A) (L : proEtaleDerivedCategory Y A) :=
  (tensor m A X).obj (K, (constantPullback (A := A) f).obj L)

/-- The source S of the actual compactification projection.
Source: Stacks 0GL1 (blueprint: def-sf-concrete-projection-reduction-data). -/
abbrev source (A : Type u) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : proEtaleDerivedCategory X A)
    (L : proEtaleDerivedCategory Y A) := (tensor m A Y).obj ((support A c).obj K, L)

/-- The target T of the actual compactification projection.
Source: Stacks 0GL1 (blueprint: def-sf-concrete-projection-reduction-data). -/
abbrev target (A : Type u) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : proEtaleDerivedCategory X A)
    (L : proEtaleDerivedCategory Y A) := (support A c).obj (input m A f K L)

/-- The specified counit-defined proper projection followed by the open tensor map.
This evaluates the dependency's compactificationProjectionFromData, with its canonical
representative-normalized mu and gamma, rather than choosing a map of endpoints.
Source: Stacks 0B56, 0GL1 (blueprint: def-sf-concrete-projection-reduction-data). -/
def projection (A : Type u) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : proEtaleDerivedCategory X A)
    (L : proEtaleDerivedCategory Y A) : source m A c K L ⟶ target m A c K L :=
  ((PurCompactSupport.projectionMap (coefficients A) c
    (tensorModel m A X) (tensorModel m A c.Z) (tensorModel m A Y)
    (proEtaleConstantRingCompositeCoefficients_eq c.i c.g A).symm).app K).app L

/-- The normalized support comparison is uniquely fixed to its original explicit formula.
Source: Stacks 0GL6 (blueprint: def-sf-concrete-projection-reduction-data).
Proof: that formula is a witness, and equality to it implies uniqueness. -/
theorem supportComparison_existsUnique {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) :
    ∃! e : (scalar m φ Y).obj ((support A c).obj K) ⟶
      (support B c).obj ((scalar m φ X).obj K),
      e = (scalarIso m φ Y).hom.app ((support A c).obj K) ≫
    (PurCompactSupport.comparison (coefficientChange φ) c).app K ≫
    (support B c).map ((scalarIso m φ X).inv.app K) := by
  exact ⟨_, rfl, fun _ h ↦ h⟩

/-- The scalar-adjunction mate of the canonical proper/open restriction comparison.
The two scalarIso factors only change the normalized representative presentation.
Source: Stacks 0GL6 (blueprint: def-sf-concrete-projection-reduction-data). -/
def supportComparison {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) :
    (scalar m φ Y).obj ((support A c).obj K) ⟶
      (support B c).obj ((scalar m φ X).obj K) :=
  (supportComparison_existsUnique m φ c K).exists.choose

/-- Explicit equation for the prescribed support comparison.
Source: Stacks 0GL6 (blueprint: def-sf-concrete-projection-reduction-data).
Proof: this is its unique equality specification. -/
theorem supportComparison_eq {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) :
    supportComparison m φ c K = (scalarIso m φ Y).hom.app ((support A c).obj K) ≫
    (PurCompactSupport.comparison (coefficientChange φ) c).app K ≫
    (support B c).map ((scalarIso m φ X).inv.app K) :=
  (supportComparison_existsUnique m φ c K).exists.choose_spec

/-- Tensor first, followed by the canonical scalar/pullback identification.
Source: Stacks 07A4 (blueprint: def-sf-concrete-projection-reduction-data). -/
def inputComparison {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : proEtaleDerivedCategory X A)
    (L : proEtaleDerivedCategory Y A) :
    (scalar m φ X).obj (input m A f K L) ≅
      input m B f ((scalar m φ X).obj K) ((scalar m φ Y).obj L) :=
  (choices.scalarTensor φ X).iso.app (K, (constantPullback (A := A) f).obj L) ≪≫
    (tensor m B X).mapIso
      ((Iso.refl _).prod ((lambda m φ f).symm.app L))

/-- u: tensor comparison followed by compact-support comparison in the first factor.
Source: Stacks 0GL6, 07A4 (blueprint: def-sf-concrete-projection-reduction-data). -/
def sourceComparison {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) (L : proEtaleDerivedCategory Y A) :
    (scalar m φ Y).obj (source m A c K L) ⟶
      source m B c ((scalar m φ X).obj K) ((scalar m φ Y).obj L) :=
  (choices.scalarTensor φ Y).iso.hom.app ((support A c).obj K, L) ≫
    (tensor m B Y).map (Prod.mkHom (supportComparison m φ c K) (𝟙 _))

/-- v: compact-support comparison followed by tensor and pullback comparisons.
Source: Stacks 0GL6, 07A4 (blueprint: def-sf-concrete-projection-reduction-data). -/
def targetComparison {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) (L : proEtaleDerivedCategory Y A) :
    (scalar m φ Y).obj (target m A c K L) ⟶
      target m B c ((scalar m φ X).obj K) ((scalar m φ Y).obj L) :=
  supportComparison m φ c (input m A f K L) ≫
    (support B c).map (inputComparison m choices φ f K L).hom


/-- The source functor on pairs, for naturality and scalar-associativity transport.
Source: Stacks 0GL1 (blueprint: def-sf-concrete-projection-reduction-data). -/
def sourceFunctor (A : Type u) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) := (support A c).prod (𝟭 _) ⋙ tensor m A Y

/-- The target functor on pairs, retaining the geometric pullback.
Source: Stacks 0GL1 (blueprint: def-sf-concrete-projection-reduction-data). -/
def targetFunctor (A : Type u) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :=
  (𝟭 _).prod (constantPullback (A := A) f) ⋙ tensor m A X ⋙ support A c

/-- The two canonical endpoint maps form a natural commuting projection square.
This asserts invertibility only of u and v. All arrows are the definitions above.
Source: Stacks 0GL6, 0E48 (blueprint: def-sf-concrete-projection-reduction-data). -/
def Square {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) (L : proEtaleDerivedCategory Y A) : Prop :=
  IsIso (sourceComparison m choices φ c K L) ∧
  IsIso (targetComparison m choices φ c K L) ∧
  (scalar m φ Y).map (projection m A c K L) ≫ targetComparison m choices φ c K L =
    sourceComparison m choices φ c K L ≫
      projection m B c ((scalar m φ X).obj K) ((scalar m φ Y).obj L)

/-- Naturality of both endpoint comparisons in both inputs, and of the projection map.
Source: Stacks 0GL1, 0GL6 (blueprint: def-sf-concrete-projection-reduction-data). -/
def Naturality {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : Prop :=
  ∀ (K K' : proEtaleDerivedCategory X A) (L L' : proEtaleDerivedCategory Y A)
    (a : K ⟶ K') (b : L ⟶ L'),
    (scalar m φ Y).map ((sourceFunctor m A c).map (Prod.mkHom a b)) ≫
        sourceComparison m choices φ c K' L' =
      sourceComparison m choices φ c K L ≫ (sourceFunctor m B c).map
        (Prod.mkHom ((scalar m φ X).map a) ((scalar m φ Y).map b)) ∧
    (scalar m φ Y).map ((targetFunctor m A c).map (Prod.mkHom a b)) ≫
        targetComparison m choices φ c K' L' =
      targetComparison m choices φ c K L ≫ (targetFunctor m B c).map
        (Prod.mkHom ((scalar m φ X).map a) ((scalar m φ Y).map b)) ∧
    (sourceFunctor m A c).map (Prod.mkHom a b) ≫ projection m A c K' L' =
      projection m A c K L ≫ (targetFunctor m A c).map (Prod.mkHom a b)

/-- The successive-reduction cocycle for u and v, with balanced associativity
inserted at both inputs and the output. The direct coefficient map is psi composed
with phi; for quotient maps this is precisely the quotient from n to r.
Source: Stacks 0D6D, 0E47 (blueprint: def-sf-concrete-projection-reduction-data). -/
def Composition {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : proEtaleDerivedCategory X A)
    (L : proEtaleDerivedCategory Y A) : Prop :=
  (scalar m ψ Y).map (sourceComparison m choices φ c K L) ≫
      sourceComparison m choices ψ c ((scalar m φ X).obj K) ((scalar m φ Y).obj L) ≫
      (sourceFunctor m C c).map (Prod.mkHom ((scalarComp m φ ψ X).hom.app K)
        ((scalarComp m φ ψ Y).hom.app L)) =
    (scalarComp m φ ψ Y).hom.app (source m A c K L) ≫
      sourceComparison m choices (ψ.comp φ) c K L ∧
  (scalar m ψ Y).map (targetComparison m choices φ c K L) ≫
      targetComparison m choices ψ c ((scalar m φ X).obj K) ((scalar m φ Y).obj L) ≫
      (targetFunctor m C c).map (Prod.mkHom ((scalarComp m φ ψ X).hom.app K)
        ((scalarComp m φ ψ Y).hom.app L)) =
    (scalarComp m φ ψ Y).hom.app (target m A c K L) ≫
      targetComparison m choices (ψ.comp φ) c K L

/-- Identity reductions give identity endpoint comparisons under the scalar unitors.
Source: Stacks 07A6 (blueprint: def-sf-concrete-projection-reduction-data). -/
def Identity (A : Type u) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : proEtaleDerivedCategory X A)
    (L : proEtaleDerivedCategory Y A) : Prop :=
  sourceComparison m choices (RingHom.id A) c K L ≫
      (sourceFunctor m A c).map (Prod.mkHom ((scalarId m A X).hom.app K)
        ((scalarId m A Y).hom.app L)) = (scalarId m A Y).hom.app (source m A c K L) ∧
  targetComparison m choices (RingHom.id A) c K L ≫
      (targetFunctor m A c).map (Prod.mkHom ((scalarId m A X).hom.app K)
        ((scalarId m A Y).hom.app L)) = (scalarId m A Y).hom.app (target m A c K L)

/-- The actual quotient map from exponent n to exponent m, induced by identity on R.
Source: blueprint finite-reduction paragraph
(blueprint: def-sf-concrete-projection-reduction-data). -/
def quotient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {m n : ℕ} (hmn : m ≤ n) :
    Padic.coefficientExtensionRing l E n →+* Padic.coefficientExtensionRing l E m :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)


end WeilConjectures.ConcreteProjectionReduction
