/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.FourierTransform.FdCoefficientComparison
public import WeilConjectures.CategoryTheory.StageSystem.CommonStageCalculus

/-! # Presentations for raw scalar comparisons

Notation and data for the raw localization of scalar comparisons between coefficient stages:
completed and ordinary integral transitions, the rational transitions with their associators and
unitors, and the four-field associator contractions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FdRawLocalization

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- The completed integral scalar-extension transition along `E ≤ L`. -/
abbrev U {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :=
  sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
    (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
    (pbcFiniteFieldInclusion l Ω h) T

/-- The specified shift structure on the completed integral transition. -/
instance uCommShift {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    (U l Ω T h).CommShift ℤ :=
  (GeneralAlgebraicallyClosedCoefficients.integralScalarCommShift_existsUnique l
    (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
    (pbcFiniteFieldInclusion l Ω h) T).exists.choose

/-- The ordinary integral scalar-extension transition along `E ≤ L`. -/
abbrev C {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :=
  pbcIntegralScalarExtension l Ω T dT.out iT.out h

/-- Associativity of the completed integral transitions, including the transport along the
composite coefficient inclusion. -/
def integralAssoc {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M) :
    U l Ω T h ⋙ U l Ω T k ≅ U l Ω T (h.trans k) :=
  sfIntegralScalarComp l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
    (pbcFiniteFieldInclusion l Ω h) T 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
    (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω k) ≪≫
  eqToIso (congrArg (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω M) · T)
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k))

/-- The completed integral transition along `E ≤ E` is isomorphic to the identity. -/
def integralUnit (E : Padic.FiniteCoefficientFields l Ω) :
    U l Ω T (le_refl E) ≅ 𝟭 _ :=
  eqToIso (congrArg (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω E) · T)
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 E)) ≪≫
  sfIntegralScalarUnit l (pbcFiniteField.{u} l Ω E) T 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime))

/-- The rational scalar-extension transition along `E ≤ L`. -/
abbrev scalar {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :=
  GeneralAlgebraicallyClosedCoefficients.transition l Ω T E L h

/-- The specified shift structure on the rational transition. -/
instance scalarCommShift {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    (scalar l Ω T h).CommShift ℤ :=
  GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω T E L h

/-- The associator of the rational transitions. -/
abbrev assoc {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M) :=
  GeneralAlgebraicallyClosedCoefficients.associator l Ω T E L M h k

/-- The unitor of the rational transitions. -/
abbrev unit (E : Padic.FiniteCoefficientFields l Ω) :=
  GeneralAlgebraicallyClosedCoefficients.unitor l Ω T E

/-- The raw scalar system on the stage categories. -/
abbrev P := pbcScalarSystem l Ω T dT.out iT.out

variable (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)

/-- The supplied integral functor of the stage comparison at `E`. -/
abbrev I (E : Padic.FiniteCoefficientFields l Ω) := (stage E).integral.functor

/-- The supplied rational functor of the stage comparison at `E`. -/
abbrev suppliedJ (E : Padic.FiniteCoefficientFields l Ω) := (stage E).rational.functor

/-- A family of functors from the coefficient stages to the stage categories, with shift
structures, agreeing (up to `HEq`) with the supplied rational functors and their shifts. -/
structure RationalFamily where
  functor : ∀ E : Padic.FiniteCoefficientFields l Ω,
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E ⥤ pbcStageCategory l Ω T E
  identity : ∀ E, HEq (functor E) (suppliedJ l Ω T stage E)
  [shift : ∀ E, (functor E).CommShift ℤ]
  shift_identity : ∀ E (n : ℤ),
    HEq ((functor E).commShiftIso n) ((suppliedJ l Ω T stage E).commShiftIso n)

attribute [instance] RationalFamily.shift

variable (family : RationalFamily l Ω T stage)

/-- The rational functor of the family at `E`. -/
abbrev J (E : Padic.FiniteCoefficientFields l Ω) := family.functor E

/-- The type of families of isomorphisms `scalar h ⋙ J L ≅ J E ⋙ T h` comparing the rational
transitions with the raw scalar system. -/
abbrev RawComparison := ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
  scalar l Ω T h ⋙ J l Ω T stage family L ≅ J l Ω T stage family E ⋙ (P l Ω T).T h

/-- The composite of the three successive comparisons along `E ≤ L ≤ M ≤ N` at `K`. -/
def fourComparison (j : RawComparison l Ω T stage family)
    {E L M N : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M) (m : M ≤ N)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :=
  (j m).hom.app ((scalar l Ω T k).obj ((scalar l Ω T h).obj K)) ≫
    ((P l Ω T).T m).map ((j k).hom.app ((scalar l Ω T h).obj K)) ≫
    ((P l Ω T).T m).map (((P l Ω T).T k).map ((j h).hom.app K))

/-- The associator contraction in the four-field diagram that first contracts `E ≤ L ≤ M`. -/
def leftContraction {E L M N : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :=
  (scalar l Ω T m).map ((assoc l Ω T h k).hom.app K) ≫
    (assoc l Ω T (h.trans k) m).hom.app K

/-- The associator contraction in the four-field diagram that first contracts `L ≤ M ≤ N`. -/
def rightContraction {E L M N : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :=
  (assoc l Ω T k m).hom.app ((scalar l Ω T h).obj K) ≫
    (assoc l Ω T h (k.trans m)).hom.app K

end WeilConjectures.FdRawLocalization
