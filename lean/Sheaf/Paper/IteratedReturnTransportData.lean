module

public import Sheaf.Paper.RealizedPullbackComparisons
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.TraceFormula.PointTransportComposition
public import Sheaf.Paper.LocalFrobeniusTrace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.Paper.FieldDerivedScalarTower

/-! # Definitions for iterated point return transport

Source: blueprint main-20261015, sec-trace-formula/sk-thm-trace-transport,
prop-trf-karoubi-independence.proof.md, final sentence
(blueprint: def-trf-iterated-return-transport-data).

## Main definitions and statement

* `pointIterate` defines the stipulated recursion for I.
* `finiteReturn`, `integralReturn`, `rationalReturn` define the actual return comparison.
* `ScalarEquations` gives the two scalar identities, including whole quotient diagrams.
* `Properties` collects naturality and the identity and tower normalizations.
* The proof theorem stays in `IteratedReturnTransportScalarCalculus`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

universe u v w a b c
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

namespace IteratedReturnTransport

/-- The functor U^j in the specified point-transport recursion.
Source: blueprint trace-transport, local normalization Step 2
(blueprint: def-trf-iterated-return-transport-data). -/
def iterate {C : Type a} [Category.{b} C] (U : C ⥤ C) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | j + 1 => iterate U j ⋙ U

/-- I^0 is identity and I^(j+1) is iota at U^j N after I^j.
Source: blueprint trace-transport, local normalization Step 2
(blueprint: def-trf-iterated-return-transport-data). -/
def pointIterate {C : Type a} [Category.{b} C] {V : Type c} [Category.{v} V]
    (B : C ⥤ V) (U : C ⥤ C) (ι : ∀ N : C, B.obj N ⟶ B.obj (U.obj N))
    (N : C) : (j : ℕ) → B.obj N ⟶ B.obj ((iterate U j).obj N)
  | 0 => 𝟙 _
  | j + 1 => pointIterate B U ι N j ≫ ι ((iterate U j).obj N)

/-- The iterated specified compositor, from pullback along g^(r+1) to repeated pullback.
Source: Stacks 0D6D; blueprint trace-transport, local normalization Step 2
(blueprint: def-trf-iterated-return-transport-data). -/
def powerComparison {S : Type a} [Category.{b} S] (X : S)
    {C : Type c} [Category.{v} C] (F : (X ⟶ X) → C ⥤ C)
    (comp : ∀ (h k : X ⟶ X) (N : C),
      (F (h ≫ k)).obj N ≅ (F h).obj ((F k).obj N)) (g : X ⟶ X) :
    (r : ℕ) → (N : C) → (F ((End.of g) ^ (r + 1))).obj N ≅
      (iterate (F g) (r + 1)).obj N
  | 0, N => eqToIso (congrArg (fun h ↦ (F h).obj N) (pow_one (End.of g)))
  | r + 1, N =>
    eqToIso (congrArg (fun h ↦ (F h).obj N) (pow_succ (End.of g) (r + 1))) ≪≫
      comp g ((End.of g) ^ (r + 1)) N ≪≫ (F g).mapIso (powerComparison X F comp g r N)

/-- Iterate the actual one-step scalar comparison; the zero step is the identity.
Source: blueprint trace-transport, local normalization Step 9
(blueprint: def-trf-iterated-return-transport-data). -/
def scalarIterate {C : Type a} [Category.{b} C] {V : Type c} [Category.{v} V]
    (T : C ⥤ V) (U : C ⥤ C) (W : V ⥤ V)
    (α : ∀ N : C, T.obj (U.obj N) ≅ W.obj (T.obj N)) :
    (j : ℕ) → (N : C) → T.obj ((iterate U j).obj N) ≅
      (iterate W j).obj (T.obj N)
  | 0, N => Iso.refl (T.obj N)
  | j + 1, N => α ((iterate U j).obj N) ≪≫ W.mapIso (scalarIterate T U W α j N)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The finite-level compositor in intrinsic coordinates, using both unit-normalized
presentation comparisons from the recorded finite composition interface.
Source: Stacks 0D6D; blueprint trace-transport, specified-family paragraph
(blueprint: def-trf-iterated-return-transport-data). -/
def finiteComposition (n : ℕ) {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :
    finiteDerivedPullback l E n (h ≫ k) ≅
      finiteDerivedPullback l E n k ⋙ finiteDerivedPullback l E n h :=
  pointPowerPullbackModel l E n (h ≫ k) ≪≫
    integralFiniteCanonicalPullbackComposition l E h k n ≪≫
    Functor.isoWhiskerRight (pointPowerPullbackModel l E n k).symm _ ≪≫
    Functor.isoWhiskerLeft _ (pointPowerPullbackModel l E n h).symm

/-- The finite v, with the common composite identified by the actual return-square equality.
The endpoint functors are successive one-step pullbacks.
Source: Stacks 0D6D; blueprint trace-transport, local normalization Step 2
(blueprint: def-trf-iterated-return-transport-data). -/
def finiteReturn (n r : ℕ) (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)))
    (K : proEtaleDerivedCategory (D.geometricFiber X₀).left
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  (powerComparison (Spec (.of D.k)) (finiteDerivedPullback l E n)
      (fun h k N ↦ (finiteComposition l E n h k).app N)
      (frobeniusPointIso D).hom r ((finiteDerivedPullback l E n z).obj K)).symm ≪≫
    ((finiteComposition l E n _ z).app K).symm ≪≫
    eqToIso (congrArg (fun f ↦ (finiteDerivedPullback l E n f).obj K) w) ≪≫
    (finiteComposition l E n z _).app K ≪≫
    (finiteDerivedPullback l E n z).mapIso
      (powerComparison (D.geometricFiber X₀).left (finiteDerivedPullback l E n)
        (fun h k N ↦ (finiteComposition l E n h k).app N)
        (D.geometricFrobenius X₀).hom r K)

variable (C : IntegralComparisonSystem.{u} l)
  [hpoint : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x)]
  [hspace : ∀ x : (D.geometricFiber X₀).left,
    Invertible (l : (D.geometricFiber X₀).left.residueField x)]

/-- Integral v, built from exactly the counit-normalized integral compositors.
Source: blueprint trace-transport, local normalization Step 2
(blueprint: def-trf-iterated-return-transport-data). -/
def integralReturn (r : ℕ) (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)))
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :=
  (powerComparison (Spec (.of D.k)) (fun f ↦ constructibleIntegralPullback l E f)
      (fun h k N ↦ integralComparisonConstructibleComposition l E C h k N)
      (frobeniusPointIso D).hom r ((constructibleIntegralPullback l E z).obj K)).symm ≪≫
    (integralComparisonConstructibleComposition l E C
      ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) z K).symm ≪≫
    eqToIso (congrArg
      (fun f : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left ↦
        (constructibleIntegralPullback l E f).obj K) w) ≪≫
    integralComparisonConstructibleComposition l E C z
      ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)) K ≪≫
    (constructibleIntegralPullback l E z).mapIso
      (powerComparison (D.geometricFiber X₀).left (fun f ↦ constructibleIntegralPullback l E f)
        (fun h k N ↦ integralComparisonConstructibleComposition l E C h k N)
        (D.geometricFrobenius X₀).hom r K)

/-- Rational v is the rationalization of the same normalized compositors.
Source: blueprint trace-transport, local normalization Steps 2 and 8
(blueprint: def-trf-iterated-return-transport-data). -/
def rationalReturn (r : ℕ) (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)))
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :=
  (powerComparison (Spec (.of D.k)) (fun f ↦ rationalDerivedPullback l E f)
      (fun h k N ↦ integralComparisonRationalComposition l E C h k N)
      (frobeniusPointIso D).hom r ((rationalDerivedPullback l E z).obj K)).symm ≪≫
    (integralComparisonRationalComposition l E C
      ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) z K).symm ≪≫
    eqToIso (congrArg
      (fun f : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left ↦
        (rationalDerivedPullback l E f).obj K) w) ≪≫
    integralComparisonRationalComposition l E C z
      ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)) K ≪≫
    (rationalDerivedPullback l E z).mapIso
      (powerComparison (D.geometricFiber X₀).left (fun f ↦ rationalDerivedPullback l E f)
        (fun h k N ↦ integralComparisonRationalComposition l E C h k N)
        (D.geometricFrobenius X₀).hom r K)

/-- I^m at the finite quotient stage, before restricting the fully faithful bounded target.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def finiteI (n : ℕ) :=
  pointIterate
    (@Functor.mapDerivedCategory
    (integralOperationsFiniteModules l E (Spec (.of D.k)) n) _ _
    (HasDerivedCategory.standard _)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
    _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFiniteSectionsAdditive D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteLimits D (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteColimits D (Padic.coefficientExtensionRing l E (n + 1))))
    (finiteDerivedPullback l E n (frobeniusPointIso D).hom)
    (frobeniusPointTransportFinite D l hl E n)

/-- I^m in the derived-complete integral point category.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def integralI :=
  pointIterate (pointIntegralFibre D l hl E)
    (constructibleIntegralPullback l E (frobeniusPointIso D).hom)
    (frobeniusPointTransportIntegralConstructible D l hl E)

/-- I^m in the raw rational point category, on every rational morphism.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def rationalI :=
  pointIterate (pointRationalFibre D l hl E)
    (rationalDerivedPullback l E (frobeniusPointIso D).hom)
    (localPointTransport l E D hl)

/-- t = Fib(v) after I^m at the finite coefficient stage.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def finiteTransport (n r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)))
    (K : proEtaleDerivedCategory (D.geometricFiber X₀).left
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  finiteI D l hl E n ((finiteDerivedPullback l E n z).obj K) (r + 1) ≫
    (@Functor.mapDerivedCategory
    (integralOperationsFiniteModules l E (Spec (.of D.k)) n) _ _
    (HasDerivedCategory.standard _)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
    _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFiniteSectionsAdditive D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteLimits D (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteColimits D (Padic.coefficientExtensionRing l E (n + 1)))).map
      (finiteReturn D l E X₀ n r z w K).hom

/-- t = Fib(v) after I^m at the integral coefficient stage.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def integralTransport (r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)))
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :=
  integralI D l hl E ((constructibleIntegralPullback l E z).obj K) (r + 1) ≫
    (pointIntegralFibre D l hl E).map
      (integralReturn D l E X₀ C r z w K).hom

/-- t = Fib(v) after I^m at the rational coefficient stage.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def rationalTransport (r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)))
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :=
  rationalI D l hl E ((rationalDerivedPullback l E z).obj K) (r + 1) ≫
    (pointRationalFibre D l hl E).map
      (rationalReturn D l E X₀ C r z w K).hom

/-- Naturality at finite coefficients; the source and point arguments are precisely
the recorded bounded constructible categories. Equality is tested in the ambient
derived module category, whose bounded-target inclusion is fully faithful.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def FiniteNaturality (n r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) : Prop :=
  (∀ (N J : (intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).FullSubcategory) (f : N ⟶ J),
    finiteI D l hl E n N.obj (r + 1) ≫
        (@Functor.mapDerivedCategory
    (integralOperationsFiniteModules l E (Spec (.of D.k)) n) _ _
    (HasDerivedCategory.standard _)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
    _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFiniteSectionsAdditive D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteLimits D (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteColimits D (Padic.coefficientExtensionRing l E (n + 1)))).map
          ((iterate (finiteDerivedPullback l E n (frobeniusPointIso D).hom) (r + 1)).map f.hom) =
      ((pointFiniteFibre D l hl E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n))).map f).hom ≫
        finiteI D l hl E n J.obj (r + 1)) ∧
  (∀ (K J : (intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (D.geometricFiber X₀).left).FullSubcategory)
      (f : K ⟶ J),
    finiteTransport D l hl E X₀ n r z w K.obj ≫
        (@Functor.mapDerivedCategory
    (integralOperationsFiniteModules l E (Spec (.of D.k)) n) _ _
    (HasDerivedCategory.standard _)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
    _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFiniteSectionsAdditive D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteLimits D (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteColimits D (Padic.coefficientExtensionRing l E (n + 1)))).map
          ((finiteDerivedPullback l E n z).map
            ((iterate (finiteDerivedPullback l E n (D.geometricFrobenius X₀).hom)
              (r + 1)).map f.hom)) =
      (@Functor.mapDerivedCategory
    (integralOperationsFiniteModules l E (Spec (.of D.k)) n) _ _
    (HasDerivedCategory.standard _)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
    _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFiniteSectionsAdditive D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteLimits D (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteColimits D (Padic.coefficientExtensionRing l E (n + 1)))).map
          ((finiteDerivedPullback l E n z).map f.hom) ≫
        finiteTransport D l hl E X₀ n r z w J.obj)

/-- The two naturality assertions at the integral stage.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def IntegralNaturality (r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) : Prop :=
  (∀ (N J : sfIntegralConstructibleCategory l E (Spec (.of D.k))) (f : N ⟶ J),
    integralI D l hl E N (r + 1) ≫ (pointIntegralFibre D l hl E).map
        ((iterate (constructibleIntegralPullback l E (frobeniusPointIso D).hom) (r + 1)).map f) =
      (pointIntegralFibre D l hl E).map f ≫ integralI D l hl E J (r + 1)) ∧
  (∀ (K J : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) (f : K ⟶ J),
    integralTransport D l hl E X₀ C r z w K ≫
        (pointIntegralFibre D l hl E).map ((constructibleIntegralPullback l E z).map
          ((iterate (constructibleIntegralPullback l E (D.geometricFrobenius X₀).hom)
            (r + 1)).map f)) =
      (pointIntegralFibre D l hl E).map ((constructibleIntegralPullback l E z).map f) ≫
        integralTransport D l hl E X₀ C r z w J)

/-- The two naturality assertions at the rational stage.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def RationalNaturality (r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) : Prop :=
  (∀ (N J : sfRationalConstructibleCategory l E (Spec (.of D.k))) (f : N ⟶ J),
    rationalI D l hl E N (r + 1) ≫ (pointRationalFibre D l hl E).map
        ((iterate (rationalDerivedPullback l E (frobeniusPointIso D).hom) (r + 1)).map f) =
      (pointRationalFibre D l hl E).map f ≫ rationalI D l hl E J (r + 1)) ∧
  (∀ (K J : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) (f : K ⟶ J),
    rationalTransport D l hl E X₀ C r z w K ≫
        (pointRationalFibre D l hl E).map ((rationalDerivedPullback l E z).map
          ((iterate (rationalDerivedPullback l E (D.geometricFrobenius X₀).hom) (r + 1)).map f)) =
      (pointRationalFibre D l hl E).map ((rationalDerivedPullback l E z).map f) ≫
        rationalTransport D l hl E X₀ C r z w J)

/-- The same return-square composite on whole simultaneous quotient diagrams, before
derived localization or integral realization.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def systemReturn (r : ℕ) (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1)))
    (K : coefficientSequenceModules l E (D.geometricFiber X₀).left) :=
  (powerComparison (Spec (.of D.k)) (integralComparisonSequencePullback.{u, u} l E)
      (fun h k N ↦ (integralComparisonSequenceComposition.{u, u} l E h k).app N)
      (frobeniusPointIso D).hom r
      ((integralComparisonSequencePullback.{u, u} l E z).obj K)).symm ≪≫
    ((integralComparisonSequenceComposition.{u, u} l E _ z).app K).symm ≪≫
    eqToIso (congrArg
      (fun f ↦ (integralComparisonSequencePullback.{u, u} l E f).obj K) w) ≪≫
    (integralComparisonSequenceComposition.{u, u} l E z _).app K ≪≫
    (integralComparisonSequencePullback.{u, u} l E z).mapIso
      (powerComparison (D.geometricFiber X₀).left (integralComparisonSequencePullback.{u, u} l E)
        (fun h k N ↦ (integralComparisonSequenceComposition.{u, u} l E h k).app N)
        (D.geometricFrobenius X₀).hom r K)

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (ι : E →ₐ[ℚ_[l]] M)

/-- The specified system pullback/scalar comparison, iterated through every one-step pullback.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def systemPowerScalar (Y : Scheme.{u})
    (g : Y ⟶ Y) (m : ℕ) (K : coefficientSequenceModules l E Y) :=
  scalarIterate ((integralComparisonSequenceScalarModel.{u, u} l E M ι Y).E)
    (integralComparisonSequencePullback.{u, u} l E g)
      (integralComparisonSequencePullback.{u, u} l M g)
      (fun N ↦ (integralComparisonSequenceScalarPullback.{u, u} l E M ι g).app N) m K

/-- The specified integral pullback/scalar comparison, iterated through every one-step pullback.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def integralPowerScalar (Y : Scheme.{u})
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (g : Y ⟶ Y) (m : ℕ) (K : sfIntegralConstructibleCategory l E Y) :=
  scalarIterate (integralComparisonConstructibleScalar l E M ι Y)
    (constructibleIntegralPullback l E g) (constructibleIntegralPullback l M g)
      (fun N ↦ ObjectProperty.isoMk _ (integralComparisonScalar l E M ι C g N)) m K

/-- The specified rational pullback/scalar comparison, iterated through every one-step pullback.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def rationalPowerScalar (Y : Scheme.{u})
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (g : Y ⟶ Y) (m : ℕ) (K : sfRationalConstructibleCategory l E Y) :=
  scalarIterate (sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι)
    (rationalDerivedPullback l E g) (rationalDerivedPullback l M g)
      (fun N ↦ (integralComparisonRationalScalar l E C M ι g).app N) m K

section ScalarEquation

variable {CX CS DX DS : Type a} [Category.{b} CX] [Category.{b} CS]
  [Category.{b} DX] [Category.{b} DS]

/-- The first displayed scalar equation, in Lean composition order.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def ReturnScalarEquation (P : CX ⥤ CS) (Q : DX ⥤ DS)
    (U : CS ⥤ CS) (W : DS ⥤ DS) (G : CX ⥤ CX) (H : DX ⥤ DX)
    (S : CS ⥤ DS) (T : CX ⥤ DX) (m : ℕ)
    (a : ∀ K : CX, S.obj (P.obj K) ≅ Q.obj (T.obj K))
    (δ : ∀ N : CS, S.obj ((iterate U m).obj N) ≅ (iterate W m).obj (S.obj N))
    (d : ∀ K : CX, T.obj ((iterate G m).obj K) ≅ (iterate H m).obj (T.obj K))
    (vE : ∀ K : CX, (iterate U m).obj (P.obj K) ≅ P.obj ((iterate G m).obj K))
    (vM : ∀ K : DX, (iterate W m).obj (Q.obj K) ≅ Q.obj ((iterate H m).obj K)) : Prop :=
  ∀ K : CX,
    (δ (P.obj K)).hom ≫ (iterate W m).map (a K).hom ≫ (vM (T.obj K)).hom =
      S.map (vE K).hom ≫ (a ((iterate G m).obj K)).hom ≫ Q.map (d K).hom

/-- The second displayed scalar equation, using the same iterated point comparison δ.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def PointScalarEquation {VE VM : Type c} [Category.{v} VE] [Category.{v} VM]
    (U : CS ⥤ CS) (W : DS ⥤ DS) (S : CS ⥤ DS) (B : CS ⥤ VE) (B' : DS ⥤ VM)
    (V : VE ⥤ VM) (m : ℕ)
    (δ : ∀ N : CS, S.obj ((iterate U m).obj N) ≅ (iterate W m).obj (S.obj N))
    (β : ∀ N : CS, V.obj (B.obj N) ≅ B'.obj (S.obj N))
    (IE : ∀ N : CS, B.obj N ⟶ B.obj ((iterate U m).obj N))
    (IM : ∀ N : DS, B'.obj N ⟶ B'.obj ((iterate W m).obj N)) : Prop :=
  ∀ N : CS, V.map (IE N) ≫ (β ((iterate U m).obj N)).hom ≫ B'.map (δ N).hom =
    (β N).hom ≫ IM (S.obj N)

end ScalarEquation

/-- The first scalar identity for the actual system return comparisons.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def SystemScalarEquation (r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) : Prop :=
  ReturnScalarEquation (integralComparisonSequencePullback.{u, u} l E z)
    (integralComparisonSequencePullback.{u, u} l M z)
    (integralComparisonSequencePullback.{u, u} l E (frobeniusPointIso D).hom)
      (integralComparisonSequencePullback.{u, u} l M (frobeniusPointIso D).hom)
    (integralComparisonSequencePullback.{u, u} l E (D.geometricFrobenius X₀).hom)
    (integralComparisonSequencePullback.{u, u} l M (D.geometricFrobenius X₀).hom)
    ((integralComparisonSequenceScalarModel.{u, u} l E M ι (Spec (.of D.k))).E)
    ((integralComparisonSequenceScalarModel.{u, u} l E M ι (D.geometricFiber X₀).left).E) (r + 1)
    (fun K ↦ (integralComparisonSequenceScalarPullback.{u, u} l E M ι z).app K)
    (systemPowerScalar l E M ι (Spec (.of D.k)) (frobeniusPointIso D).hom (r + 1))
    (systemPowerScalar l E M ι (D.geometricFiber X₀).left (D.geometricFrobenius X₀).hom (r + 1))
    (systemReturn D l E X₀ r z w)
    (systemReturn D l M X₀ r z w)

/-- The first scalar identity for the actual integral return comparisons.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def IntegralScalarEquation (r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) : Prop :=
  ReturnScalarEquation (constructibleIntegralPullback l E z) (constructibleIntegralPullback l M z)
    (constructibleIntegralPullback l E (frobeniusPointIso D).hom)
      (constructibleIntegralPullback l M (frobeniusPointIso D).hom)
    (constructibleIntegralPullback l E (D.geometricFrobenius X₀).hom)
    (constructibleIntegralPullback l M (D.geometricFrobenius X₀).hom)
    (integralComparisonConstructibleScalar l E M ι (Spec (.of D.k)))
    (integralComparisonConstructibleScalar l E M ι (D.geometricFiber X₀).left) (r + 1)
    (fun K ↦ ObjectProperty.isoMk _ (integralComparisonScalar l E M ι C z K))
    (integralPowerScalar l E C M ι (Spec (.of D.k)) (frobeniusPointIso D).hom (r + 1))
    (integralPowerScalar l E C M ι (D.geometricFiber X₀).left (D.geometricFrobenius X₀).hom (r + 1))
    (integralReturn D l E X₀ C r z w)
    (integralReturn D l M X₀ C r z w)

/-- The first scalar identity for the actual rational return comparisons.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def RationalScalarEquation (r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) : Prop :=
  ReturnScalarEquation (rationalDerivedPullback l E z) (rationalDerivedPullback l M z)
    (rationalDerivedPullback l E (frobeniusPointIso D).hom)
      (rationalDerivedPullback l M (frobeniusPointIso D).hom)
    (rationalDerivedPullback l E (D.geometricFrobenius X₀).hom)
    (rationalDerivedPullback l M (D.geometricFrobenius X₀).hom)
    (sfRationalScalarExtension l E (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι)
    (sfRationalScalarExtension l E (D.geometricFiber X₀).left 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι) (r + 1)
    (fun K ↦ (integralComparisonRationalScalar l E C M ι z).app K)
    (rationalPowerScalar l E C M ι (Spec (.of D.k)) (frobeniusPointIso D).hom (r + 1))
    (rationalPowerScalar l E C M ι (D.geometricFiber X₀).left (D.geometricFrobenius X₀).hom (r + 1))
    (rationalReturn D l E X₀ C r z w)
    (rationalReturn D l M X₀ C r z w)

/-- The second scalar identity with inverse of the actual rational point-sections
comparison, in the finite-dimensional module target.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def RationalPointScalarEquation (m : ℕ) : Prop :=
  PointScalarEquation
    (rationalDerivedPullback l E (frobeniusPointIso D).hom)
    (rationalDerivedPullback l M (frobeniusPointIso D).hom)
    (sfRationalScalarExtension l E (Spec (.of D.k)) 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι)
    (pointRationalFibre D l hl E) (pointRationalFibre D l hl M)
    (DerivedCategory.pointFdScalarExtension ι.toRingHom) m
    (rationalPowerScalar l E C M ι (Spec (.of D.k)) (frobeniusPointIso D).hom m)
    (fun N ↦ ((pointRationalFibreScalarIso D l hl E M ι).app N).symm)
    (fun N ↦ rationalI D l hl E N m) (fun N ↦ rationalI D l hl M N m)

/-- Unit normalization for the iterated actual pullback/scalar comparison.
Source: blueprint trace-transport, local normalization Steps 8 and 9
(blueprint: def-trf-iterated-return-transport-data). -/
def PowerScalarUnit {A : Type a} [Category.{b} A]
    (U T : A ⥤ A) (m : ℕ)
    (δ : ∀ N : A, T.obj ((iterate U m).obj N) ≅ (iterate U m).obj (T.obj N))
    (unit : ∀ N : A, T.obj N ≅ N) : Prop :=
  ∀ N : A, (δ N).hom ≫ (iterate U m).map (unit N).hom = (unit _).hom

/-- Tower normalization for the iterated actual pullback/scalar comparison.
Source: blueprint trace-transport, local normalization Steps 8 and 9
(blueprint: def-trf-iterated-return-transport-data). -/
def PowerScalarTower {A B V : Type a} [Category.{b} A] [Category.{b} B] [Category.{b} V]
    (U : A ⥤ A) (W : B ⥤ B) (Z : V ⥤ V)
    (T : A ⥤ B) (S : B ⥤ V) (R : A ⥤ V) (m : ℕ)
    (δT : ∀ N : A, T.obj ((iterate U m).obj N) ≅ (iterate W m).obj (T.obj N))
    (δS : ∀ N : B, S.obj ((iterate W m).obj N) ≅ (iterate Z m).obj (S.obj N))
    (δR : ∀ N : A, R.obj ((iterate U m).obj N) ≅ (iterate Z m).obj (R.obj N))
    (assoc : ∀ N : A, S.obj (T.obj N) ≅ R.obj N) : Prop :=
  ∀ N : A, S.map (δT N).hom ≫ (δS (T.obj N)).hom ≫
      (iterate Z m).map (assoc N).hom = (assoc ((iterate U m).obj N)).hom ≫ (δR N).hom

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (j : M →ₐ[ℚ_[l]] L)

/-- Identity and successive coefficient extension at the system stage,
with the specified multiplication unit and tensor associator.
Source: blueprint trace-transport, local normalization Steps 8 and 9
(blueprint: def-trf-iterated-return-transport-data). -/
def SystemPowerNormalization (Y : Scheme.{u})
    (g : Y ⟶ Y) (m : ℕ) : Prop :=
  PowerScalarUnit (integralComparisonSequencePullback.{u, u} l E g)
    ((integralComparisonSequenceScalarModel.{u, u} l E E (AlgHom.id ℚ_[l] E) Y).E) m
    (systemPowerScalar l E E (AlgHom.id ℚ_[l] E) Y g m)
      (fun N ↦ (integralComparisonSequenceScalarUnit.{u, u} l E Y).app N) ∧
  PowerScalarTower (integralComparisonSequencePullback.{u, u} l E g)
    (integralComparisonSequencePullback.{u, u} l M g)
    (integralComparisonSequencePullback.{u, u} l L g)
    ((integralComparisonSequenceScalarModel.{u, u} l E M ι Y).E)
    ((integralComparisonSequenceScalarModel.{u, u} l M L j Y).E)
    ((integralComparisonSequenceScalarModel.{u, u} l E L (j.comp ι) Y).E) m
    (systemPowerScalar l E M ι Y g m)
    (systemPowerScalar l M L j Y g m)
    (systemPowerScalar l E L (j.comp ι) Y g m)
    (fun N ↦ (integralComparisonSequenceScalarComposition.{u, u} l E M ι L j Y).app N)

/-- Identity and successive coefficient extension at the integral stage,
with the specified multiplication unit and tensor associator.
Source: blueprint trace-transport, local normalization Steps 8 and 9
(blueprint: def-trf-iterated-return-transport-data). -/
def IntegralPowerNormalization (Y : Scheme.{u})
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (g : Y ⟶ Y) (m : ℕ) : Prop :=
  PowerScalarUnit (constructibleIntegralPullback l E g)
    (integralComparisonConstructibleScalar l E E (AlgHom.id ℚ_[l] E) Y) m
    (integralPowerScalar l E C E (AlgHom.id ℚ_[l] E) Y g m)
      (fun N ↦ ObjectProperty.isoMk _ (integralComparisonScalarUnit l E Y N)) ∧
  PowerScalarTower (constructibleIntegralPullback l E g) (constructibleIntegralPullback l M g)
    (constructibleIntegralPullback l L g)
    (integralComparisonConstructibleScalar l E M ι Y)
    (integralComparisonConstructibleScalar l M L j Y)
    (integralComparisonConstructibleScalar l E L (j.comp ι) Y) m
    (integralPowerScalar l E C M ι Y g m)
    (integralPowerScalar l M C L j Y g m)
    (integralPowerScalar l E C L (j.comp ι) Y g m)
    (fun N ↦ ObjectProperty.isoMk _ (integralComparisonScalarAssociator l E M ι L j Y N))

/-- Identity and successive coefficient extension at the rational stage,
with the specified multiplication unit and tensor associator.
Source: blueprint trace-transport, local normalization Steps 8 and 9
(blueprint: def-trf-iterated-return-transport-data). -/
def RationalPowerNormalization (Y : Scheme.{u})
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (g : Y ⟶ Y) (m : ℕ) : Prop :=
  PowerScalarUnit (rationalDerivedPullback l E g)
    (sfRationalScalarExtension l E Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E (AlgHom.id ℚ_[l] E)) m
    (rationalPowerScalar l E C E (AlgHom.id ℚ_[l] E) Y g m) (fun N ↦ (sfRationalScalarUnit l E Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime))).app N) ∧
  PowerScalarTower (rationalDerivedPullback l E g) (rationalDerivedPullback l M g)
    (rationalDerivedPullback l L g)
    (sfRationalScalarExtension l E Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι)
    (sfRationalScalarExtension l M Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L j)
    (sfRationalScalarExtension l E Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L (j.comp ι)) m
    (rationalPowerScalar l E C M ι Y g m)
    (rationalPowerScalar l M C L j Y g m)
    (rationalPowerScalar l E C L (j.comp ι) Y g m)
    (fun N ↦ (sfRationalScalarComp l E M ι Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L j).app N)

/-- Identity and successive-extension compatibility of the inverse point-sections
comparison β. The finite-dimensional target is included fully faithfully into D(E).
Source: blueprint trace-transport, local normalization Steps 8 and 9
(blueprint: def-trf-iterated-return-transport-data). -/
def PointScalarNormalization : Prop :=
  (∀ N : sfRationalConstructibleCategory l E (Spec (.of D.k)),
    (((pointRationalFibreScalarIso D l hl E E (AlgHom.id ℚ_[l] E)).app N).inv).hom ≫
        ((pointRationalFibre D l hl E).map
          ((sfRationalScalarUnit l E (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app N)).hom =
      (DerivedCategory.fieldScalarUnit E).hom.app ((pointRationalFibre D l hl E).obj N).obj) ∧
  (∀ N : sfRationalConstructibleCategory l E (Spec (.of D.k)),
    ((DerivedCategory.pointFdScalarExtension j.toRingHom).map
        ((pointRationalFibreScalarIso D l hl E M ι).inv.app N)).hom ≫
        ((pointRationalFibreScalarIso D l hl M L j).inv.app
          ((sfRationalScalarExtension l E (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) M ι).obj N)).hom ≫
        ((pointRationalFibre D l hl L).map
          ((sfRationalScalarComp l E M ι (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L j).hom.app N)).hom =
      ((pointFibreFdTensorTower ι.toRingHom j.toRingHom).hom.app
        ((pointRationalFibre D l hl E).obj N)).hom ≫
        ((pointRationalFibreScalarIso D l hl E L (j.comp ι)).inv.app N).hom)

/-- The two scalar equations at the three required realizations, with the same δ
in the return equation and in the point transport equation.
Source: blueprint trace-transport, local normalization Steps 8 and 9
(blueprint: def-trf-iterated-return-transport-data). -/
def ScalarEquations (r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) : Prop :=
  SystemScalarEquation D l E X₀ M ι r z w ∧
    IntegralScalarEquation D l E X₀ C M ι r z w ∧
    RationalScalarEquation D l E X₀ C M ι r z w ∧
    RationalPointScalarEquation D l hl E C M ι (r + 1)

/-- All clauses of the node, with canonical prime-invertibility instances supplied
from the finite-field datum. The three levels use exactly the same return equality;
scalar equations and their normalization use the same actual comparisons throughout.
Source: blueprint trace-transport, local normalization Steps 2, 8, 9
(blueprint: def-trf-iterated-return-transport-data). -/
def Properties (r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : ((End.of (frobeniusPointIso D).hom) ^ (r + 1)) ≫ z =
      z ≫ ((End.of (D.geometricFrobenius X₀).hom) ^ (r + 1))) : Prop :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl X₀
  (∀ n : ℕ, FiniteNaturality D l hl E X₀ n r z w) ∧
    IntegralNaturality D l hl E X₀ C r z w ∧
    RationalNaturality D l hl E X₀ C r z w ∧
    ScalarEquations D l hl E X₀ C M ι r z w ∧
    SystemPowerNormalization l E M ι L j (Spec (.of D.k))
      (frobeniusPointIso D).hom (r + 1) ∧
    SystemPowerNormalization l E M ι L j (D.geometricFiber X₀).left
      (D.geometricFrobenius X₀).hom (r + 1) ∧
    IntegralPowerNormalization l E C M ι L j (Spec (.of D.k))
      (frobeniusPointIso D).hom (r + 1) ∧
    IntegralPowerNormalization l E C M ι L j (D.geometricFiber X₀).left
      (D.geometricFrobenius X₀).hom (r + 1) ∧
    RationalPowerNormalization l E C M ι L j (Spec (.of D.k))
      (frobeniusPointIso D).hom (r + 1) ∧
    RationalPowerNormalization l E C M ι L j (D.geometricFiber X₀).left
      (D.geometricFrobenius X₀).hom (r + 1) ∧
    PointScalarNormalization D l hl E M ι L j

end IteratedReturnTransport

end WeilConjectures
