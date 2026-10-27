module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.SmoothPurityTowerGluing
public import Sheaf.Paper.SmoothPurityTowerShriekLevels
public import Sheaf.Paper.FieldShriekSystemComparison
public import Sheaf.Paper.FieldExceptionalSystemComparison
public import Sheaf.Paper.SmoothPurityTowerGamma
public import Sheaf.Paper.SmoothPurityTowerGammaData
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.SecSmoothPurity.ReductionCompatibilities

public import Sheaf.Paper.FieldShriekSystemModels
public import Sheaf.Paper.FieldExceptionalSystemDomains
public import Sheaf.Paper.FieldExceptionalSystemAdjoints
public import Sheaf.Paper.FieldExceptionalSystemComponents
public import Sheaf.Paper.SmoothPurityTowerChartData
public import Sheaf.Paper.SmoothPurityCoordinateRightComparisons
public import Sheaf.Paper.TowerP1CoefficientCoordinates
public import Sheaf.Paper.TowerP1TensorCoordinates
public import Sheaf.Paper.TowerP1LevelWords
public import Sheaf.Paper.FiniteSmoothPurityMaps
public import Sheaf.Paper.FiniteSmoothCoefficientArrows
public import Sheaf.Paper.FiniteRingSectionDeformation
public import Sheaf.SecSmoothPurity.ReductionExceptionalObjects
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer


/-! # Shifted-sheaf detection of the scalar orientation equation

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md (2),
rank-one tower orientation; returned step 6
(blueprint: lem-sp-field-orientation-system-comparison).

We use the dependency's actual strict-system derived category and its normalized
full subcategory. Positive coefficient exponent n+1 is indexed by n : ℕ.
All endpoint comparisons below retain their root, unit and counit normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.FieldOrientationSystem
open FieldShriekSystem FieldExceptionalSystem

variable (P : PurityFiniteSetting.{u}) (D : Models P)

/-- The actual coefficient unit, as an object of the specified normalized subcategory.
Source: blueprint (2), J_A (blueprint: lem-sp-field-orientation-system-comparison). -/
def coefficientUnit (E : Index P) (T : Scheme.{u})
    (h : normalized P D E T (SpTowerGamma.unit P.coefficients.l E.val T)) : N P D E T :=
  ⟨SpTowerGamma.unit P.coefficients.l E.val T, h⟩

/-- Root-normalized coordinates for the source of a tower orientation. These are the
coefficient, tensor and root comparisons of tower_gamma, before choosing an orientation.
Source: blueprint (2), J_X(d)[2d]
(blueprint: lem-sp-field-orientation-system-comparison). -/
structure Coordinates (E : Index P) (T : Scheme.{u}) where
  twists : SpChartAdmissibility.Twists P.coefficients.l E.val T
  roots : SpCoordinateAdjunction.RootLines P.coefficients.l E.val T
  units : ∀ n : ℕ, IsUnit ((P.coefficients.l ^ (n + 1) : ℕ) : Γ(T, ⊤))
  coefficients : ∀ n : ℕ,
    letI : Finite (SpTowerShriek.R P.coefficients.l E.val n) := (D.base E).finite n
    SpTowerP1.CoefficientCoordinates P.coefficients.l E.val n T (units n)
  tensors : ∀ n : ℕ,
    letI : Finite (SpTowerShriek.R P.coefficients.l E.val n) := (D.base E).finite n
    SpTowerP1.TensorCoordinates P.coefficients.l E.val n (D.base E) T

/-- The dependency's recursively ordered shifted Tate line.
Source: blueprint (2), orientation source
(blueprint: lem-sp-field-orientation-system-comparison). -/
def line {E : Index P} {T : Scheme.{u}} (w : Coordinates P D E T) (d : ℕ) :=
  SpTowerGamma.orderedLine P.coefficients.l E.val (D.base E) T w.twists d

/-- The specified finite evaluation word for that line, with no free endpoint map.
Source: blueprint (2), canonical twist comparison
(blueprint: lem-sp-field-orientation-system-comparison). -/
def lineWord {E : Index P} {T : Scheme.{u}} (w : Coordinates P D E T) (n d : ℕ) :=
  letI : Finite (SpTowerShriek.R P.coefficients.l E.val n) := (D.base E).finite n
  SpTowerGamma.coefficientWord P.coefficients.l E.val (D.base E) T w.twists w.roots n
    (w.units n) (w.coefficients n) (w.tensors n) d

/-- The specified finite unit evaluation word.
Source: blueprint (2), C_Y J_A = J_B
(blueprint: lem-sp-field-orientation-system-comparison). -/
def unitWord {E : Index P} {T : Scheme.{u}} (w : Coordinates P D E T) (n : ℕ) :=
  letI : Finite (SpTowerShriek.R P.coefficients.l E.val n) := (D.base E).finite n
  SpTowerP1.unitWord P.coefficients.l E.val n T (w.coefficients n)

variable {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (p : Z ⟶ Y) [IsProper p]
  (b : FieldShriekSystem.Laws P D (SpTowerGamma.factorization j p))
  (a : Domains P D (SpTowerGamma.factorization j p))
  (A : Adjoints P D (SpTowerGamma.factorization j p) b a)

/-- The dualizing object of the given tower adjunction, at the actual coefficient unit.
Source: blueprint (2), omega_A = G_A J_A
(blueprint: lem-sp-field-orientation-system-comparison). -/
def omega (E : Index P)
    (h : normalized P D E Y (SpTowerGamma.unit P.coefficients.l E.val Y)) :=
  ((A.right E).obj (coefficientUnit P D E Y h)).obj

end AlgebraicGeometry.ProEtale.FieldOrientationSystem
