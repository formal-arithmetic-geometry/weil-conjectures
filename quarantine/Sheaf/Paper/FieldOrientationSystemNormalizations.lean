module

public import Sheaf.Paper.FieldOrientationSystemFiniteOrientation

/-! Unit- and root-normalized system scalar comparisons.
Source: blueprint (2) (blueprint: lem-sp-field-orientation-system-comparison). -/

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

variable {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (p : Z ⟶ Y) [IsProper p]
  (b : FieldShriekSystem.Laws P D (SpTowerGamma.factorization j p))
  (a : Domains P D (SpTowerGamma.factorization j p))
  (A : Adjoints P D (SpTowerGamma.factorization j p) b a)

/-- Canonical finite normalization of a whole-system coefficient-unit comparison.
The right side is the ordinary scalar unit comparison, transported by the canonical
site/scalar isomorphism. Thus no automorphism of the coefficient unit is permitted.
Source: blueprint (2), C_Y J_A = J_B
(blueprint: lem-sp-field-orientation-system-comparison). -/
def IsUnitComparison {E F : Index P} (hEF : E ≤ F)
    (vE : Coordinates P D E Y) (vF : Coordinates P D F Y)
    (q : (D.scalars E F hEF Y).T.obj (SpTowerGamma.unit P.coefficients.l E.val Y) ⟶
      SpTowerGamma.unit P.coefficients.l F.val Y) : Prop :=
  ∀ n : ℕ,
    letI : Finite (SpTowerShriek.R P.coefficients.l E.val n) := (D.base E).finite n
    letI : Finite (SpTowerShriek.R P.coefficients.l F.val n) := (D.base F).finite n
    (scalarExtensionFunctor ((D.coefficients E F hEF).quotient n) Y).map
        (unitWord P D vE n).comparison ≫
      (b.scalarEvaluation E F hEF Y n).iso.inv.app _ ≫
      (SpTowerShriek.Ev P.coefficients.l F.val Y n).map q =
    (reductionSiteScalarIso ((D.coefficients E F hEF).quotient n) Y).hom.app _ ≫
      (SpTowerP1.nu P.coefficients.l F.val n Y).map
        (Etale.FiniteSmoothPurity.scalarZeroLineIso
          (RingHom.ulift.{u + 1, u + 1, u, u} ((D.coefficients E F hEF).quotient n))
          (P.coefficients.l ^ (n + 1)) (P.coefficients.l ^ (n + 1))
          (SpTowerP1.levelAnnihilates P.coefficients.l E.val n)
          (SpTowerP1.levelAnnihilates P.coefficients.l F.val n) Y).hom ≫
      (unitWord P D vF n).comparison

/-- Canonical finite normalization of coefficient extension on the shifted Tate line.
Each finite comparison fixes the root of unity and extends its scalar coefficient.
Source: blueprint (2), canonical coefficient comparison of twists
(blueprint: lem-sp-field-orientation-system-comparison). -/
def IsLineComparison {E F : Index P} (hEF : E ≤ F)
    (wE : Coordinates P D E X) (wF : Coordinates P D F X) (d : ℕ)
    (q : (D.scalars E F hEF X).T.obj (line P D wE d) ⟶ line P D wF d) : Prop :=
  ∀ n : ℕ,
    letI : Finite (SpTowerShriek.R P.coefficients.l E.val n) := (D.base E).finite n
    letI : Finite (SpTowerShriek.R P.coefficients.l F.val n) := (D.base F).finite n
    ∃ e : Etale.FiniteSmoothPurity.CoefficientLineComparison
        (RingHom.ulift.{u + 1, u + 1, u, u} ((D.coefficients E F hEF).quotient n))
        (P.coefficients.l ^ (n + 1)) (P.coefficients.l ^ (n + 1))
        (SpTowerP1.levelAnnihilates P.coefficients.l E.val n)
        (SpTowerP1.levelAnnihilates P.coefficients.l F.val n) X,
      e.roots = 𝟙 _ ∧
      (scalarExtensionFunctor ((D.coefficients E F hEF).quotient n) X).map
          (lineWord P D wE n d).comparison ≫
        (b.scalarEvaluation E F hEF X n).iso.inv.app _ ≫
        (SpTowerShriek.Ev P.coefficients.l F.val X n).map q =
      (reductionSiteScalarIso ((D.coefficients E F hEF).quotient n) X).hom.app _ ≫
        (SpTowerP1.nu P.coefficients.l F.val n X).map (e.tensorPower d).hom ≫
        (lineWord P D wF n d).comparison


attribute [irreducible] IsUnitComparison IsLineComparison

end AlgebraicGeometry.ProEtale.FieldOrientationSystem
