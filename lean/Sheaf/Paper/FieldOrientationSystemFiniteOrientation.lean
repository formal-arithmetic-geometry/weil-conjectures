module

public import Sheaf.Paper.FieldOrientationSystemCoordinates

/-! Actual finite diagonal normalization of system orientations.
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

section FiniteNormalization
variable [IsNoetherian X] [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]

/-- Equality with the specified diagonal/DNC maps at every positive level, using
only the recorded finite right adjoint, its counit-normalized ordinary realization,
and the root-normalized source word. This is a concrete predicate on actual maps.
Source: blueprint (2), specified finite orientations
(blueprint: lem-sp-field-orientation-system-comparison). -/
def IsOrientation (E : Index P) (d : ℕ) (w : Coordinates P D E X)
    (v : Coordinates P D E Y)
    (h : normalized P D E Y (SpTowerGamma.unit P.coefficients.l E.val Y))
    (o : line P D w d ⟶ omega P D j p b a A E h) : Prop :=
  ∀ n : ℕ,
    letI : Finite (SpTowerShriek.R P.coefficients.l E.val n) := (D.base E).finite n
    ∃ dg : Etale.FiniteRingSectionDeformation.Geometry d
        (pullback.fst (j ≫ p) (j ≫ p)) (pullback.diagonal (j ≫ p)),
    ∃ alpha : Etale.dualizingComplex
        (ModuleCat.{u + 1} (SpTowerP1.levelRing P.coefficients.l E.val n)) (j ≫ p) ≅
      Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing P.coefficients.l E.val n)
        (P.coefficients.l ^ (n + 1)) (SpTowerP1.levelAnnihilates P.coefficients.l E.val n) X d,
      Etale.FiniteSmoothPurity.OrientationNormalized
        (SpTowerP1.levelRing P.coefficients.l E.val n) (P.coefficients.l ^ (n + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
        (SpTowerP1.levelAnnihilates P.coefficients.l E.val n) (j ≫ p) d dg (w.units n) alpha ∧
    ∃ ui : (A.finite E n).realization.origin.obj
        ((level P D a E Y n).obj (coefficientUnit P D E Y h)) ≅
      Etale.ordinaryFiniteUnit (SpTowerP1.levelRing P.coefficients.l E.val n) Y,
      (SpTowerP1.nu P.coefficients.l E.val n Y).map ui.hom ≫
          (unitWord P D v n).comparison =
        ((A.finite E n).realization.originIso.hom.app
          ((level P D a E Y n).obj (coefficientUnit P D E Y h))) ∧
      (lineWord P D w n d).comparison ≫
          (SpTowerShriek.Ev P.coefficients.l E.val X n).map o =
        (SpTowerP1.nu P.coefficients.l E.val n X).map
          (alpha.inv ≫
            (SpTowerGamma.finiteRightComparison (SpTowerShriek.R P.coefficients.l E.val n)
              j p (A.finite E n).closed (A.finite E n).right (A.finite E n).adj
              (A.finite E n).realization).inv.app _ ≫
            (A.finite E n).realization.right.map
              (ui ≪≫ Etale.singleFunctorObjUnitIso
                (ModuleCat.{u + 1} (SpTowerP1.levelRing P.coefficients.l E.val n)) Y).inv) ≫
          ((A.finite E n).realization.rightIso.inv.app
            ((level P D a E Y n).obj (coefficientUnit P D E Y h))) ≫
          ((A.evaluation E n).inv.app (coefficientUnit P D E Y h)).hom

end FiniteNormalization

attribute [irreducible] IsOrientation

end AlgebraicGeometry.ProEtale.FieldOrientationSystem
