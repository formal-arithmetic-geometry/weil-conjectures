module

public import Sheaf.Paper.FieldOrientationSystemNormalizations
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! Canonical concentrated-object presentations for the orientation comparison.
Source: blueprint (2), shifted-heart assembly
(blueprint: lem-sp-field-orientation-system-comparison). -/

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
variable {X : Scheme.{u}}

/-- The canonical cohomology sheaf of a shifted concentrated object. Using the
cohomology of the concrete ordered line fixes its heart object without choosing an
unrelated identification with an abstract Tate-line presentation.
Source: blueprint (2), shifted-heart assembly
(blueprint: lem-sp-field-orientation-system-comparison). -/
def heartSheaf {E : Index P} (V : SpTowerShriek.D P.coefficients.l E.val X) (s : ℤ) :=
  (DerivedCategory.homologyFunctor _ 0).obj (V⟦-s⟧)

/-- Shift back the normalized identification with the sole cohomology sheaf.
Source: blueprint (2), the concentrated-object identification
(blueprint: lem-sp-field-orientation-system-comparison). -/
def heartIdentification {E : Index P} (V : SpTowerShriek.D P.coefficients.l E.val X)
    (s : ℤ) (i : (DerivedCategory.singleFunctor _ 0).obj (heartSheaf P V s) ≅ V⟦-s⟧) :
    ((DerivedCategory.singleFunctor _ 0).obj (heartSheaf P V s))⟦s⟧ ≅ V :=
  (shiftFunctor _ s).mapIso i ≪≫ shiftNegShift V s

/-- Exact level evaluation commutes with the single embedding and common shift.
These are the canonical functor comparisons, with no chosen endpoint arrow.
Source: blueprint (2), shifted-heart assembly
(blueprint: lem-sp-field-orientation-system-comparison). -/
def evaluationSingleShift {E : Index P}
    (M : SpTowerShriek.S P.coefficients.l E.val X) (n : ℕ) (s : ℤ) :
    (SpTowerShriek.Ev P.coefficients.l E.val X n).obj
        (((DerivedCategory.singleFunctor _ 0).obj M)⟦s⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        ((SpTowerShriek.ev P.coefficients.l E.val X n).obj M))⟦s⟧ :=
  ((SpTowerShriek.Ev P.coefficients.l E.val X n).commShiftIso s).app _ ≪≫
    (shiftFunctor _ s).mapIso
      (((SpTowerShriek.ev P.coefficients.l E.val X n).mapDerivedCategorySingleFunctor 0).app M)

/-- Both heart identifications induce the identity on the specified cohomology
sheaves. The system map is uniquely pinned by the finite orientation maps: a finite
sheaf map beta reconstructs the prescribed finite orientation if and only if beta
is its evaluation. The right side of that equation is the actual evaluated arrow
fixed by IsOrientation's finite diagonal/DNC normalization. This is the beta/evaluation
characterization of strict_line_heart_assembly, applied to the canonical heart of
the concrete ordered source line, rather than a freely chosen source isomorphism.
Source: blueprint (2), shifted-heart assembly
(blueprint: lem-sp-field-orientation-system-comparison). -/
def IsHeartInduced {E : Index P} (w : Coordinates P D E X) (d : ℕ)
    (V : SpTowerShriek.D P.coefficients.l E.val X) (o : line P D w d ⟶ V) : Prop :=
  ∃ (i : (DerivedCategory.singleFunctor _ 0).obj
        (heartSheaf P (line P D w d) (2 * (d : ℤ))) ≅
      (line P D w d)⟦-(2 * (d : ℤ))⟧)
    (j : (DerivedCategory.singleFunctor _ 0).obj
        (heartSheaf P V (2 * (d : ℤ))) ≅ V⟦-(2 * (d : ℤ))⟧),
    (DerivedCategory.homologyFunctor _ 0).map i.hom =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app _ ∧
    (DerivedCategory.homologyFunctor _ 0).map j.hom =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app _ ∧
    ∃! h : heartSheaf P (line P D w d) (2 * (d : ℤ)) ⟶
        heartSheaf P V (2 * (d : ℤ)),
      (o = (heartIdentification P (line P D w d) (2 * (d : ℤ)) i).inv ≫
        ((DerivedCategory.singleFunctor _ 0).map h)⟦2 * (d : ℤ)⟧' ≫
        (heartIdentification P V (2 * (d : ℤ)) j).hom) ∧
      ∀ (n : ℕ) (beta :
          (SpTowerShriek.ev P.coefficients.l E.val X n).obj
              (heartSheaf P (line P D w d) (2 * (d : ℤ))) ⟶
          (SpTowerShriek.ev P.coefficients.l E.val X n).obj
              (heartSheaf P V (2 * (d : ℤ)))),
        (SpTowerShriek.Ev P.coefficients.l E.val X n).map
              (heartIdentification P (line P D w d) (2 * (d : ℤ)) i).inv ≫
            (evaluationSingleShift P
              (heartSheaf P (line P D w d) (2 * (d : ℤ))) n (2 * (d : ℤ))).hom ≫
            ((DerivedCategory.singleFunctor _ 0).map beta)⟦2 * (d : ℤ)⟧' ≫
            (evaluationSingleShift P (heartSheaf P V (2 * (d : ℤ)))
              n (2 * (d : ℤ))).inv ≫
            (SpTowerShriek.Ev P.coefficients.l E.val X n).map
              (heartIdentification P V (2 * (d : ℤ)) j).hom =
          (SpTowerShriek.Ev P.coefficients.l E.val X n).map o ↔
        beta = (SpTowerShriek.ev P.coefficients.l E.val X n).map h

attribute [irreducible] IsHeartInduced

end AlgebraicGeometry.ProEtale.FieldOrientationSystem
