module

public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! Operation preservation for the inverse restricted adjunct. -/

@[expose] public section

universe vA vB uA uB

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory.Adjunction

set_option autoImplicit false

/-- The inverse adjunct preserves ring operations.
Source: Stacks Project, Proposition 00YV, proof of (2), extended there to rings.

Proof: For a binary operation m, let rho be R's product comparison and lambda L's. Naturality of
epsilon at the two projections, together with the projection equations of rho and lambda, gives
L(rho inverse) followed by epsilon_(Y times Y) equal to lambda_(RY,RY) followed by (epsilon_Y
times epsilon_Y). Check this equality by composing with each projection; cancel the invertible
product comparisons when checking. Naturality of epsilon at m_Y then identifies the composite of L
of the transported binary operation with epsilon_Y with the product of epsilon_Y's followed by
m_Y. Substitute opsL and opsR and the equation m_X followed by g equals (g times g) followed by
m_(RF Y). Cancel eL and eR to obtain m_(LF X) followed by the conjugated inverse adjunct equal to
the product of two copies of that adjunct followed by m_Y. Apply this to addition and
multiplication. For a constant q, naturality at q_Y and uniqueness of the map into the terminal
object identify the composite of the inverse terminal comparisons and epsilon_terminal with the
identity. With the constant equations opsL, opsR, and that for g, this proves q_(LF X) followed by
the inverse adjunct equals q_Y, both for zero and for one. Package zero and addition as
IsAddMonHom and one and multiplication as IsMonHom; these give IsRingHom. Negation preservation
follows from additivity and is not a field of IsRingHom.
(blueprint: lem-weil-pbc-ring-coadjunct-preserves-operations)
-/
theorem ringCoadjunctPreservesOperations
    {A : Type uA} [Category.{vA} A] [CartesianMonoidalCategory A]
    {B : Type uB} [Category.{vB} B] [CartesianMonoidalCategory B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    [PreservesFiniteProducts L] [PreservesFiniteProducts R]
    [BraidedCategory A] [BraidedCategory B]
    (LF : CommRingObjCat A ⥤ CommRingObjCat B) (RF : CommRingObjCat B ⥤ CommRingObjCat A)
    (hL : LF ⋙ CommRingObjCat.forget B = CommRingObjCat.forget A ⋙ L)
    (hR : RF ⋙ CommRingObjCat.forget A = CommRingObjCat.forget B ⋙ R)
    (opsL : let eL := eqToIso hL; (∀ X : CommRingObjCat A,
            AddMonObj.add (X := (LF.obj X).X) ≫ eL.hom.app X =
              (eL.hom.app X ⊗ₘ eL.hom.app X) ≫
                (prodComparisonIso L X.X X.X).inv ≫ L.map (AddMonObj.add (X := X.X)) ∧
            AddMonObj.zero (X := (LF.obj X).X) ≫ eL.hom.app X =
              (preservesTerminalIso L).inv ≫ L.map (AddMonObj.zero (X := X.X)) ∧
            AddGrpObj.neg (X := (LF.obj X).X) ≫ eL.hom.app X =
              eL.hom.app X ≫ L.map (AddGrpObj.neg (X := X.X)) ∧
            MonObj.mul (X := (LF.obj X).X) ≫ eL.hom.app X =
              (eL.hom.app X ⊗ₘ eL.hom.app X) ≫
                (prodComparisonIso L X.X X.X).inv ≫ L.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (LF.obj X).X) ≫ eL.hom.app X =
              (preservesTerminalIso L).inv ≫ L.map (MonObj.one (X := X.X))))
    (opsR : let eR := eqToIso hR; (∀ X : CommRingObjCat B,
            AddMonObj.add (X := (RF.obj X).X) ≫ eR.hom.app X =
              (eR.hom.app X ⊗ₘ eR.hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (AddMonObj.add (X := X.X)) ∧
            AddMonObj.zero (X := (RF.obj X).X) ≫ eR.hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (AddMonObj.zero (X := X.X)) ∧
            AddGrpObj.neg (X := (RF.obj X).X) ≫ eR.hom.app X =
              eR.hom.app X ≫ R.map (AddGrpObj.neg (X := X.X)) ∧
            MonObj.mul (X := (RF.obj X).X) ≫ eR.hom.app X =
              (eR.hom.app X ⊗ₘ eR.hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (RF.obj X).X) ≫ eR.hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (MonObj.one (X := X.X)))) :
    ∀ (X : CommRingObjCat A) (Y : CommRingObjCat B) (g : X ⟶ RF.obj Y),
      IsRingHom (show (LF.obj X).X ⟶ Y.X from (eqToIso hL).hom.app X ≫
        (adj.homEquiv X.X Y.X).symm (g.hom ≫ (eqToIso hR).hom.app Y)) := by sorry

end CategoryTheory.Adjunction
