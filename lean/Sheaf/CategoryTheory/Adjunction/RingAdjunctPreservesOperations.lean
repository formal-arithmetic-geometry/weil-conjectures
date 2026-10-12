module

public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! Operation preservation for the forward restricted adjunct. -/

@[expose] public section

universe vA vB uA uB

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory.Adjunction

set_option autoImplicit false

/-- The forward adjunct preserves ring operations.
Source: Stacks Project, Proposition 00YV, proof of (2), extended there to rings.

Proof: For a binary operation m, write lambda for the comparison of L and rho for that of R.
Naturality of eta at the two projections gives eta_(X times X) followed by R(lambda) and rho equal
to eta_X times eta_X: the two projections of these maps are eta_X followed by the corresponding
projection. Thus eta_(X times X) followed by R(lambda) equals (eta_X times eta_X) followed
by rho inverse. Naturality at m_X gives m_X followed by eta_X equal to eta_(X times X) followed by
RL(m_X). Combine these identities with opsL, opsR, and the equation m_(LF X) followed by f equals
(f times f) followed by m_Y. Cancel the component isomorphisms eL and eR to obtain m_X followed by
the displayed conjugated adjunct equal to the product of two copies of that adjunct followed by
m_(RF Y). Apply this once to addition and once to multiplication. For a constant q, naturality at
q_X gives q_X followed by eta_X equal to eta_terminal followed by RL(q_X). The composite of
eta_terminal with the images of the two terminal comparison maps is the unique terminal
endomorphism, hence the identity. Using opsL, opsR and the constant equation for f gives q_X
followed by the conjugated adjunct equal to q_(RF Y), for q zero and one. The zero and addition
equations give IsAddMonHom; the one and multiplication equations give IsMonHom. These yield
IsRingHom. No separate negation equation is required for IsRingHom.
(blueprint: lem-weil-pbc-ring-adjunct-preserves-operations) -/
theorem ringAdjunctPreservesOperations
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
    ∀ (X : CommRingObjCat A) (Y : CommRingObjCat B) (f : LF.obj X ⟶ Y),
      IsRingHom (show X.X ⟶ (RF.obj Y).X from adj.homEquiv X.X Y.X
        ((eqToIso hL).inv.app X ≫ f.hom) ≫ (eqToIso hR).inv.app Y) := by sorry

end CategoryTheory.Adjunction
