module

public import Mathlib.CategoryTheory.Monoidal.Ring

@[expose] public section

universe vA vB uA uB

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory.Adjunction

/-- Transport of a single finite-product-preserving functor on commutative ring objects.
(blueprint: lem-weil-pbc-finite-product-ring-functor)
Source: Stacks Project, Proposition 00YV, paragraph on rings as sextuples.

Proof: on an object X take the underlying object F(X). Define addition and
multiplication by F of the original binary operation precomposed with the inverse
product comparison, zero and one using the inverse terminal comparison, and
negation by F of negation. For any term in n variables, its transported evaluation
composed with the comparison F(X^n) -> F(X)^n equals F of its original evaluation.
Prove this by induction: projections follow from the defining comparison;
constants follow from uniqueness of maps to the terminal object; operations follow
from naturality of binary comparisons and functoriality. Applying this identity to
both sides of associativity, units, inverses, commutativity and distributivity and
cancelling the comparison proves all CommRingObj axioms. Send a ring morphism f to
F(f). Naturality of the comparisons proves preservation of addition, multiplication,
zero and one; negation follows from the additive group structure. Functoriality
follows from that of F. The underlying objects and maps were chosen literally as
F(X) and F(f), so the forgetful equality holds strictly. Its eqToIso components
are identities, giving the displayed operation equations. -/
theorem finiteProductRingFunctor
    {A : Type uA} [Category.{vA} A] [CartesianMonoidalCategory A]
    {B : Type uB} [Category.{vB} B] [CartesianMonoidalCategory B]
    (F : A ⥤ B) [PreservesFiniteProducts F] :
    letI : BraidedCategory A := BraidedCategory.ofCartesianMonoidalCategory
    letI : BraidedCategory B := BraidedCategory.ofCartesianMonoidalCategory
    ∃ (FF : CommRingObjCat A ⥤ CommRingObjCat B)
      (hF : FF ⋙ CommRingObjCat.forget B = CommRingObjCat.forget A ⋙ F),
      let eF := eqToIso hF
      (∀ X : CommRingObjCat A,
            AddMonObj.add (X := (FF.obj X).X) ≫ eF.hom.app X =
              (eF.hom.app X ⊗ₘ eF.hom.app X) ≫
                (prodComparisonIso F X.X X.X).inv ≫ F.map (AddMonObj.add (X := X.X)) ∧
            AddMonObj.zero (X := (FF.obj X).X) ≫ eF.hom.app X =
              (preservesTerminalIso F).inv ≫ F.map (AddMonObj.zero (X := X.X)) ∧
            AddGrpObj.neg (X := (FF.obj X).X) ≫ eF.hom.app X =
              eF.hom.app X ≫ F.map (AddGrpObj.neg (X := X.X)) ∧
            MonObj.mul (X := (FF.obj X).X) ≫ eF.hom.app X =
              (eF.hom.app X ⊗ₘ eF.hom.app X) ≫
                (prodComparisonIso F X.X X.X).inv ≫ F.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (FF.obj X).X) ≫ eF.hom.app X =
              (preservesTerminalIso F).inv ≫ F.map (MonObj.one (X := X.X))) := by
  sorry

end CategoryTheory.Adjunction
