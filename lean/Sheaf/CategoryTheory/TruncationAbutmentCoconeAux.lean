module

public import Sheaf.CategoryTheory.TruncationCouple
public import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

@[expose] public section
universe u₁ u₂ v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Auxiliary compatibility package for the normalized truncation cocone.
Source: Stacks Tag 05TC (2), blueprint step 5; (blueprint: lem-sp-truncation-abutment-cocone-aux)
The proof expands the bridge naturality, the truncation transition identity, and induction on
`incomingAlphaIter`; it is split from the existential cocone theorem to isolate these equations. -/
theorem truncation_abutment_cocone_aux
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [IsGrothendieckAbelian.{v₁} A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) (X : BigradedExactCouple B 0)
    (hD : X.D = TruncationCouple.D F K)
    (halpha : ∀ p q : ℤ, X.alpha p q =
      eqToHom (by rw [hD]) ≫ TruncationCouple.alpha F K p q ≫
        eqToHom (by rw [hD]))
    (H : ℤ → B) (hH : H = fun n : ℤ ↦ (DerivedCategory.homologyFunctor B n).obj
      (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K.obj)))
    (j : ∀ n q : ℤ, X.D (n - q) q ⟶ H n)
    (c : ∀ n : ℤ, X.D 0 n ⟶ H n)
    (hj : ∀ n q, j n q = eqToHom (by rw [hD]; unfold TruncationCouple.D; congr 1; omega) ≫
      (TruncationCouple.bridgeIso F (TruncationCouple.truncation K q) n).inv ≫
      (DerivedCategory.homologyFunctor B n).map
        (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE q))) ≫
      eqToHom (by rw [hH]))
    (hc : ∀ n, c n = eqToHom (by congr 1; omega) ≫ j n n) :
    (∀ n, IsIso (c n)) ∧
    (∀ n p, X.alphaDiagonal n p ≫ eqToHom (by congr 1; omega) ≫ j n (n-p) =
      eqToHom (by congr 1; omega) ≫ j n (n-(p+1))) ∧
    (∀ (n p : ℤ) (_ : 0 ≤ p), eqToHom (by congr 1 <;> omega) ≫ j n (n-p) =
      X.incomingAlphaIter p.toNat 0 n ≫ c n) := by sorry

end CategoryTheory
