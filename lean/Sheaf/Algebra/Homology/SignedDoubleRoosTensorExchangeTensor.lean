/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchangeDefinitions

/-! Signed double Roos interchange and tensor augmentation coherence. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe uC vC r w

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.SignedDoubleRoos

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  (R : Sheaf J CommRingCat.{r})

/-- Tensoring with a principal two-term Koszul tower commutes with Roos, including
its strict augmentation, for a signed interchange with the prescribed coordinates.

Source: Stacks Tags 012Z, 03EK, 014E, and 0941; steps 6--8 of
`lem-sp-signed-double-roos-tensor-exchange`
(blueprint: lem-sp-signed-double-roos-tensor-core).

Proof: tensoring a module with the unit sheaf is naturally isomorphic to that
module: the maps are x tensor r mapping to rx and x mapping to x tensor 1.
The sectionwise maps respect balancing and restrictions and descend through
sheafification. A principal Koszul complex has just the unit sheaf in degrees
-1 and 0. Hence each degree of its tensor with an unbounded complex is a binary
biproduct, and the product universal property commutes this biproduct with the
countable product. Apply these identifications to both Roos coordinates to
construct gamma and its inverse, preserving each tensor summand coordinate.
For intrinsic degree a, Roos degree p, and Koszul degree b, the differential
coefficients are (-1)^p, (-1)^(a+p), and -(1-s_n) on both sides; therefore the
maps are chain maps. The same coordinate tests prove naturality in the tower,
compatibility with Koszul transitions (t,1), and compatibility with evaluation.
The degree-zero Koszul inclusion is natural in the input complex; its compatible
family followed by the strict Roos lift gives eta, and the individual inclusions
give tau. They are precisely the fixed augmentation and strictAugmentation.
These maps have zero shifted Koszul-Roos coordinate. On an input with n-Roos
coordinates (v,u), the map Roos_n(eta) has coordinates
(v tensor 1,0,u tensor 1,0). The assumed formula for beta changes these to
(v tensor 1,u tensor 1,0,0). Thus both j-Roos-degree-one coordinates vanish,
and the other two are the stated coordinate inclusions. The previously checked
augmentation compatibility of gamma identifies this map, after Roos_j(gamma
inverse), with the strict augmentation of Roos_n Q. Equality follows by the
jointly monic product and biproduct projections, rather than by uniqueness of
maps in the derived category. This uses no regularity, boundedness, or torsion
assumption, and no preservation of arbitrary products by arbitrary tensor. -/
theorem signed_double_roos_tensor_core
    (β : rows R ≅ columns R)
    (hβ : (∀ (X : ℕᵒᵖ ⥤ Tower R) (p q : Bool) (k : ℤ) (n j : ℕ),
        (β.hom.app X).f k ≫ columnCoordinate R X p q k n j =
          if p && q then -rowCoordinate R X p q k n j
          else rowCoordinate R X p q k n j)) :
      ∀ t : (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections,
        ∃ (η : 𝟭 (Complex R) ⟶ completion R t)
          (τ : ∀ j : ℕ, 𝟭 (Complex R) ⟶
            tensorTower R t ⋙ (CategoryTheory.evaluation ℕᵒᵖ (Complex R)).obj (op j))
          (γ : ∀ Q : Tower R,
            (tensorTower R t).obj ((roos R).obj Q) ≅
              (Q ⋙ tensorTower R t).flip ⋙ roos R),
          (∀ P : Complex R, η.app P = augmentation R P t) ∧
          (∀ (P : Complex R) (j : ℕ),
            (τ j).app P = (strictAugmentation R P t).app (op j)) ∧
          (∀ (Q Q' : Tower R) (f : Q ⟶ Q') (j : ℕ),
            ((tensorTower R t).map ((roos R).map f)).app (op j) ≫
                (γ Q').hom.app (op j) =
              (γ Q).hom.app (op j) ≫ (roos R).map
                (((flipFunctor _ _ _).map
                  (Functor.whiskerRight f (tensorTower R t))).app (op j))) ∧
          (∀ (Q : Tower R) (j : ℕ) (p : Bool) (a b k : ℤ) (h : a + b = k) (n : ℕ),
            HomologicalComplex.ιTensorObj ((roos R).obj Q) (principalKoszul R t j)
                a b k h ≫ ((γ Q).hom.app (op j)).f k ≫
                coordinate R ((Q ⋙ tensorTower R t).flip.obj (op j)) p k n =
              (coordinate R Q p a n ▷ (principalKoszul R t j).X b) ≫
                HomologicalComplex.ιTensorObj (Q.obj (op n)) (principalKoszul R t j)
                  (a - degree p) b (k - degree p) (by omega)) ∧
          (∀ (Q : Tower R) (j n : ℕ),
            (γ Q).hom.app (op j) ≫
                evaluation R ((Q ⋙ tensorTower R t).flip.obj (op j)) n =
              (evaluation R Q n ▷ principalKoszul R t j)) ∧
          (∀ (Q : Tower R) (j : ℕ),
            (strictAugmentation R ((roos R).obj Q) t).app (op j) ≫
                (γ Q).hom.app (op j) =
              (roos R).map (Q.rightUnitor.inv ≫ Functor.whiskerLeft Q (τ j))) ∧
          (∀ Q : Tower R,
            (roos R).map (Q.rightUnitor.inv ≫ Functor.whiskerLeft Q η) ≫
                β.hom.app (Q ⋙ tensorTower R t) ≫ (roos R).map (γ Q).inv =
              augmentation R ((roos R).obj Q) t) ∧
          (∀ (Q : Tower R) (p q : Bool) (k : ℤ) (n j : ℕ),
            ((roos R).map (Q.rightUnitor.inv ≫ Functor.whiskerLeft Q η) ≫
                β.hom.app (Q ⋙ tensorTower R t)).f k ≫
                columnCoordinate R (Q ⋙ tensorTower R t) p q k n j =
              if hq : q then 0 else
                coordinate R Q p k n ≫
                  ((strictAugmentation R (Q.obj (op n)) t).app (op j)).f
                    (k - degree p) ≫
                  eqToHom (congrArg (fun a : ℤ ↦
                    (((tensorTower R t).obj (Q.obj (op n))).obj (op j)).X a)
                    (by simp [degree, hq]))) := by
  sorry

end CategoryTheory.SignedDoubleRoos
