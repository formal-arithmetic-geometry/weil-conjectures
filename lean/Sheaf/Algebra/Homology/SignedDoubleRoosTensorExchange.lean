/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchangeDefinitions
import Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchangeInterchange
import Sheaf.Algebra.Homology.SignedDoubleRoosTensorExchangeTensor

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

/-- Signed double Roos interchange, its tensor exchange and exact augmentation coherence.
All maps use the existing strict shifted cone. The natural isomorphism beta has sign
(-1)^(pq), and gamma preserves the indicated Roos/tensor coordinates. Its normalization
in the derived category is the explicit derivedInterchange above.

Source: blueprint sec-smooth-purity/sk-lem-sp-tower, completeness calculation;
Stacks 014E, 012Z, 03EK and 0941
(blueprint: lem-sp-signed-double-roos-tensor-exchange).

Proof plan:
1. Expand the two products and finite biproducts using their universal properties
(def-weil-category-product, def-sp-abelian). The commuting transitions give AB=BA.
2. In row coordinates (a,b,c,h), the differential is
(da,-db-Ba,-dc-Aa,dh+Bc-Ab), by def-weil-strict-roos-model.
3. The map (a,b,c,h) to (a,c,b,-h) commutes with this differential and is its own
inverse after reversing indices. This gives beta with exactly the four stated signs.
4. Product maps commute with permutation and negation, proving naturality. The two
zero-degree evaluations retain (a,b) and (a,c), so both evaluation squares commute.
5. Localize beta and conjugate by the normalized comparisons of
lem-weil-strict-roos-comparison. This is derivedInterchange; the normalization
preserves both evaluation squares and strict augmentations.
6. Only Koszul degrees -1 and 0 occur. The unit tensor isomorphism, the sheafification
universal property (def-weil-presheaf-modules-sheafification) and product/biproduct
interchange give the two coordinate identifications gamma. No assertion that an
arbitrary tensor preserves products is used (def-pur-sheaf-tensor-product).
7. In intrinsic degree a and Roos degree p the three differential coefficients are
(-1)^p, (-1)^(a+p), and -(1-s). They agree on both sides, with the total tensor of
def-pc-tensor-complex-sheaves. The same component tests give naturality, compatibility
with Koszul transitions, inclusions and evaluations.
8. The unit has only j-Roos degree zero (def-pur-principal-koszul-quotient-towers).
Before beta its coordinates are (v tensor 1,0,u tensor 1,0); afterwards they are
(v tensor 1,u tensor 1,0,0). Applying Roos to gamma inverse is exactly the unit of H.
All computations use only four Roos coordinates and two Koszul degrees; neither
boundedness, torsion, regularity nor a normalization assumption on Q is required. -/
theorem signed_double_roos_tensor_exchange
    [HasExactLimitsOfShape (Discrete ℕ) (Modules R)] :
    ∃ β : rows R ≅ columns R,
      (∀ (X : ℕᵒᵖ ⥤ Tower R) (p q : Bool) (k : ℤ) (n j : ℕ),
        (β.hom.app X).f k ≫ columnCoordinate R X p q k n j =
          if p && q then -rowCoordinate R X p q k n j
          else rowCoordinate R X p q k n j) ∧
      (∀ (X : ℕᵒᵖ ⥤ Tower R) (n : ℕ),
        β.hom.app X ≫ (roos R).map (innerEvaluation R X.flip n) =
          evaluation R (X ⋙ roos R) n) ∧
      (∀ (X : ℕᵒᵖ ⥤ Tower R) (j : ℕ),
        β.hom.app X ≫ evaluation R (X.flip ⋙ roos R) j =
          (roos R).map (innerEvaluation R X j)) ∧
      (∀ [HasDerivedCategory.{w} (Modules R)]
          (X : ℕᵒᵖ ⥤ Tower R) (Dnj Djn : DerivedCategory.{w} (Modules R))
          (ρnj : DerivedCategory.Q.obj ((rows R).obj X) ≅ Dnj)
          (ρjn : DerivedCategory.Q.obj ((columns R).obj X) ≅ Djn),
        ∃ δ : Dnj ≅ Djn,
          ρnj.hom ≫ δ.hom = DerivedCategory.Q.map (β.hom.app X) ≫ ρjn.hom) ∧
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
  obtain ⟨β, hcoord, hn, hj⟩ := signed_double_roos_interchange_core R
  refine ⟨β, hcoord, hn, hj, ?_, signed_double_roos_tensor_core R β hcoord⟩
  intro _ X Dnj Djn ρnj ρjn
  refine ⟨derivedInterchange R X (β.app X) ρnj ρjn, ?_⟩
  simp only [derivedInterchange, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.hom_inv_id_assoc]

end CategoryTheory.SignedDoubleRoos
