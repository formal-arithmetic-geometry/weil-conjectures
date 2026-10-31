/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CondensedProductBarComparison
public import WeilConjectures.CategoryTheory.CondensedInjectiveBarRows
import WeilConjectures.CategoryTheory.CondensedFreeLinearizationTensor
import WeilConjectures.CategoryTheory.Monoidal.ModuleEqualizerInternalHom

/-! # Coordinates of the product internal bar

Source: latest blueprint, direct-image stability, paragraph (3), formal internal-bar
expansion, steps 1–3 and 5 of the product resolution model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction
namespace CategoryTheory.CondensedBar

variable {A : Ring.{u}} {G H : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- The underived parameter identifications, before choosing any resolution.
Source: paragraph (3), product-model steps 1–3 and 5
(blueprint: lem-sfb-condensed-product-bar-coordinates). -/
structure ProductBarCoordinates (F : InternalFunctions A) (B : ProductBar A.toMon G H) where
  /-- The free-product identification is natural in both parameters and generator normalized. -/
  freeProduct : ∀ P Q : Profinite.{u},
    freeParameter A (Profinite.of (P × Q)) ≅ freeParameter A P ⊗ freeParameter A Q
  /-- On every generalized generator the identification sends [(p,q)] to [p] tensor [q]. -/
  freeProduct_generator : ∀ (P Q S : Profinite.{u}) (p : S ⟶ P) (q : S ⟶ Q),
    ((freeProduct P Q).hom.hom.hom.app (op S))
        (parameterGenerator A (Profinite.of (P × Q)) S
          (ConcreteCategory.ofHom (p.hom.hom.prodMk q.hom.hom))) =
      Profinite.CondensedAction.InternalBar.pureTensor A.toMon _ _ S
        (parameterGenerator A P S p) (parameterGenerator A Q S q)
  /-- Currying is natural in the module variable. -/
  curryIso : ∀ P Q : Profinite.{u},
    F.functor (Profinite.of (P × Q)) ≅ F.functor Q ⋙ F.functor P
  /-- Currying has the specified evaluation on all base changes, not an arbitrary iso. -/
  curry_evaluate : ∀ (P Q S : Profinite.{u}) (M : Modules A)
    (x : sections A ((F.functor (Profinite.of (P × Q))).obj M) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : C(T, P))
    (W : Profinite.{u}) (k : W ⟶ T) (h : C(W, Q)),
    (F.evaluate Q T M
      ((F.evaluate P S ((F.functor Q).obj M)
        (((curryIso P Q).hom.app M).hom.hom.app (op S) x)).val T f g)).val W k h =
      (F.evaluate (Profinite.of (P × Q)) S M x).val W (k ≫ f)
        ((g.comp k.hom.hom).prodMk h)
  /-- Each bidegree is the actual second-variable internal Hom functor. -/
  columnIso : ∀ a b : ℕ,
    B.cochains ⋙ productBarEvaluation A.toMon a b ≅
      forgetAction ⋙ F.functor (Profinite.of ((Fin a → G) × (Fin b → H)))
  /-- The column identification agrees with the normalized represented-section formula. -/
  column_evaluate : ∀ (M : Equivariant A (G × H)) (a b : ℕ) (S : Profinite.{u})
    (x : sections A ((B.cochains ⋙ productBarEvaluation A.toMon a b).obj M) S)
    (T : Profinite.{u}) (f : T ⟶ S)
    (g : Fin a → C(T, G)) (h : Fin b → C(T, H)),
    (F.evaluate (Profinite.of ((Fin a → G) × (Fin b → H))) S M.module
      (((columnIso a b).hom.app M).hom.hom.app (op S) x)).val T f
        ((tupleMap g).prodMk (tupleMap h)) =
      M.module.X.obj.map ((ConcreteCategory.ofHom
        (f.hom.hom.prodMk ((tupleMap g).prodMk (tupleMap h))))).op (B.sections M a b S x)
  /-- The product single-group bar, with all of its specified inhomogeneous operators. -/
  singleBar : BarDiagram (G := G × H) F
  /-- Coordinate reordering is an isomorphism of complete cosimplicial diagrams. -/
  diagonalIso : (B.cochains ⋙ Functor.uncurry ⋙
    (Functor.whiskeringLeft _ _ _).obj (Functor.diag SimplexCategory)) ≅ singleBar.diagram
  /-- The diagonal identification is the coordinate reordering on internal functions. -/
  diagonal_evaluate : ∀ (M : Equivariant A (G × H)) (n : ℕ) (S : Profinite.{u})
    (x : sections A ((B.cochains ⋙ productBarEvaluation A.toMon n n).obj M) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin n → C(T, G × H)),
    (F.evaluate (power (G × H) n) S M.module
      ((((diagonalIso.hom.app M).app (SimplexCategory.mk n) ≫
        (singleBar.term M n).hom).hom.hom.app (op S)) x)).val T f (tupleMap g) =
      M.module.X.obj.map ((ConcreteCategory.ofHom (f.hom.hom.prodMk
        ((tupleMap (fun i ↦ ContinuousMap.fst.comp (g i))).prodMk
          (tupleMap (fun i ↦ ContinuousMap.snd.comp (g i))))))).op (B.sections M n n S x)

/-- The two internal nerves admit the normalized parameter identifications.

Source: latest blueprint direct-image stability, paragraph (3), formal internal-bar
expansion, product-resolution-model steps 1–3 and 5
(blueprint: lem-sfb-condensed-product-bar-coordinates).

Proof:
1. Apply the normalized free-linearization tensor comparison to represented P and Q.
The Yoneda product comparison identifies their product with represented P times Q.
Its inverse sends [(p,q)] to [p] tensor [q], by the generator formula.
2. The closed adjunction applied twice gives currying. On every test module the two
adjunction bijections identify both sides with maps from its tensor with A[P] tensor
A[Q]. Evaluation of the counits gives the successive-evaluation formula, with k then f.
3. Represent the product-function sheaf by M(S times G^a times H^b). Define the two
sets of inhomogeneous faces by substitution and the two coefficient actions. Define
codegeneracies by inserting the identity. These maps are linear and natural in S and M.
Associativity, the action law and the unit law prove the cosimplicial identities.
The two first faces commute since (g,1) and (1,h) commute; all other mixed operators
modify disjoint lists. This gives the functor B on the two simplex categories.
4. The represented-function adjunction gives columnIso. Evaluate after the graph
of f and the parameter tuples to obtain column_evaluate on every base change.
5. Reorder a tuple of pairs into a pair of tuples. The inverse pairs corresponding
coordinates. The first diagonal face acts by (g,h), interior faces multiply both
coordinates, the final face drops both, and degeneracies insert (1,1). This gives
the full cosimplicial diagonalIso and its stated evaluation. These constructions use
empty tuples in degree zero and retain the unnormalized nerve for trivial groups;
empty profinite parameters and the zero module satisfy the same adjunction formulas.
-/
theorem exists_productBarCoordinates (F : InternalFunctions A) :
    ∃ B : ProductBar A.toMon G H, Nonempty (ProductBarCoordinates F B) := by sorry

end CategoryTheory.CondensedBar
