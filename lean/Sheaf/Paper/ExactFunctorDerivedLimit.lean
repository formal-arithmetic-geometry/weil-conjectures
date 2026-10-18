/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.SequentialDerivedInverseLimit
public import Sheaf.Paper.PbcDerivedProductRepresentation
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Sheaf.Paper.PbcRoosTriangle
import Sheaf.Paper.CompletedDerivedInverseLimit

/-! # Exact functors and sequential derived limits

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc,
lem-cbc-exact-functor-rlim, order 1586; Stacks Tags 08TC, 014V, 0145 and 014A
(blueprint: lem-cbc-exact-functor-rlim).

## Main declarations

* `CategoryTheory.roosProductComparisonIso`: the canonical product comparison,
  transported along the supplied transition-compatible evaluation isomorphism.
* `AlgebraicGeometry.ProEtale.exactFunctor_isDerivedLimit`: the image Roos triangle,
  existence of a compatible comparison, and invertibility of every such comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v u' v' t s

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The canonical product comparison after identifying the evaluated image tower.
Both the map and its inverse are determined by the product universal property and
by the supplied diagram isomorphism; no cone comparison is chosen here.
Source: blueprint lem-cbc-exact-functor-rlim, product comparison and evaluation clause;
Stacks Tag 08TC (blueprint: lem-cbc-exact-functor-rlim). -/
def roosProductComparisonIso
    {C : Type u} [Category.{v} C] [HasCountableProducts C]
    {D : Type u'} [Category.{v'} D] [HasCountableProducts D]
    (F : C ⥤ D) (hprod : ∀ K : ℕ → C, IsIso (piComparison F K))
    (K : ℕᵒᵖ ⥤ C) (N : ℕᵒᵖ ⥤ D) (e : N ≅ K ⋙ F) :
    F.obj (∏ᶜ (fun n : ℕ ↦ K.obj (op n))) ≅ ∏ᶜ (fun n : ℕ ↦ N.obj (op n)) :=
  letI := hprod (fun n : ℕ ↦ K.obj (op n))
  asIso (piComparison F (fun n : ℕ ↦ K.obj (op n))) ≪≫
    Pi.mapIso (fun n : ℕ ↦ e.symm.app (op n))

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- An exact additive functor preserving countable products sends the specified
Roos triangle to the image tower's Roos triangle. There exists a triangle
comparison with any specified target Roos triangle, and every comparison
satisfying the two displayed equations is invertible.

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc,
lem-cbc-exact-functor-rlim, order 1586; Stacks Tags 08TC, 014V, 0145, 014A and 0H9J
(blueprint: lem-cbc-exact-functor-rlim).

Proof:
1. Evaluate the two strict derived towers using def-weil-pbc-derived-inverse-limit.
   The natural isomorphism towerCompat identifies their evaluations and respects
   every transition. The hypotheses hL and hL' are the chosen triangles of
   prop-weil-pbc-roos-triangle.
2. The canonical product comparison has projection F(pr_n). Applying each target
   projection, naturality of towerCompat gives phi F(s) = s' phi. Additivity gives
   phi F(1-s) = (1-s') phi, by def-weil-tower-transition-endomorphism and
   def-weil-category-product.
3. By def-weil-triangulated-category, F sends the source triangle to a distinguished
   triangle with connecting map F(delta) followed by xi_L. Transport both product
   vertices through the product isomorphism. Its middle map is the target 1-s, so
   def-weil-derived-limit gives the displayed image Roos triangle and derived-limit
   property.
4. Rotate this triangle and the target triangle. TR3 completes the identity maps
   on their two product vertices to u : F(L)[1] -> L'[1]. Unshift u to c. Its two
   squares give c followed by p' = F(p) followed by phi and
   F(delta) followed by xi_L and c[1] = phi followed by delta'. This proves existence
   without selecting a unique cone comparison (Stacks 0H9J).
5. For any c satisfying these equations, the product calculation in step 2 gives
   the remaining square. The triangle morphism has two invertible product components;
   lem-sf-triangle-morphism-iso makes c invertible. In particular the existing c
   gives F(L) isomorphic to L', compatibly with these triangles.
-/
theorem exactFunctor_isDerivedLimit
    (T : Scheme.{t}) (S : Scheme.{s})
    {A : Type t} [CommRing A] {B : Type s} [CommRing B]
    (dT : AdicCoefficientDatum A) (dS : AdicCoefficientDatum B)
    (F : DerivedCategory (CompletedAdicModules T dT) ⥤
      DerivedCategory (CompletedAdicModules S dS))
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (towerF : DerivedCategory (CompletedAdicTowers T dT) ⥤
      DerivedCategory (CompletedAdicTowers S dS))
    (towerCompat : towerF ⋙ adicDerivedTowerEvaluation S dS ≅
      adicDerivedTowerEvaluation T dT ⋙
        (Functor.whiskeringRight ℕᵒᵖ (DerivedCategory (CompletedAdicModules T dT))
          (DerivedCategory (CompletedAdicModules S dS))).obj F)
    (hprod : ∀ K : ℕ → DerivedCategory (CompletedAdicModules T dT),
      IsIso (piComparison F K))
    (M : DerivedCategory (CompletedAdicTowers T dT))
    (L : DerivedCategory (CompletedAdicModules T dT))
    (p : L ⟶ ∏ᶜ (fun n : ℕ ↦ ((adicDerivedTowerEvaluation T dT).obj M).obj (op n)))
    (δ : (∏ᶜ (fun n : ℕ ↦ ((adicDerivedTowerEvaluation T dT).obj M).obj (op n))) ⟶ L⟦(1 : ℤ)⟧)
    (hL : IsDerivedLimitTriangle (fun n : ℕ ↦ ((adicDerivedTowerEvaluation T dT).obj M).map
        (homOfLE (Nat.le_succ n)).op) L p δ)
    (L' : DerivedCategory (CompletedAdicModules S dS))
    (p' : L' ⟶ ∏ᶜ (fun n : ℕ ↦ ((adicDerivedTowerEvaluation S dS).obj (towerF.obj M)).obj (op n)))
    (δ' : (∏ᶜ (fun n : ℕ ↦ ((adicDerivedTowerEvaluation S dS).obj (towerF.obj M)).obj (op n))) ⟶
      L'⟦(1 : ℤ)⟧)
    (hL' : IsDerivedLimitTriangle (fun n : ℕ ↦ ((adicDerivedTowerEvaluation S dS).obj
      (towerF.obj M)).map
        (homOfLE (Nat.le_succ n)).op) L' p' δ') :
    IsDerivedLimitTriangle (fun n : ℕ ↦ ((adicDerivedTowerEvaluation S dS).obj (towerF.obj M)).map
        (homOfLE (Nat.le_succ n)).op)
      (F.obj L) (F.map p ≫ (roosProductComparisonIso F hprod
        ((adicDerivedTowerEvaluation T dT).obj M) ((adicDerivedTowerEvaluation S dS).obj
          (towerF.obj M)) (towerCompat.app M)).hom)
      ((roosProductComparisonIso F hprod
        ((adicDerivedTowerEvaluation T dT).obj M) ((adicDerivedTowerEvaluation S dS).obj
          (towerF.obj M)) (towerCompat.app M)).inv ≫
        F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L) ∧
    IsAdicSequentialDerivedLimit S dS (towerF.obj M) (F.obj L) ∧
    (∃ c : F.obj L ⟶ L',
      c ≫ p' = F.map p ≫ (roosProductComparisonIso F hprod
        ((adicDerivedTowerEvaluation T dT).obj M) ((adicDerivedTowerEvaluation S dS).obj
          (towerF.obj M)) (towerCompat.app M)).hom ∧
      F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L ≫ c⟦(1 : ℤ)⟧' =
        (roosProductComparisonIso F hprod
        ((adicDerivedTowerEvaluation T dT).obj M) ((adicDerivedTowerEvaluation S dS).obj
          (towerF.obj M)) (towerCompat.app M)).hom ≫ δ') ∧
    (∀ c : F.obj L ⟶ L',
      c ≫ p' = F.map p ≫ (roosProductComparisonIso F hprod
        ((adicDerivedTowerEvaluation T dT).obj M) ((adicDerivedTowerEvaluation S dS).obj
          (towerF.obj M)) (towerCompat.app M)).hom →
      F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L ≫ c⟦(1 : ℤ)⟧' =
        (roosProductComparisonIso F hprod
        ((adicDerivedTowerEvaluation T dT).obj M) ((adicDerivedTowerEvaluation S dS).obj
          (towerF.obj M)) (towerCompat.app M)).hom ≫ δ' →
      IsIso c) := by
  sorry

end AlgebraicGeometry.ProEtale
