/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.Paper.PbcRoosTriangle
public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# The proper base change rectangle after sequential derived inverse limit

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1346;
Stacks Project, Tag 08TC (blueprint: lem-weil-pbc-rectangle-derived-limit).

The four derived strict towers and their commuting rectangle are the inputs supplied
by lem-weil-pbc-tower-compatibility. The derived-limit functor is fixed together with
its natural Roos triangle. Index n denotes positive coefficient level n+1.

## Main definitions and statements

* `pbcRoosProjection`: the first Roos arrow followed by a product projection.
* `pbcRectangleDerivedLimit`: the rectangle equality and its three component equalities.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The projection to level n+1 is exactly the first Roos arrow followed by the
corresponding derived-product projection. No evaluation of a limit morphism is used.
Source: blueprint order 1346; Stacks 08TC
(blueprint: lem-weil-pbc-rectangle-derived-limit). -/
def pbcRoosProjection
    (T : Scheme.{u}) {R : Type u} [CommRing R] (d : Scheme.AdicCoefficientDatum R)
    (F : DerivedCategory (Scheme.CompletedAdicTowers T d) ⥤
      DerivedCategory (Scheme.CompletedAdicModules T d))
    (p : F ⟶ pbcTowerProduct T d)
    (M : DerivedCategory (Scheme.CompletedAdicTowers T d)) (n : ℕ) :
    F.obj M ⟶ ((pbcDerivedEvaluation T d).obj M).obj (op n) :=
  p.app M ≫ Pi.π (fun k : ℕ ↦ ((pbcDerivedEvaluation T d).obj M).obj (op k)) n

/-- Applying the fixed triangulated derived-limit functor to the four compatible
corner towers preserves their rectangle, including the precise component formula.
The hypothesis hrectangle is the derived-tower equality supplied by
lem-weil-pbc-tower-compatibility, before taking any evaluations. The transformations
p and δ are the natural Roos triangle of prop-weil-pbc-roos-triangle for the chosen
functor of prop-weil-pbc-rlim-functoriality.

Source: blueprint order 1346; Stacks 08TC
(blueprint: lem-weil-pbc-rectangle-derived-limit).

Proof, following the two steps of the node:
1. Apply F to hrectangle. Preservation of composition gives
   F(h) ≫ F(v') = F(v) ≫ F(h') in the derived module category itself.
2. Naturality of p says F(a) ≫ p_N = p_M ≫ (R product)(a). Composing with
   the n-th product projection and using Pi.map_π gives
   F(a) ≫ pr_N,n = pr_M,n ≫ ev_n(a). Apply this first to v' and then h,
   and first to h' and then v. Finally evaluate hrectangle at n to identify
   the two finite-level composites. These are arrows from F(A) to D_n;
   equality of all components is never used to infer equality of limit arrows. -/
theorem pbcRectangleDerivedLimit
    (T : Scheme.{u}) {R : Type u} [CommRing R] (d : Scheme.AdicCoefficientDatum R)
    (A B C D : DerivedCategory (Scheme.CompletedAdicTowers T d))
    (h : A ⟶ B) (v : A ⟶ C) (h' : C ⟶ D) (v' : B ⟶ D)
    (hrectangle : h ≫ v' = v ≫ h')
    (F : DerivedCategory (Scheme.CompletedAdicTowers T d) ⥤
      DerivedCategory (Scheme.CompletedAdicModules T d))
    [F.CommShift ℤ] [F.IsTriangulated]
    (p : F ⟶ pbcTowerProduct T d)
    (δ : pbcTowerProduct T d ⟶ F ⋙
      shiftFunctor (DerivedCategory (Scheme.CompletedAdicModules T d)) (1 : ℤ))
    (_hRoos : ∀ M : DerivedCategory (Scheme.CompletedAdicTowers T d),
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ ((pbcDerivedEvaluation T d).obj M).map
          (homOfLE (Nat.le_succ n)).op)
        (F.obj M) (p.app M) (δ.app M)) :
    (F.map h ≫ F.map v' = F.map v ≫ F.map h') ∧
      ∀ n : ℕ,
        ((F.map h ≫ F.map v') ≫ pbcRoosProjection T d F p D n =
          pbcRoosProjection T d F p A n ≫
            ((pbcDerivedEvaluation T d).map h).app (op n) ≫
            ((pbcDerivedEvaluation T d).map v').app (op n)) ∧
        (pbcRoosProjection T d F p A n ≫
            ((pbcDerivedEvaluation T d).map h).app (op n) ≫
            ((pbcDerivedEvaluation T d).map v').app (op n) =
          pbcRoosProjection T d F p A n ≫
            ((pbcDerivedEvaluation T d).map v).app (op n) ≫
            ((pbcDerivedEvaluation T d).map h').app (op n)) ∧
        (pbcRoosProjection T d F p A n ≫
            ((pbcDerivedEvaluation T d).map v).app (op n) ≫
            ((pbcDerivedEvaluation T d).map h').app (op n) =
          (F.map v ≫ F.map h') ≫ pbcRoosProjection T d F p D n) := by
  have hprojection {M N : DerivedCategory (Scheme.CompletedAdicTowers T d)}
      (f : M ⟶ N) (n : ℕ) :
      F.map f ≫ pbcRoosProjection T d F p N n =
        pbcRoosProjection T d F p M n ≫
          ((pbcDerivedEvaluation T d).map f).app (op n) := by
    simpa only [pbcRoosProjection, pbcTowerProduct, Category.assoc, Pi.map_π] using
      congrArg (fun k ↦ k ≫
        Pi.π (fun k : ℕ ↦ ((pbcDerivedEvaluation T d).obj N).obj (op k)) n)
        (p.naturality f)
  constructor
  · simpa only [Functor.map_comp] using congrArg F.map hrectangle
  · intro n
    have heval :
        ((pbcDerivedEvaluation T d).map h).app (op n) ≫
            ((pbcDerivedEvaluation T d).map v').app (op n) =
          ((pbcDerivedEvaluation T d).map v).app (op n) ≫
            ((pbcDerivedEvaluation T d).map h').app (op n) := by
      simpa only [Functor.map_comp, NatTrans.comp_app] using
        congrArg (fun f ↦ ((pbcDerivedEvaluation T d).map f).app (op n)) hrectangle
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Functor.map_comp, NatTrans.comp_app, Category.assoc] using
        hprojection (h ≫ v') n
    · exact congrArg (fun f ↦ pbcRoosProjection T d F p A n ≫ f) heval
    · simpa only [Functor.map_comp, NatTrans.comp_app, Category.assoc] using
        (hprojection (v ≫ h') n).symm

end AlgebraicGeometry.ProEtale
