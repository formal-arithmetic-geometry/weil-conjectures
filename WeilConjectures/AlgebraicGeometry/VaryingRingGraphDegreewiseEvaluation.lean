/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRingGraphSummand

/-!
# Degreewise evaluation of the varying-ring graph map

The statement is the ordinary, componentwise graph square, refined to strict semilinear
coefficient systems.
Source: Stacks Project, Tag 0F4L, lemma-shriek-into-star-separated-etale
(blueprint: lem-sp-varying-ring-graph-degreewise-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.VaryingRingGraph

namespace AlgebraicGeometry.ProEtale.VaryingRingGraph

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/--
Evaluation at one coefficient ring carries the normalized ordinary varying-ring graph map to
its single-ring graph map: `a⁰ ∘ ev_{T,n}(γ_c) ∘ σ = g_{*,n}(ι) ∘ γ_{c,n}`, for every system,
degreewise for every unbounded cochain complex, and in the homotopy categories (stated
on the composite functors, which absorbs the canonical composition comparisons).
Source: Stacks Project, Tag 0F4L, lemma-shriek-into-star-separated-etale; Zheng 4.10
(blueprint: lem-sp-varying-ring-graph-degreewise-evaluation).

Proof.
1. Put `M = ev_{U,n} N` and call the two maps `A_N`, `B_N`. The unsheafified source of the
   single-ring sum has one summand `M(V,w)` per lift `w : V → U`; by the universal property
   of sheafification it suffices to compare `A_N`, `B_N` on these lift generators.
2. For `L = Σ_e` (resp. `i_!`) the inverse mate `κ = ε_n ∘ L_n(b) ∘ L_n E_U(η)` satisfies
   `f_n^*(κ) ∘ η_n = b ∘ E_U(η)` by naturality and a triangle identity; in section
   coordinates `σ` sends lift generators to lift generators and `ι` open units to open units.
3. On `P = V ×_T Z` with graph `s = (1_V, i ∘ w)` and complement `Q`, `a⁰` is the identity
   on sections; both `A_N` and `B_N` restrict along `s` to the open unit of `m` and to zero
   on `Q`.
4. The graph is clopen, so restriction to the cover `{s(V), Q}` is injective
   (lem-pur-clopen-ringed-module-gluing, arbitrary-ring part); hence `A_N = B_N`, naturally.
5. Apply this to every term of a complex; the additive functors act termwise on chain
   maps and homotopies, so the equality descends to homotopy categories.
-/
theorem varyingRingGraphDegreewiseEvaluation {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e)
    [QuasiCompact c.i] (n : ℕ) :
    (∀ (N : SemilinearProperOpen.Modules C τ U),
      (sumEvaluationInv C τ e n).app N ≫
          (ev C τ T n).map ((graphMap C τ e c).app N) ≫
          ((SemilinearProperOpen.evalPushOrdinary_existsUnique C τ n c.g).choose.inv.app
            ((SemilinearProperOpen.extension C τ c.i).obj N)).app (op 0) =
        (levelGraphMap (C n) e c).app ((ev C τ U n).obj N) ≫
          (StrictTower.moduleDirectImage (C n) c.g).map
            ((openEvaluationInv C τ c.i n).app N)) ∧
    (∀ (K : HomologicalComplex (SemilinearProperOpen.Modules C τ U) (ComplexShape.up ℤ))
      (k : ℤ),
      (sumEvaluationInv C τ e n).app (K.X k) ≫
          (ev C τ T n).map ((graphMap C τ e c).app (K.X k)) ≫
          ((SemilinearProperOpen.evalPushOrdinary_existsUnique C τ n c.g).choose.inv.app
            ((SemilinearProperOpen.extension C τ c.i).obj (K.X k))).app (op 0) =
        (levelGraphMap (C n) e c).app ((ev C τ U n).obj (K.X k)) ≫
          (StrictTower.moduleDirectImage (C n) c.g).map
            ((openEvaluationInv C τ c.i n).app (K.X k))) ∧
    (letI : (levelSum (C n) e).Additive := levelSum_additive (C n) e
    letI : (StrictTower.moduleDirectImage (C n) c.g).Additive :=
      StrictTower.moduleDirectImage_additive (C n) c.g
    NatTrans.mapHomotopyCategory
        ((sumEvaluationInv C τ e n ≫
          Functor.whiskerRight (graphMap C τ e c) (ev C τ T n) ≫
          Functor.whiskerLeft (SemilinearProperOpen.extension C τ c.i)
            (Functor.whiskerRight
              (SemilinearProperOpen.evalPushOrdinary_existsUnique C τ n c.g).choose.inv
              ((evaluation ℕᵒᵖ (StrictTower.Modules (C n) T)).obj (op 0))) :
          ev C τ U n ⋙ levelSum (C n) e ⟶
            SemilinearProperOpen.extension C τ c.i ⋙ ev C τ c.Z n ⋙
              StrictTower.moduleDirectImage (C n) c.g)) (ComplexShape.up ℤ) =
      NatTrans.mapHomotopyCategory
        ((Functor.whiskerLeft (ev C τ U n) (levelGraphMap (C n) e c) ≫
          Functor.whiskerRight (openEvaluationInv C τ c.i n)
            (StrictTower.moduleDirectImage (C n) c.g) :
          ev C τ U n ⋙ levelSum (C n) e ⟶
            SemilinearProperOpen.extension C τ c.i ⋙ ev C τ c.Z n ⋙
              StrictTower.moduleDirectImage (C n) c.g)) (ComplexShape.up ℤ)) := by
  sorry


end AlgebraicGeometry.ProEtale.VaryingRingGraph
