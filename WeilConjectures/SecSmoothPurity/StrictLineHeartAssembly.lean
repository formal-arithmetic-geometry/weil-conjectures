/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.SecSmoothPurity.ScalarExtensionFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Strict tower assembly from compatible shifted line maps

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/
  sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md`,
paragraph (1), strict-heart assembly of compatible finite orientation maps
(blueprint: lem-sp-strict-line-heart-assembly).

The level notation below is the abstract categorical presentation of the strict
coefficient tower supplied by `sk-def-sp-coefficient-towers` and
`det-sp-coefficient-towers-abelian`: `eval n` is its exact level evaluation,
`red h` its canonical derived reduction, and `tensor h` the actual derived scalar
reduction.  Writing all levels in one displayed abelian category keeps the
statement independent of universe lifts; the coefficient-tower specialization
uses the corresponding level category at each `n`.  The prescribed maps are
written after applying the common shift `[-s]`, canonically equivalent to
`L_n[0][s] ≅ V_n` under `(K[1])^r = K^{r+1}`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/- STATEMENT-DISPUTED: the abstract signature omits the conservativity and
  exactness/naturality data needed to pass from the evaluated complexes back to
  the tower.  For example, take C = D = ModuleCat ℤ, let every `eval n` be the
  zero functor, take `s = 0`, `L = ℤ`, `V` to be a nonzero object concentrated
  in degree 1, and set every `L₀ n = 0`.  The `levelIso`, `a`, `hV`, `ordinaryRed`,
  `hRed`, `red`, and `ha` hypotheses are then witnessed by zero maps and
  identity maps, while the conclusion would give an isomorphism from the zero
  degree-zero object to the nonzero shifted object.  The concrete tower
  theorem formerly used by this route supplied exact level evaluations and
  joint conservativity; those hypotheses are absent here. -/

/-- Strict-heart assembly from compatible shifted line maps.

`C` is the Grothendieck abelian tower category, `D` is its common displayed
level category, `eval`, `tensor`, and `red` are the exact evaluations, actual
scalar reductions, and canonical derived reduction squares of
`det-sp-coefficient-towers-abelian`.  `L₀ n` is the level of the strict line and
`line` expresses that it is locally free of rank one.  `ordinaryRed` and `hRed`
retain the ordinary scalar reductions and their invertibility.  `hV` gives the
levelwise concentration in degree `-s`; `a` and `ha` are the prescribed
isomorphisms and their compatibility for every `m ≤ n`.

The conclusion takes `W = H^0(V[-s])`, gives the canonical single-complex
identification, unique compatible level maps and their strict-tower
isomorphism, and shifts back to an isomorphism with `V`.

Proof: exact evaluations jointly detect the cohomological bounds, so the
levelwise hypotheses put `V[-s]` in the heart.  The concentrated-single theorem
identifies it with the single complex on its zeroth cohomology.  Full
faithfulness of the single embedding lifts each compatible derived level map
uniquely to a sheaf map; lifting inverses proves that they are isomorphisms.
Naturality of `red` and `ha` gives the strict-tower compatibility, and shifting
back gives the final isomorphism. -/
theorem strictLineHeartAssembly
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type u} [Category.{v} D] [Abelian D] [HasDerivedCategory.{w} D]
    (L : C) (V : DerivedCategory C) (s : ℤ)
    (L₀ : ℕ → D)
    (line : D → Prop)
    (hL : ∀ n : ℕ, line (L₀ n))
    (eval : ∀ n : ℕ, DerivedCategory C ⥤ DerivedCategory D)
    (tensor : ∀ {m n : ℕ}, m ≤ n → DerivedCategory D ⥤ DerivedCategory D)
    (ordinaryRed : ∀ {m n : ℕ} (h : m ≤ n),
      (tensor h).obj ((DerivedCategory.singleFunctor D 0).obj (L₀ n)) ⟶
        (DerivedCategory.singleFunctor D 0).obj (L₀ m))
    (hRed : ∀ {m n : ℕ} (h : m ≤ n), IsIso (ordinaryRed h))
    (red : ∀ {m n : ℕ} (h : m ≤ n),
      eval n ⋙ tensor h ⟶ eval m)
    (hV : ∀ n : ℕ, ∀ q : ℤ, q ≠ -s →
      IsZero ((DerivedCategory.homologyFunctor D q).obj ((eval n).obj V)))
    (levelIso : ∀ n : ℕ,
      (eval n).obj ((DerivedCategory.singleFunctor C 0).obj L) ≅
        (DerivedCategory.singleFunctor D 0).obj (L₀ n))
    (a : ∀ n : ℕ,
      (eval n).obj ((DerivedCategory.singleFunctor C 0).obj L) ≅
        (eval n).obj ((shiftFunctor (DerivedCategory C) (-s)).obj V))
    (ha : ∀ {m n : ℕ} (h : m ≤ n),
      (tensor h).map (a n).hom ≫ (red h).app ((shiftFunctor (DerivedCategory C) (-s)).obj V) =
        (red h).app ((DerivedCategory.singleFunctor C 0).obj L) ≫ (a m).hom) :
    let V' := (shiftFunctor (DerivedCategory C) (-s)).obj V
    let W := (DerivedCategory.homologyFunctor C 0).obj V'
    ∃ (ε : (DerivedCategory.singleFunctor C 0).obj W ≅ V')
      (α : L ≅ W),
      (∀ n : ℕ,
        (eval n).map ((DerivedCategory.singleFunctor C 0).map α.hom) ≫
            (eval n).map ε.hom = (a n).hom) ∧
      (∀ β : L ≅ W,
        (∀ n : ℕ,
          (eval n).map ((DerivedCategory.singleFunctor C 0).map β.hom) ≫
              (eval n).map ε.hom = (a n).hom) → β = α) ∧
      Nonempty ((shiftFunctor (DerivedCategory C) s).obj
        ((DerivedCategory.singleFunctor C 0).obj L) ≅ V) := by
  sorry

end AlgebraicGeometry.ProEtale
