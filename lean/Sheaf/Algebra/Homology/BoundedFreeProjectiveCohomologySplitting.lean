/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Module.Projective

/-!
# Splitting a bounded finite-free complex with projective cohomology

Source: the Weil conjectures blueprint, `main-20261015`, `sec-purity-real-sheaves`,
`sk-p-real-rankone/lem-wf-curve-finite-level-pd.proof.md`, paragraph beginning
“We record the elementary splitting argument needed here”
(blueprint: lem-wf-bounded-free-complex-projective-cohomology-splitting).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A bounded finite-free complex with projective cohomology splits into its cohomology
and identity-differential disks. Source: the Weil conjectures blueprint, `main-20261015`,
`sec-purity-real-sheaves/sk-p-real-rankone/lem-wf-curve-finite-level-pd.proof.md`, paragraph
“We record the elementary splitting argument needed here”
(blueprint: lem-wf-bounded-free-complex-projective-cohomology-splitting).

The finite set `s` contains every degree with nonzero cohomology and every lower degree
of a nonzero disk. The categorical image of `L.d i (i + 1)` is the boundary module
`B^(i+1)`. `HomologicalComplex.double` places its identity in degrees `i,i+1`.
Coproducts here are finite direct sums in additive categories. The derived summands
are the degree-zero cohomology modules shifted by `-i`; the complex summands are
single-term, zero-differential complexes in degree `i`. `Homotopy (𝟙 D) 0` says exactly
that the identity is `dh + hd` for maps of degree `-1`.

Proof: (1) Choose bounds `a,b`, put `Z^i = ker d^i`, `B^i = im d^(i-1)`, and use
image and quotient to obtain the two short exact sequences onto `B^(i+1)` and `H^i`.
(2) Finite-free modules and zero are projective; the lifting characterization of
`def-weil-pbc-projective-module` shows that retracts of projectives are projective.
(3) Descending from `B^(b+1) = 0`, split `L^i -> B^(i+1)` by a section `t_i`.
Then `L^i = Z^i ⊕ B^(i+1)`, so `Z^i` is projective.
(4) Split `Z^i -> H^i` by a section `s_i`; this gives `Z^i = B^i ⊕ H^i` and makes
`B^i` projective, completing the descending induction. Outside the bounds use zero.
(5) The map `(u,h,c) ↦ u + s_i(h) + t_i(c)` identifies
`B^i ⊕ H^i ⊕ B^(i+1)` with `L^i`; its inverse uses `z = x - t_i(p_i(x))` and sends
`x` to `(z - s_i(q_i(z)), q_i(z), p_i(x))`. The differential becomes `(u,h,c) ↦ (c,0,0)`.
(6) These maps assemble to the displayed complex isomorphism with the cohomology
singletons and the boundary disks. Boundedness makes both families finitely supported.
(7) On each disk put the identity as the homotopy from its upper degree to its lower
degree and zero elsewhere. In both nonzero degrees `dh + hd` is the identity.
(8) Projection to the cohomology summands induces the identity on cohomology and is a
quasi-isomorphism. The localization of `def-weil-abstract-derived-category` inverts it;
its additivity and shift compatibility identify the image with the finite sum of
`H^i[-i]`, giving the derived isomorphism. -/
theorem exists_bounded_free_projective_cohomology_splitting
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (L : CochainComplex (ModuleCat.{v} R) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (L.X i))
    (hfree : ∀ i : ℤ, ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R (L.X i)))
    (hprojective : ∀ i : ℤ, Module.Projective R (L.homology i)) :
    ∃ s : Finset ℤ,
      (∀ i : ℤ, i ∉ s →
        IsZero (L.homology i) ∧ IsZero (image (L.d i (i + 1)))) ∧
      Nonempty ((DerivedCategory.Q.obj L) ≅
        ∐ (fun i : s ↦ ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
          (L.homology i.1))⟦-i.1⟧)) ∧
      Nonempty (L ≅
        ((∐ (fun i : s ↦ (HomologicalComplex.single (ModuleCat.{v} R)
            (ComplexShape.up ℤ) i.1).obj (L.homology i.1))) ⨿
          (∐ (fun i : s ↦ HomologicalComplex.double
            (𝟙 (image (L.d i.1 (i.1 + 1))))
            (c := ComplexShape.up ℤ) (i₀ := i.1) (i₁ := i.1 + 1) rfl)))) ∧
      ∀ i : ℤ, Nonempty (Homotopy
        (𝟙 (HomologicalComplex.double (𝟙 (image (L.d i (i + 1))))
          (c := ComplexShape.up ℤ) (i₀ := i) (i₁ := i + 1) rfl)) 0) := sorry

end CochainComplex
