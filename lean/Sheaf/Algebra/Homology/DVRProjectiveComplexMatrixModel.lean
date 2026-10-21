/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Finite matrix coordinates for a bounded projective complex over a DVR

Source: the current blueprint, `sec-six-functors-basics`,
`sk-lem-int-integral-heart-local-model.proof.md`, clause (1); Stacks Tags 05CF
(`algebra.tex`, `lemma-characterize-projective`) and 0AUW(3)
(`more-algebra.tex`, `lemma-dedekind-torsion-free-flat`).
(blueprint: lem-sfb-dvr-projective-complex-matrix-model)

The isomorphism of complexes is expressed by its component linear equivalences and
its differential compatibility. This allows the module carriers and the scalar ring
to live in independent universes. The matrices act on column vectors.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A bounded complex of finite projective modules over a DVR admits finite matrix
coordinates with exactly the same support bounds. The component equivalences and
commutation equation express a strict isomorphism of complexes over the original ring.

Source: the current blueprint, `sec-six-functors-basics`,
`sk-lem-int-integral-heart-local-model.proof.md`, clause (1); Stacks Tags 05CF and
0AUW(3). (blueprint: lem-sfb-dvr-projective-complex-matrix-model)

Proof plan:
1. Split each projective term into a free module using
   `def-weil-pbc-projective-module`. If a nonzero scalar kills an element, its image
   in the free module has every coordinate zero because the DVR is a domain; the
   retraction then kills the original element. Thus each term is torsion-free.
2. Apply `lem-sc-dvr-fg-torsionfree-free` to obtain a finite basis for each term in
   the interval (`def-weil-pbc-free-module`). Enumerate it to get `Fin (n i)` and
   the equivalence `e i`. Outside the interval take rank zero and the equivalence
   with the zero term supplied by the support hypothesis.
3. Define entry `(k,j)` of `D i` to be coordinate `k` of
   `(e (i + 1)).symm (d (e i u_j))`. Expanding a vector in the standard basis proves
   `d (e i x) = e (i + 1) ((D i).mulVec x)`, including empty coordinate sets.
4. The original square-zero relation and injectivity of `e (i + 2)` give
   `D (i + 1) * D i = 0` by evaluation on standard vectors and then coordinates.
5. The matrices therefore define a complex of the coordinate modules. Step 3
   makes the `e i` a chain map. Composing its equality with their inverses shows
   those inverses also commute with the differentials; the two composites are
   identities degreewise. The rank bounds give the same support interval, with
   no change of scalar ring and no passage to a quasi-isomorphic replacement. -/
theorem exists_finite_matrix_model_of_projective_over_dvr
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (a b : ℤ) (hab : a ≤ b) (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i))
    [∀ i : ℤ, Module.Finite R (P.X i)] [∀ i : ℤ, Module.Projective R (P.X i)] :
    ∃ (n : ℤ → ℕ) (e : ∀ i : ℤ, (Fin (n i) → R) ≃ₗ[R] P.X i)
      (D : ∀ i : ℤ, Matrix (Fin (n (i + 1))) (Fin (n i)) R),
      (∀ i : ℤ, i < a ∨ b < i → n i = 0) ∧
      (∀ (i : ℤ) (x : Fin (n i) → R),
        (P.d i (i + 1)).hom (e i x) = e (i + 1) ((D i).mulVec x)) ∧
      (∀ i : ℤ, D (i + 1) * D i = 0) := by
  have _hab := hab
  classical
  have : ∀ i : ℤ, Module.IsTorsionFree R (P.X i) := fun i ↦ by
    obtain ⟨s, hs⟩ := (inferInstance : Module.Projective R (P.X i)).out
    exact Function.Injective.moduleIsTorsionFree s hs.injective s.map_smul
  let n : ℤ → ℕ := fun i ↦ Module.finrank R (P.X i)
  let c := fun i : ℤ ↦ Module.finBasis R (P.X i)
  let e := fun i : ℤ ↦ (c i).equivFun.symm
  let D := fun i : ℤ ↦ LinearMap.toMatrix (c i) (c (i + 1)) (P.d i (i + 1)).hom
  refine ⟨n, e, D, ?_, ?_, ?_⟩
  · intro i hi
    have := ModuleCat.subsingleton_of_isZero (hP i hi)
    exact Module.finrank_eq_zero_of_subsingleton R (P.X i)
  · intro i x
    apply (c (i + 1)).equivFun.injective
    change (c (i + 1)).equivFun ((P.d i (i + 1)).hom ((c i).equivFun.symm x)) =
      (c (i + 1)).equivFun ((c (i + 1)).equivFun.symm ((D i).mulVec x))
    rw [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply]
    simpa only [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using
      ((P.d i (i + 1)).hom.toMatrix_mulVec_repr (c i) (c (i + 1))
        ((c i).equivFun.symm x)).symm
  · intro i
    change LinearMap.toMatrix (c (i + 1)) (c (i + 1 + 1))
        (P.d (i + 1) (i + 1 + 1)).hom *
      LinearMap.toMatrix (c i) (c (i + 1)) (P.d i (i + 1)).hom = 0
    rw [← LinearMap.toMatrix_comp]
    have hz : (P.d (i + 1) (i + 1 + 1)).hom.comp (P.d i (i + 1)).hom = 0 := by
      exact congrArg ModuleCat.Hom.hom (P.d_comp_d i (i + 1) (i + 1 + 1))
    rw [hz, map_zero]

end CochainComplex
