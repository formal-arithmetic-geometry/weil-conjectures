/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Reflection
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Rational root directions and the weight plus central lattice embedding

Source: Milne, Algebraic Groups (2017), Appendix C.29, C.34--C.35, C.41--C.44,
pp. 614--618; Exercise 21-4, p. 461
(blueprint: lem-sfb-root-datum-lattice-embedding).

The helper constructions name the rational extensions, subspaces, lattices and canonical
embedding occurring in the statement. Tensor symmetry identifies `ℚ ⊗[ℤ] M` with `M ⊗[ℤ] ℚ`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace RootDatumLattice

variable {M : Type u} [AddCommGroup M]

/-- Rational extension of an integral coroot, by the tensor universal property.
Source: Milne C.29 (blueprint: lem-sfb-root-datum-lattice-embedding). -/
noncomputable def rationalCoroot (c : M →ₗ[ℤ] ℤ) : (ℚ ⊗[ℤ] M) →ₗ[ℚ] ℚ :=
  ((Int.castAddHom ℚ).toIntLinearMap.comp c).liftBaseChange ℚ

/-- Rational root span in the rationalized character lattice.
Source: Milne C.29 (blueprint: lem-sfb-root-datum-lattice-embedding). -/
def rootSpan (R : Set M) : Submodule ℚ (ℚ ⊗[ℤ] M) :=
  Submodule.span ℚ ((TensorProduct.mk ℤ ℚ M 1) '' R)

/-- A root regarded as an element of its rational span.
Source: Milne C.29 (blueprint: lem-sfb-root-datum-lattice-embedding). -/
def root (R : Set M) (a : R) : rootSpan R :=
  ⟨TensorProduct.mk ℤ ℚ M 1 a, Submodule.subset_span ⟨a, a.property, rfl⟩⟩

/-- The rational coroot restricted to the root span.
Source: Milne C.29 (blueprint: lem-sfb-root-datum-lattice-embedding). -/
noncomputable def coroot (R : Set M) (c : R → M →ₗ[ℤ] ℤ) (a : R) :
    rootSpan R →ₗ[ℚ] ℚ :=
  (rationalCoroot (c a)).comp (rootSpan R).subtype

/-- The common annihilator of the rationally extended coroots.
Source: Milne C.42--C.44 (blueprint: lem-sfb-root-datum-lattice-embedding). -/
noncomputable def centralSpace (R : Set M) (c : R → M →ₗ[ℤ] ℤ) :
    Submodule ℚ (ℚ ⊗[ℤ] M) :=
  ⨅ a : R, (rationalCoroot (c a)).ker

/-- The weight lattice consists of vectors taking integral values under every coroot.
Source: Milne C.26 and C.35 (blueprint: lem-sfb-root-datum-lattice-embedding). -/
noncomputable def weightLattice (R : Set M) (c : R → M →ₗ[ℤ] ℤ) :
    Submodule ℤ (rootSpan R) :=
  ⨅ a : R, (LinearMap.range (Int.castAddHom ℚ).toIntLinearMap).comap
    ((coroot R c a).restrictScalars ℤ)

/-- The integral root lattice in the rational root span.
Source: Milne C.26 and C.35 (blueprint: lem-sfb-root-datum-lattice-embedding). -/
def rootLattice (R : Set M) : Submodule ℤ (rootSpan R) :=
  Submodule.span ℤ (Set.range (root R))

/-- The central lattice is the actual image of the original lattice under central projection.
Source: Milne C.43 and Exercise 21-4
(blueprint: lem-sfb-root-datum-lattice-embedding). -/
noncomputable def centralLattice (R : Set M) (c : R → M →ₗ[ℤ] ℤ)
    (h : IsCompl (rootSpan R) (centralSpace R c)) : Submodule ℤ (centralSpace R c) :=
  LinearMap.range (((centralSpace R c).projectionOnto (rootSpan R) h.symm).restrictScalars ℤ
    ∘ₗ TensorProduct.mk ℤ ℚ M 1)

/-- The canonical pair of projections, with their codomains restricted to the two lattices.
Source: Milne C.35, C.43 and Exercise 21-4
(blueprint: lem-sfb-root-datum-lattice-embedding). -/
noncomputable def embedding (R : Set M) (c : R → M →ₗ[ℤ] ℤ)
    (h : IsCompl (rootSpan R) (centralSpace R c))
    (hp : ∀ m : M, (rootSpan R).projectionOnto (centralSpace R c) h
      (TensorProduct.mk ℤ ℚ M 1 m) ∈ weightLattice R c) :
    M →ₗ[ℤ] (weightLattice R c × centralLattice R c h) :=
  (LinearMap.codRestrict (weightLattice R c)
    (((rootSpan R).projectionOnto (centralSpace R c) h).restrictScalars ℤ
      ∘ₗ TensorProduct.mk ℤ ℚ M 1) hp).prod
    (((centralSpace R c).projectionOnto (rootSpan R) h.symm).restrictScalars ℤ
      ∘ₗ TensorProduct.mk ℤ ℚ M 1).rangeRestrict

/-- The rational root/central decomposition and finite-index weight-lattice embedding.
Source: Milne C.29, C.34--C.35, C.41--C.44, pp. 614--618; Exercise 21-4, p. 461
(blueprint: lem-sfb-root-datum-lattice-embedding).

Proof plan:
1. Choose a finite integral basis. Its tensor coordinates identify the rationalization with
   a rational coordinate space and show that the integral lattice injects. Extend each coroot
   rationally; normalization makes its reflection involutive and sends its root to its negative.
2. Average the coordinate dot product over the finite reflection group. The resulting rational
   symmetric form is positive definite and invariant. Invariance under a root reflection gives
   c_a(x) = 2 B(x,a) / B(a,a).
3. Consequently the common coroot kernel is the orthogonal complement of the root span.
   The Gram matrix of a rational root basis is invertible, giving complementary subspaces and
   the two canonical rational projections.
4. Restrict the given axioms to the root span. The form identifies the dual space with it,
   so the coroots span its dual. Apply `Module.Dual.eq_of_preReflection_mapsTo`
   (lem-sfb-finite-spanning-reflection-uniqueness) to prove uniqueness of each coroot.
5. Evaluation on the coroots embeds the weight lattice into the finite product of copies of
   ℤ. Apply `Submodule.basisOfPid` (lem-weil-subgroup-finite-free-abelian-group-free).
   Roots belong to the weight lattice. Clearing denominators shows its integral basis is a
   rational basis, so its rank is the dimension of the root span.
6. Clear the denominators of that basis in a root basis. A positive integer D then sends
   the weight lattice into the root lattice. Reducing basis coefficients modulo D proves
   the quotient finite, including D = 1 for empty bases.
7. The central image is generated by the projected integral basis and is torsion-free.
   Apply `Module.basisOfFiniteTypeTorsionFree'` (lem-trf-fg-torsionfree-group-free).
   Clearing denominators shows that its rank is the central dimension. Every projected
   root component has integral coroot evaluations, since its central component is annihilated.
8. Summing the two projections recovers the original element, so the canonical pair is injective.
   Clear denominators of bases of the weight and central lattices in the original basis.
   A positive multiple of their product lies in the image. Reducing coefficients modulo that
   integer proves the cokernel finite.
9. A root has projections itself and zero. Coroot evaluations ignore the central component.
   For empty roots the root span and weight lattice are zero, the central space is the entire
   rationalization, and the embedding is (0,id). Zero rank gives only empty bases and trivial
   quotients. Thus neither nonempty roots nor positive rank is assumed. -/
theorem lattice_embedding (M : Type u) [AddCommGroup M] [Module.Free ℤ M]
    [Module.Finite ℤ M] (R : Set M) (hR : R.Finite) (hzero : (0 : M) ∉ R)
    (c : R → M →ₗ[ℤ] ℤ) (hc : Function.Injective c)
    (hnorm : ∀ a : R, c a a = 2)
    (hperm : ∀ a : R, Set.BijOn (Module.preReflection (a : M) (c a)) R R)
    (hW : Finite (Subgroup.closure (Set.range
      (fun a : R ↦ Module.reflection (hnorm a)))))
    (hred : ∀ a : R,
      ((ℚ ∙ (TensorProduct.mk ℤ ℚ M 1 a) : Submodule ℚ (ℚ ⊗[ℤ] M)) : Set _)
        ∩ ((TensorProduct.mk ℤ ℚ M 1) '' R) =
          {TensorProduct.mk ℤ ℚ M 1 a, -(TensorProduct.mk ℤ ℚ M 1 a)}) :
    Submodule.span ℚ (Set.range (root R)) = ⊤ ∧
    (∀ a : R, coroot R c a (root R a) = 2) ∧
    (∀ a : R, Set.BijOn (Module.preReflection (root R a) (coroot R c a))
      (Set.range (root R)) (Set.range (root R))) ∧
    (∀ a b : R, ∃ n : ℤ, coroot R c a (root R b) = (n : ℚ)) ∧
    (∀ a : R, ((ℚ ∙ root R a : Submodule ℚ (rootSpan R)) : Set _)
      ∩ Set.range (root R) = {root R a, -(root R a)}) ∧
    Submodule.span ℚ (Set.range (coroot R c)) = ⊤ ∧
    (∀ (a : R) (f : rootSpan R →ₗ[ℚ] ℚ), f (root R a) = 2 →
      Set.MapsTo (Module.preReflection (root R a) f)
        (Set.range (root R)) (Set.range (root R)) → f = coroot R c a) ∧
    Nonempty (Module.Basis (Fin (Module.finrank ℚ (rootSpan R))) ℤ (weightLattice R c)) ∧
    rootLattice R ≤ weightLattice R c ∧
    Finite ((weightLattice R c) ⧸ (rootLattice R).comap (weightLattice R c).subtype) ∧
    ∃ h : IsCompl (rootSpan R) (centralSpace R c),
      Nonempty (Module.Basis (Fin (Module.finrank ℚ (centralSpace R c))) ℤ
        (centralLattice R c h)) ∧
      ∃ hp : ∀ m : M, (rootSpan R).projectionOnto (centralSpace R c) h
          (TensorProduct.mk ℤ ℚ M 1 m) ∈ weightLattice R c,
        Function.Injective (embedding R c h hp) ∧
        Finite (((weightLattice R c) × centralLattice R c h) ⧸
          LinearMap.range (embedding R c h hp)) ∧
        (∀ a : R, (((embedding R c h hp a).1 : rootSpan R) = root R a) ∧
          (embedding R c h hp a).2 = 0) ∧
        (∀ (a : R) (m : M), (c a m : ℚ) = coroot R c a
          ((rootSpan R).projectionOnto (centralSpace R c) h
            (TensorProduct.mk ℤ ℚ M 1 m))) := by
  sorry

end RootDatumLattice
