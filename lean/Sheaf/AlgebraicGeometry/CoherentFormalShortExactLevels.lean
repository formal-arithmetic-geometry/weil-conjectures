/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Levels of a short exact sequence of coherent formal modules

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0CYV, remarks (a) and (b),
and proof of Lemma 087X (blueprint: lem-weil-pbc-coherent-formal-short-exact-levels).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A short exact sequence in Coh(X,I) is right exact at every positive level, and
its first term at each level is a quotient of the kernel of a later component.
Here `op n` denotes positive level `n + 1`. No componentwise monomorphism is asserted.

Source: Stacks, proof of Lemma 0CYV, first paragraph, remarks (a) and (b), referring
back to the proof of Lemma 087X
(blueprint: lem-weil-pbc-coherent-formal-short-exact-levels).

Proof:
1. Composition is termwise (def-weil-pbc-coherent-formal-module). Thus an isomorphism
of systems has isomorphic components. Uniqueness of kernels and cokernels gives
comparison isomorphisms commuting with their structure maps.
2. By lem-weil-pbc-coherent-formal-modules-abelian and
lem-weil-pbc-abelian-exact-epi-cokernel, the second arrow is a cokernel of the first.
The termwise cokernels give another cokernel. The comparison isomorphism identifies
its component projections with the second arrow's components. These are epimorphisms
with kernel equal to the first arrow's image, by
lem-weil-pbc-quasi-coherent-module-cokernel-image (and pqf-def-coherent).
3. By lem-weil-pbc-abelian-short-exact-kernel, the first arrow is a kernel of the second.
Compare with the kernel constructed in lem-weil-pbc-coherent-formal-module-kernel.
For positive level N, choose M = N + 2c with its uniform Artin-Rees constant c.
The image of Ker(alpha_M) in F_(N+c) is the stabilized K'_(N+c).
The image corestriction onto K'_(N+c), its quotient onto
K'_(N+c)/I^N K'_(N+c), and the component of the comparison isomorphism onto G_N
are all epimorphisms. Their composite proves the quotient assertion.
4. The kernel construction need not have injective component maps; hence exactness
is asserted only at F_N and surjectivity at H_N, not injectivity at G_N.
-/
theorem coherentFormalModule_shortExact_levels (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) (S : ShortComplex (CoherentFormalModule X I))
    (hS : S.ShortExact) :
    (∀ n : ℕ,
      (S.map ((IsCoherentFormalModule I).ι ⋙
        (evaluation ℕᵒᵖ X.Modules).obj (op n))).Exact ∧ Epi (S.g.hom.app (op n))) ∧
    (∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧
      ∃ q : kernel (S.g.hom.app (op m)) ⟶ S.X₁.obj.obj (op n), Epi q) := by
  sorry

end AlgebraicGeometry
