/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Exactness of coherent formal completion

Source: Stacks Project, Cohomology of Schemes, Lemma 0881 and equation 0880
(blueprint: lem-weil-pbc-formal-completion-exact).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The coherent-module and coherent-formal-module categories are abelian, and the
canonical completion functor is additive and carries every short exact sequence to a
short exact sequence. The additivity witness supplies zero preservation when mapping
short complexes; it is not a hypothesis. Positive level n is indexed by op (n - 1).

Source: Stacks Project, Cohomology of Schemes, Lemma 0881, equation 0880; Homology,
Lemma 010N (4) (blueprint: lem-weil-pbc-formal-completion-exact).

Proof:
1. Coherent modules are closed under kernels, cokernels and finite sums on a locally
Noetherian scheme (lem-weil-pbc-coherent-kernel-cokernel-locnoeth), and under isomorphism
(lem-weil-pbc-coherent-modules-kernel-cokernel-sum). Apply
lem-weil-pbc-abelian-full-subcategory-exact. The formal category is abelian by
lem-weil-pbc-coherent-formal-modules-abelian. Reduction of maps modulo ideal powers is
additive: precompose with the quotient epimorphism and use uniqueness of the induced map.
2. Choose a finite affine cover by Noetherian rings. Restriction commutes with ideal
products and their quotient cokernels (lem-weil-pbc-ideal-times-quasi-coherent-affine-sections).
Thus restriction commutes with completion. By
lem-weil-pbc-coherent-formal-modules-local-exactness it suffices to check short exactness
on each affine open.
3. On an affine open U, sections of the original sequence are short exact: kernels are
sectionwise, and quasi-coherent cokernels have surjective affine sections
(lem-weil-pbc-quasi-coherent-module-cokernel-image). Coherent modules have finite affine
sections by pqf-lem-coherent-ft-locnoeth and lem-weil-pbc-quasi-coherent-finite-type-affine.
4. The affine equivalence of lem-weil-pbc-coherent-formal-modules-affine identifies the
completed sequence with the adic completions of these finite modules. Affine sections of
F/I^n F are M/I^n M, including the induced maps, by
lem-weil-pbc-ideal-times-quasi-coherent-affine-sections and
lem-weil-pbc-affine-tilde-gamma-adjunction.
5. Apply lem-weil-pbc-completion-exact-finite-modules (Algebra, Lemma 00MB (2)). The
completion ring is Noetherian (lem-weil-pbc-adic-completion-noetherian); therefore the
sequence is short exact in its abelian category of finite modules
(lem-weil-pbc-finite-modules-noetherian-abelian).
6. The additive quasi-inverse of the affine equivalence carries this sequence back to a
short exact formal sequence (lem-weil-pbc-equivalence-injective-resolutions). Naturality
of the equivalence identifies it with the restricted completed sequence. Apply the local
criterion from step 2. Together with step 1 this proves exactness.
-/
theorem formalCompletion_exact (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) :
    Nonempty (Abelian (AlgebraicGeometry.CoherentModules X)) ∧
      Nonempty (Abelian (AlgebraicGeometry.CoherentFormalModule X I)) ∧
      ∃ h : (AlgebraicGeometry.completion X I).Additive,
        ∀ S : ShortComplex (AlgebraicGeometry.CoherentModules X), S.ShortExact →
          (@ShortComplex.map _ _ _ _ _ _ S (AlgebraicGeometry.completion X I)
            (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
              (AlgebraicGeometry.completion X I) h)).ShortExact := by
  sorry

end AlgebraicGeometry
