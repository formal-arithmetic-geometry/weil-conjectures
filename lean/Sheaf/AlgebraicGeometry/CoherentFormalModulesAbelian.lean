/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-! # Coherent formal modules form an abelian category

Source: Stacks Project, Cohomology of Schemes, Lemma 087X, part (1), and the description
of cokernels in its proof (blueprint: lem-weil-pbc-coherent-formal-modules-abelian).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The category Coh(X,I) is abelian, and every morphism has a cokernel cofork whose
image under evaluation at each positive level is a cokernel cofork of that component.
Thus its cokernel is the inverse system of termwise cokernels, with transitions induced
by the universal property. Here `op n` denotes positive level `n + 1`.

Source: Stacks, Lemma 087X, part (1), and its proof
(blueprint: lem-weil-pbc-coherent-formal-modules-abelian).

Proof (the ten steps of the node):
1. Transitions are surjective and identify later terms modulo lower powers with earlier
terms. Choose a finite affine cover. The affine equivalence of
lem-weil-pbc-coherent-formal-modules-affine identifies each system with a finite module over
an adic completion; quasi-coherent maps and submodules can be checked on these affines
using lem-weil-pbc-affine-tilde-gamma-adjunction and
lem-weil-pbc-ideal-times-quasi-coherent-affine-sections.
2. Addition and composition are termwise. Zero and binary direct sums satisfy the adic
conditions, giving finite biproducts (lem-weil-pbc-coherent-kernel-cokernel-locnoeth).
3. Component cokernels are coherent by that same node and
lem-weil-pbc-quasi-coherent-module-cokernel-image. Their induced transitions satisfy the
adic quotient condition: affine sections are the quotient of the target by the image,
and reducing modulo I^n commutes with that quotient. Component quotient projections are
compatible. Each compatible family killing the morphism factors uniquely through them;
epimorphic quotient projections imply that the factorizations commute with transitions.
4. Form K'_{l,m}, the image of Ker(alpha_l) in F_m. On each affine it is
(f^{-1}(I^l N) + I^m M)/I^m M. Noetherianity of the completion
(lem-weil-pbc-adic-completion-noetherian) and Artin-Rees
(lem-weil-pbc-artin-rees), applied to Ker(f) and Im(f), give a uniform c over the finite
cover. For l >= m+c these images stabilize at (K + I^m M)/I^m M, where K=Ker(f).
5. The quotient K'_m/I^n K'_m stabilizes for m >= n+c at K/I^n K. Set
K_n=K'_{n+c}/I^n K'_{n+c}. These coherent quotients satisfy the adic conditions and
form a system (lem-weil-pbc-ideal-times-quasi-coherent-affine-sections).
6. The inclusions induce a compatible map K_n -> F_n killing alpha. Any beta killed by
alpha lands in K'_{l,m}, since its source transitions are epi. Pass to the stabilized
images and then reduce modulo I^n to obtain a compatible factorization through K_n.
7. Uniqueness follows from Artin-Rees: the kernel of K_{n+c} -> F_{n+c} maps to zero in
K_n. A factorization whose composite is zero therefore vanishes after precomposition
with an epimorphic source transition, and hence vanishes. This gives kernels.
8. The constructions commute with affine restriction: kernels, images, ideal products
and cokernels restrict, and the stabilization constants can be enlarged. Under the affine
equivalence they are the kernel and cokernel of the corresponding finite module map.
9. Consequently the coimage-image comparison is an isomorphism on each affine by the
first isomorphism theorem for modules. The affine equivalence reflects isomorphisms;
componentwise local checking proves the comparison is an isomorphism globally.
10. Apply lem-weil-pbc-abelian-of-coimage-image-iso to the preadditive category with finite
products, kernels and cokernels. Step 3 gives exactly the asserted termwise cokernel clause.
-/
theorem coherentFormalModule_abelian (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) :
    Nonempty (Abelian (CoherentFormalModule X I)) ∧
      ∀ (F G : CoherentFormalModule X I) (α : F ⟶ G),
        ∃ c : CokernelCofork α, Nonempty (IsColimit c) ∧
          ∀ n : ℕ, Nonempty (IsColimit
            (((IsCoherentFormalModule I).ι ⋙
              (evaluation ℕᵒᵖ X.Modules).obj (op n)).mapCocone c)) := by
  sorry

end AlgebraicGeometry
