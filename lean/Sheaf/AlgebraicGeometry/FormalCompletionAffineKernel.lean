/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # The affine kernel fork of a completed short exact sequence

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0881, via Lemmas
087W and 087X (3), and Algebra, Lemma 00MB (2).
(blueprint: lem-weil-pbc-formal-completion-affine-kernel).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- On an affine open, the completed first arrow is a kernel of the completed second
arrow. The restriction functor is specified by its equality after the full inclusion;
no arbitrary replacement of the restriction functor is allowed. The conclusion asserts
only the kernel universal property, not that the completed second arrow is epimorphic.

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0881, affine reduction
and equivalence 087W; Algebra, Lemma 00MB (2).
(blueprint: lem-weil-pbc-formal-completion-affine-kernel).

Proof:
1. Restrict the coherent short exact sequence to U. Its underlying module sequence is
short exact because the coherent full inclusion and open restriction preserve kernels
and cokernels. Affine sections give an exact sequence of finite modules over the
Noetherian ring A = Gamma(U, O_X): kernels are sectionwise, quasi-coherent cokernels
have surjective affine sections, and coherence implies finite affine sections.
2. Restriction identifies the quotient by I^(n+1) with the quotient by the restricted
ideal power. The affine ideal-product and quotient formulas identify its sections,
including the induced maps, with M/I^(n+1)M. The specified equality for rho identifies
its objects, transitions and arrows with these restricted quotient systems.
3. Under the equivalence of Lemma 087W with finite modules over the completed ring,
the three systems and their arrows are the adic completions of the finite A-modules
and the induced linear maps. This identification follows from the natural limit cones
in the equivalence and the quotient formulas of step 2.
4. Algebra, Lemma 00MB (2) gives injectivity of the first completed map and middle
exactness. Thus the first completed map is a kernel of the second in modules over
the completed ring. This ring is Noetherian, the completed modules are finite, and
the full finite-module inclusion creates kernels, so the same fork is limiting in
the finite-module category.
5. Transport this limiting fork through the affine equivalence. Its naturality identifies
it with the fork of the restricted completed arrows. Isomorphic forks have the same
kernel universal property, which gives the stated Nonempty IsLimit.
The argument includes the zero module, the empty affine open, I = 0, and I = O_X;
no injectivity of individual quotient-level first arrows is asserted.
-/
theorem formalCompletion_affine_kernel (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) (h : (completion X I).Additive)
    (U : X.Opens) [IsNoetherian U.toScheme] (hU : IsAffineOpen U)
    (ρ : CoherentFormalModule X I ⥤ CoherentFormalModule U.toScheme (I.comap U.ι))
    (hz : ρ.PreservesZeroMorphisms)
    (hρ : ρ ⋙ (IsCoherentFormalModule (I.comap U.ι)).ι =
      (IsCoherentFormalModule I).ι ⋙
        (Functor.whiskeringRight ℕᵒᵖ X.Modules U.toScheme.Modules).obj
          (Scheme.Modules.restrictFunctor U.ι))
    (S : ShortComplex (CoherentModules X)) (hS : S.ShortExact) :
    let T := @ShortComplex.map _ _ _ _ _ _ S (completion X I)
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ (completion X I) h)
    let V := @ShortComplex.map _ _ _ _ _ _ T ρ hz
    Nonempty (IsLimit (KernelFork.ofι V.f V.zero)) := by sorry

end AlgebraicGeometry
