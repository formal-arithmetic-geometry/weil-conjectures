/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StackBigEtaleModuleCalculus

/-! # Arbitrary base change for big etale higher direct images

Source: Stacks Project, stacks-sheaves.tex, Tag 075H,
lemma-base-change-higher-direct-images
(blueprint: lem-sfb-stack-big-etale-higher-image-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace CategoryTheory

/-- Higher direct images of all structure-module sheaves commute with arbitrary
base change on the big etale sites of algebraic stacks.
Source: Stacks Project, Tag 075H, lemma-base-change-higher-direct-images
(blueprint: lem-sfb-stack-big-etale-higher-image-base-change).

Proof: apply lem-sfb-stack-big-etale-derived-base-change to the recorded two-fibre
product square and M in degree zero. Precomposition is exact and acts termwise.
For a complex K, exactness identifies the cycles and boundaries after precomposition
with the precompositions of its cycles and boundaries, hence also identifies their
quotient. Thus precomposition commutes with cohomology, naturally in K. Apply degree-i
cohomology to the derived comparison, using the injective-resolution identifications
of H^i(Rf_*M) with R^if_*M. The resulting morphism is the specified counit-mate
comparison moduliBigEtaleHigherBaseChange. Applying cohomology to the inverse derived
comparison supplies its inverse. No representability, flatness, smoothness, qcqs or
quasi-coherence hypothesis enters this argument. -/
theorem isIso_moduliBigEtaleHigherBaseChange {S : AlgebraicGeometry.Scheme.{u}}
    {X Y Y' : BasedCategory.{v, w} (Over S)}
    (hX : IsAlgebraicModuliStack X) (hY : IsAlgebraicModuliStack Y)
    (hY' : IsAlgebraicModuliStack Y') (f : BasedFunctor X Y) (b : BasedFunctor Y' Y)
    (M : ModuliBigEtaleModules X hX.1.1) (i : ℕ) :
    IsIso ((moduliBigEtaleHigherBaseChange hX.1.1 hY.1.1 hY'.1.1 f b i).app M) := by
  sorry

end CategoryTheory
