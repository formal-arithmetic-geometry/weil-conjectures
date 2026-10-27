/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q120
-/
module

public import Sheaf.AlgebraicGeometry.SpaceGroupoidModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Abelianity for flat algebraic-space groupoids

Source: Stacks Project, Groupoids in Algebraic Spaces, Tag 06VZ,
`definition-groupoid-module` and `lemma-abelian`
(blueprint: lem-sfb-flat-space-groupoid-abelian).

The descent category and its forgetful functor are the existing constructions in
`SpaceGroupoidModule`. The bundled groupoid retains an arbitrary specified
composable-arrow fibre product and all the test-scheme groupoid laws.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Flat groupoid descent modules are abelian, with their underlying addition, kernels
and cokernels. Preservation of each kernel/cokernel diagram says that its underlying
module cone is the corresponding module-sheaf kernel/cokernel; its object still carries
quasi-coherence and the induced equivariance. No finiteness hypotheses are imposed.
Source: Stacks, Tag 06VZ, `lemma-abelian`
(blueprint: lem-sfb-flat-space-groupoid-abelian).

Proof: apply lem-sfb-flat-space-groupoid-kernels-cokernels to this groupoid and its two
flat maps. Its category has exactly the same target-to-source descent, identity and
cocycle equations, underlying module morphisms, identities and compositions. That result
provides an abelian structure, with underlying addition, and computes both kernels and
cokernels on the small étale module sheaves. Flat tensor pullbacks preserve kernels and
all tensor pullbacks preserve cokernels; the induced descent isomorphisms satisfy the
unit and cocycle equations by their universal properties. The underlying kernels and
cokernels remain quasi-coherent. These are precisely the conclusions asserted here. -/
theorem flat_space_groupoid_abelian {S : Scheme.{u}} (G : ModuleGroupoid S)
    (_hs : MapIsFlat G.s) (_ht : MapIsFlat G.t) :
    ∃ (_a : Abelian (SpaceGroupoidModule G)),
      (SpaceGroupoidModule.forgetToModules (G := G)).Additive ∧
      ∀ (M N : SpaceGroupoidModule G) (f : M ⟶ N),
        PreservesLimit (parallelPair f 0)
          (SpaceGroupoidModule.forgetToModules (G := G)) ∧
        PreservesColimit (parallelPair f 0)
          (SpaceGroupoidModule.forgetToModules (G := G)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
