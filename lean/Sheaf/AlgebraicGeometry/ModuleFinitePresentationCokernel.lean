/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting
import Sheaf.AlgebraicGeometry.ModuleFiniteTypeImageExtension

/-!
# Finite presentation of cokernels on a ringed space

Source: Stacks Project, Modules, Lemma 0H96
(blueprint: lem-weil-pbc-module-finite-presentation-cokernel).

## Main statements

- `AlgebraicGeometry.RingedSpace.isFinitePresentation_cokernel_of_isFiniteType`:
  finite-type source and finitely presented target give a finitely presented cokernel.
- `AlgebraicGeometry.RingedSpace.isFinitePresentation_cokernel_of_both_isFinitePresentation`:
  the special case where both source and target are finitely presented.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

/-- Stacks Project, Modules, Lemma 0H96
(blueprint: lem-weil-pbc-module-finite-presentation-cokernel).
The cokernel of a map from a finite-type module sheaf to a finitely presented module sheaf
on a ringed space is finitely presented.

Proof (the seven steps of the node):
1. Restriction to opens preserves epis and exactness by the local lifting criterion
   (lem-weil-pbc-ringed-space-module-exactness-local-lifting), hence cokernels by
   lem-weil-pbc-abelian-exact-epi-cokernel. Both finiteness conditions are local and invariant
   under isomorphism (def-weil-pbc-module-finite-type-presentation). Finite free modules are
   finite type, and finite presentation implies finite type by its finite generating family.
2. Near each point choose a presentation O^m -> O^n -> H -> 0. Restrict f and its cokernel
   there. Locality reduces the claim to this presentation on the whole space.
3. The relations M = ker(O^n -> H) are finite type: the induced map O^m -> M is epi by
   lem-weil-pbc-abelian-exact-iff-epi-kernel-lift, and finite type passes to epi images by
   lem-weil-pbc-module-finite-type-image-extension (1).
4. The map G -> im(f) is epi by the same kernel-lift lemma. Thus im(f) is finite type by
   lem-weil-pbc-module-finite-type-image-extension (1).
5. Let N be the preimage of im(f) in O^n. Sectionwise kernels and local lifting give an
   exact sequence 0 -> M -> N -> im(f) -> 0 (def-weil-pbc-exact-sequence). Therefore N is
   finite type by lem-weil-pbc-module-finite-type-image-extension (2).
6. Near each point choose an epi O^s -> N. Its composite into O^n has cokernel Coker(f),
   since restriction preserves exactness and epis and an exact epi is a cokernel
   (lem-weil-pbc-abelian-exact-epi-cokernel). This finite presentation proves the claim.
7. If G is also finitely presented, step 1 makes it finite type, giving the final clause
   in `isFinitePresentation_cokernel_of_both_isFinitePresentation`. -/
theorem isFinitePresentation_cokernel_of_isFiniteType
    (X : RingedSpace.{u}) {G H : SheafOfModules.{u} (moduleRings X)}
    (f : G ⟶ H) [G.IsFiniteType] [H.IsFinitePresentation] :
    (cokernel f).IsFinitePresentation := by
  sorry

/-- Stacks Project, Modules, Lemma 0H96, its finite-presentation special case
(blueprint: lem-weil-pbc-module-finite-presentation-cokernel).

Proof: step 7 of the node applies Mathlib's instance
`SheafOfModules.instIsFiniteTypeOfIsFinitePresentation` to G, as its
local finite presentation supplies finitely many generators
(def-weil-pbc-module-finite-type-presentation). Then steps 1-6, stated above in
`isFinitePresentation_cokernel_of_isFiniteType`, give finite presentation of the cokernel. -/
theorem isFinitePresentation_cokernel_of_both_isFinitePresentation
    (X : RingedSpace.{u}) {G H : SheafOfModules.{u} (moduleRings X)}
    (f : G ⟶ H) [G.IsFinitePresentation] [H.IsFinitePresentation] :
    (cokernel f).IsFinitePresentation := by
  sorry

end AlgebraicGeometry.RingedSpace
