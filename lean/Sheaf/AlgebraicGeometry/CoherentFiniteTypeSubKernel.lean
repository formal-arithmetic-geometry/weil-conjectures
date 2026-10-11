/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent

/-! # Finite type submodules and kernels of coherent modules

Source: Stacks Project, Modules, Lemma 01BY
(blueprint: lem-weil-pbc-coherent-finite-type-sub-kernel).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

/-- A finite type submodule of a coherent module is coherent, and the kernel of a
map from a finite type module to a coherent module is finite type.
Source: Stacks Project, Modules, Lemma 01BY
(blueprint: lem-weil-pbc-coherent-finite-type-sub-kernel).
Proof, following the five steps of the node:
1. Restrict modules to opens by `over`. Maps from a finite free module are given
   by the images of its basis sections, and kernels are computed sectionwise,
   hence commute with restriction (def-weil-pbc-module-finite-type-presentation,
   def-weil-sheaf-of-modules-category).
2. For part (1), `K` is already of finite type. Compose each map from a finite
   free module on an open into `K` with the inclusion into `G`. Its kernel is
   finite type by coherence of `G` and equals the original kernel because the
   inclusion is sectionwise injective. Thus `K` is coherent (pqf-def-coherent).
3. For part (2), around each point choose a finite free epimorphism onto `F`.
   The kernel `L` of its composite into `G` is finite type by coherence of `G`.
   The presentation restricts to a map from `L` into the restriction of `kernel φ`
   (def-weil-pbc-module-finite-type-presentation, pqf-def-coherent).
4. Each section of `kernel φ` locally lifts through the presentation of `F`.
   Every such lift lies in `L` because its image under `φ` is zero. The map from
   `L` onto the restricted kernel is therefore an epimorphism by the local
   lifting criterion (lem-weil-pbc-ringed-space-module-exactness-local-lifting).
5. Its target is finite type, being an image of the finite type module `L`
   (lem-weil-pbc-module-finite-type-image-extension). Shrinking around the chosen
   point gives finite local generators of `kernel φ`; since the point was
   arbitrary, the kernel is of finite type.
-/
theorem coherent_finiteType_submodule_kernel
    (X : RingedSpace.{u}) :
    (∀ (K G : SheafOfModules.{u} (moduleRings X))
      (i : K ⟶ G) [Mono i],
      K.IsFiniteType → IsCoherent X G → IsCoherent X K) ∧
    (∀ (F G : SheafOfModules.{u} (moduleRings X))
      (φ : F ⟶ G),
      F.IsFiniteType → IsCoherent X G → (kernel φ).IsFiniteType) := by
  sorry

end AlgebraicGeometry.RingedSpace
