/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.AlgebraicGeometry.CoherentFormalModule

/-! # Artin-Rees for coherent modules on a Noetherian scheme

Source: Stacks Project, Cohomology of Schemes, Lemma 01YA (lemma-Artin-Rees)
(blueprint: lem-weil-pbc-coherent-artin-rees).

The pullback of the two inclusions represents their sectionwise intersection. Equalities
and inclusions of subsheaves are expressed by their images in the sections of `F` on every
open. Powers and multiplication images use the shared definitions from the formal-module
node, including the zeroth power of the ideal.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Artin-Rees for a quasi-coherent subsheaf `g : G ⟶ F` of a coherent module `F`.
The constant `c` is uniform over all opens and all `n ≥ c`. The first clause is the equality
I^(n-c)(I^c F ∩ G) = I^n F ∩ G; the second is its inclusion in I^(n-c) G, all inside F.

Source: Stacks Project, Cohomology of Schemes, Lemma 01YA (lemma-Artin-Rees)
(blueprint: lem-weil-pbc-coherent-artin-rees).

Proof:
1. Choose a finite Noetherian affine cover using pqf-def-locnoeth and quasi-compactness.
   The quasi-coherent submodule is coherent by
   lem-weil-pbc-coherent-kernel-cokernel-locnoeth. On each affine its sections and those of F
   are finite modules by lem-weil-pbc-quasi-coherent-finite-type-affine; products and powers
   are identified by lem-weil-pbc-ideal-times-quasi-coherent-affine-sections.
2. Apply lem-weil-pbc-artin-rees to every affine. Take the maximum of the constants (zero
   for the empty cover). Applying each local formula at c and n and multiplying powers
   shows that this larger constant works on every affine.
3. Express I^c F ∩ G as the kernel of G → F / I^c F. The quotient is quasi-coherent by
   lem-weil-pbc-quasi-coherent-module-cokernel-image, and the kernel by
   lem-weil-pbc-quasi-coherent-module-kernel. Its affine sections are the intersection;
   lem-weil-pbc-ideal-times-quasi-coherent-affine-sections identifies its ideal products.
4. Both sides are quasi-coherent. Restrict using
   lem-weil-pbc-module-restriction-open-immersion-colimits and identify the submodules from
   their affine sections by lem-weil-pbc-affine-tilde-gamma-adjunction. Equality on the cover
   yields equality on X. Finally I^c F ∩ G ⊆ G gives the claimed inclusion by the
   multiplication-image definition in def-weil-pbc-coherent-formal-module. -/
theorem coherent_artin_rees {X : Scheme.{u}} [IsNoetherian X]
    (F G : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (g : G ⟶ F) [Mono g] (hG : G.IsQuasicoherent) (I : X.IdealSheafData) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n → ∀ W : X.Opens,
      Set.range ((idealModuleProductι (idealSheafPower I.toModulesι (n - c)).2
        (pullback (idealModuleProductι (idealSheafPower I.toModulesι c).2 F) g) ≫
          pullback.fst (idealModuleProductι (idealSheafPower I.toModulesι c).2 F) g ≫
            idealModuleProductι (idealSheafPower I.toModulesι c).2 F).app W) =
        Set.range ((idealModuleProductι (idealSheafPower I.toModulesι n).2 F).app W) ∩
          Set.range (g.app W) ∧
      Set.range ((idealModuleProductι (idealSheafPower I.toModulesι n).2 F).app W) ∩
          Set.range (g.app W) ⊆
        Set.range ((idealModuleProductι (idealSheafPower I.toModulesι (n - c)).2 G ≫
          g).app W) := by
  sorry

end AlgebraicGeometry.Scheme
