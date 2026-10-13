/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Affine comparison for ideal products and intersections

Source: Stacks Project, Cohomology of Schemes, Tag 01YA, affine reduction in the proof;
Algebra, Tag 00IN (blueprint: lem-weil-pbc-artin-rees-affine-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- An equality of ideal products and intersections of affine section modules yields
an equality of the corresponding subsheaves on that affine open. This is the geometric
comparison only; neither coherence, a Noetherian hypothesis, nor an Artin-Rees bound
is assumed.

Source: Stacks Project, Cohomology of Schemes, Tag 01YA, affine reduction in the proof;
Schemes, Tags 01I8 and 01IC
(blueprint: lem-weil-pbc-artin-rees-affine-comparison).

Proof: Products by the powers of I are quasi-coherent, including the zeroth power.
For every t, realize H_t = I^t F ∩ G as the kernel of G → F/(I^t F).
The quotient, kernel, and ideal products of this kernel are quasi-coherent.
Evaluation on the affine open is exact on quasi-coherent modules. Thus H_t(U)
is I(U)^t F(U) ∩ image(G(U) → F(U)), with its inclusion into F(U).
The affine product formula identifies the image of I^(n-c) H_c on U with
I(U)^(n-c) (I(U)^c F(U) ∩ image(G(U) → F(U))). The assumed module equality
therefore identifies the affine sections of I^(n-c) H_c and H_n, compatibly
with both inclusions into F. Restrict these quasi-coherent modules to U.
The affine tilde/global-sections equivalence transports the equality into an
isomorphism of the two submodules of F restricted to U, commuting with their
inclusions. Evaluate this isomorphism on any W ≤ U to obtain equality of ranges.
The empty open, zero modules, zero or unit ideal, and c=0 or n=0 need no exclusion:
exactness and the affine equivalence hold for them, and I^0 is the unit ideal. -/
theorem artin_rees_affine_comparison {X : Scheme.{u}}
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (g : G ⟶ F) [Mono g] (I : X.IdealSheafData) (U : X.affineOpens) (c n : ℕ)
    (hmodule : I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) ⊓
        LinearMap.range (g.val.app (.op U.1)).hom =
      I.ideal U ^ (n - c) • (I.ideal U ^ c •
        (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) ⊓
          LinearMap.range (g.val.app (.op U.1)).hom)) :
    ∀ W : X.Opens, W ≤ U.1 →
      Set.range ((idealModuleProductι (idealSheafPower I.toModulesι (n - c)).2
        (pullback (idealModuleProductι (idealSheafPower I.toModulesι c).2 F) g) ≫
          pullback.fst (idealModuleProductι (idealSheafPower I.toModulesι c).2 F) g ≫
            idealModuleProductι (idealSheafPower I.toModulesι c).2 F).app W) =
        Set.range ((idealModuleProductι (idealSheafPower I.toModulesι n).2 F).app W) ∩
          Set.range (g.app W) := by sorry

end AlgebraicGeometry.Scheme
