/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-! # Affine comparison of ideal intersection inclusions

Source: Stacks Project, Tags 01YA, 01I8 and 01IC.
(blueprint: lem-pc-affine-ideal-intersection-inclusion)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- An inclusion between affine section submodules gives the corresponding inclusion
of ideal products on every subopen. No bound, coherence or Noetherian hypothesis is used.
Source: Stacks Project, Tag 01YA, affine reduction; Tags 01I8 and 01IC.
(blueprint: lem-pc-affine-ideal-intersection-inclusion)

Proof: Restrict to the affine scheme U. Quasi-coherent modules are the sheaves associated
to their section modules. The affine equivalence is exact and respects tensor products
(01I8); consequently it respects images, kernels and intersections. The ideal I and its
recursive powers correspond to I(U) and its ordinary powers, including power zero,
which is the structure sheaf. Thus I^m F intersect G corresponds to
I(U)^m F(U) intersect image(g(U)), whereas the image of I^n G in F corresponds to
map(g(U), I(U)^n G(U)). The assumed inclusion factors the first inclusion into F
through the second. Apply the affine equivalence (01IC) and restrict the factorization
to W. A section in both ranges lifts uniquely to the intersection sheaf: the two
preimages satisfy the pullback condition, since their images agree. Its image under
the factorization is a preimage in I^n G, proving the range inclusion. This works for
an empty U or W, m=0, n=0, zero modules, and zero or unit ideals. -/
theorem affine_ideal_intersection_inclusion {X : Scheme.{u}}
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (g : G ⟶ F) [Mono g] (I : X.IdealSheafData) (U : X.affineOpens) (m n : ℕ)
    (hmodule : I.ideal U ^ m • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) ⊓
        LinearMap.range (g.val.app (.op U.1)).hom ≤
      Submodule.map (g.val.app (.op U.1)).hom
        (I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1)))) :
    ∀ W : X.Opens, W ≤ U.1 →
      Set.range ((idealModuleProductι (idealSheafPower I.toModulesι m).2 F).app W) ∩
          Set.range (g.app W) ⊆
        Set.range ((idealModuleProductι (idealSheafPower I.toModulesι n).2 G ≫ g).app W) := by sorry

end AlgebraicGeometry.Scheme.Modules
