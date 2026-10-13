/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Affine formal gluing comparison

Source: Stacks Project, Tags 087W, 0888 and 0889(1).
(blueprint: lem-weil-pbc-affine-map-annihilation-sheafification).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Sheafification transfers a fixed annihilating power for an algebraic map.

Source: Stacks Project, Tags 01I7, 01IB and 0889(1).
(blueprint: lem-weil-pbc-affine-map-annihilation-sheafification).

Proof: exactness of tilde identifies its sheaf kernel and cokernel with tilde of
the algebraic kernel and cokernel. The given ideal annihilator inclusions say that
the product by I^t is zero in both modules. The affine ideal-product formula identifies
the sheaf product with tilde of that module product; hence both are zero sheaves.
Transport along the canonical affine scheme isomorphism and along ε. Pullback by
an isomorphism is exact and identifies the ideal sheaf of I with J, so the same
exponent t annihilates the kernel and cokernel of the displayed sheaf map. This
holds for arbitrary T and P; neither coherence nor finite generation is used.
For t=0 it says the kernel and cokernel themselves are zero, and the same argument
applies. The empty scheme is covered by the same exact functors.
-/
theorem affine_map_annihilation_sheafification
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData) :
    let A := Γ(X, ⊤)
    let I := J.ideal ⟨⊤, isAffineOpen_top X⟩
    let L := tilde.functor A ⋙ Scheme.Modules.pullback X.isoSpec.hom
    ∀ (T P : ModuleCat.{u} A) (ψ : T →ₗ[A] P) (G : X.Modules)
      (ε : L.obj P ≅ G) (t : ℕ),
      I ^ t ≤ Module.annihilator A ψ.ker →
      I ^ t ≤ Module.annihilator A (P ⧸ ψ.range) →
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (kernel (L.map (ModuleCat.ofHom ψ) ≫ ε.hom))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (cokernel (L.map (ModuleCat.ofHom ψ) ≫ ε.hom))) := by sorry

end AlgebraicGeometry
