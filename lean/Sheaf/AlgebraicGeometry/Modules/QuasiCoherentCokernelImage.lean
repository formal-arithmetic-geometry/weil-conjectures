/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Cokernels and images of quasi-coherent modules

Source: Stacks Project, Schemes, Tags 01IC, 01IB, 01LB; Modules, Tag 01AH
(blueprint: lem-weil-pbc-quasi-coherent-module-cokernel-image).

The categorical cokernel is the sheafified presheaf quotient (Mathlib's module
sheafification adjunction and colimit construction). The abelian image is its kernel;
the local-image formula below identifies it with the subsheaf in the node.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Cokernels and local images of maps of quasi-coherent modules are quasi-coherent,
and their sections on affine opens are the module cokernel and image.
Source: Stacks Project, Schemes, Tags 01IC, 01IB, 01LB; Modules, Tag 01AH
(blueprint: lem-weil-pbc-quasi-coherent-module-cokernel-image).

Proof:
1. Restrict to an affine open using
`lem-weil-pbc-module-restriction-open-immersion-colimits`: restriction preserves
cokernels and quasi-coherence (pqf-def-coherent).
2. On Spec R, use lem-weil-pbc-affine-tilde-gamma-adjunction, clauses (3), (4), (2),
and lem-weil-pbc-spec-module-tilde-sections. The tilde/global-sections identifications
turn the map into an R-linear map; tilde preserves its cokernel. Its global sections
are the quotient by the range, with surjective projection and precisely that kernel.
3. Affine neighbourhoods cover the scheme. Quasi-coherence is local, so the cokernel
is quasi-coherent; lem-weil-pbc-quasi-coherent-module-kernel gives quasi-coherence
of the kernel of its projection.
4. By lem-weil-pbc-sheaf-cokernel-local-image and def-weil-pbc-sheafification, a
section of this kernel is exactly a section locally in the image. This identifies
the abelian image with the local-image subsheaf, gives the factorization and the
epimorphic quotient map annihilating the original map, and the affine formulas
from step 2 give all the sectionwise conclusions. -/
theorem quasiCoherent_cokernel_image {X : Scheme.{u}} {F G : X.Modules}
    (φ : F ⟶ G) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Mono (Abelian.image.ι φ) ∧
    (∀ W : X.Opens,
      LinearMap.range ((Abelian.image.ι φ).val.app (op W)).hom =
        LinearMap.ker ((cokernel.π φ).val.app (op W)).hom) ∧
    (∀ (W : X.Opens) (s : Γ(G, W)),
      s ∈ Set.range ((Abelian.image.ι φ).app W) ↔
        ∀ x : X, x ∈ W → ∃ (V : X.Opens) (h : V ≤ W),
          x ∈ V ∧ ∃ t : Γ(F, V), φ.app V t = G.presheaf.map (homOfLE h).op s) ∧
    Abelian.factorThruImage φ ≫ Abelian.image.ι φ = φ ∧
    Epi (cokernel.π φ) ∧ φ ≫ cokernel.π φ = 0 ∧
    (cokernel φ).IsQuasicoherent ∧ (Abelian.image φ).IsQuasicoherent ∧
    (∀ U : X.affineOpens,
      Set.range ((Abelian.image.ι φ).app U.1) = Set.range (φ.app U.1) ∧
      Function.Surjective ((cokernel.π φ).app U.1) ∧
      LinearMap.ker ((cokernel.π φ).val.app (op U.1)).hom =
        LinearMap.range (φ.val.app (op U.1)).hom ∧
      ∃ e : (Γ(G, U.1) ⧸ LinearMap.range (φ.val.app (op U.1)).hom) ≃ₗ[Γ(X, U.1)]
          Γ(cokernel φ, U.1),
        ∀ s : Γ(G, U.1),
          e ((LinearMap.range (φ.val.app (op U.1)).hom).mkQ s) =
            (cokernel.π φ).app U.1 s) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
