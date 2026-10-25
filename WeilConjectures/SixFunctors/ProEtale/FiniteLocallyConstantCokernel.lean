/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf

/-!
# Cokernels of morphisms of constant pro-étale sheaves are locally constant

Let `Λ` be a finite commutative ring and `X` a scheme. This file shows that the cokernel of a
morphism `φ : M_X ⟶ N_X` between the constant pro-étale sheaves of `Λ`-modules of a finitely
generated module `M` and a finite module `N` is locally constant with finite stalks
(`AlgebraicGeometry.ProEtale.isFiniteLocallyConstant_cokernel`). The morphism `φ` is determined
by the global sections of `N_X` that are the images of generators of `M`; global sections of the
sheafification of the constant presheaf are locally constant, so on the members of a pro-étale
covering family `φ` is the constant morphism of a linear map `ψ : M ⟶ N`, and there the cokernel
is the constant sheaf of the finite module `N ⧸ ψ(M)`.

## Main statements

- `AlgebraicGeometry.ProEtale.IsFiniteLocallyConstant.of_cover`: being locally constant with
  finite stalks is local for the pro-étale topology.
- `AlgebraicGeometry.ProEtale.isFiniteLocallyConstant_cokernel`: the cokernel of a morphism of
  constant sheaves of finite modules is locally constant with finite stalks.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Being locally constant with finite stalks is local for the pro-étale topology: if the
pullbacks of `F` along the members of a pro-étale covering family are locally constant with
finite stalks, so is `F` (compose the covering families). -/
theorem IsFiniteLocallyConstant.of_cover {X : Scheme.{u}}
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} {ι : Type (u + 1)}
    {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    (h : ∀ i, IsFiniteLocallyConstant Λ (((g i))^*[ModuleCat.{u + 1} Λ].obj F)) :
    IsFiniteLocallyConstant Λ F :=
  sorry

/-- The cokernel of a morphism `M_X ⟶ N_X` of constant pro-étale sheaves, with `M` finitely
generated and `N` finite, is locally constant with finite stalks. -/
theorem isFiniteLocallyConstant_cokernel [Finite Λ] {X : Scheme.{u}}
    {M N : ModuleCat.{u + 1} Λ} [Module.Finite Λ M] [Finite N]
    (φ : (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj M ⟶
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj N) :
    IsFiniteLocallyConstant Λ (cokernel φ) :=
  sorry

end AlgebraicGeometry.ProEtale
