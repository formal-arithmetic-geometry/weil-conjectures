/-
Copyright (c) 2026 F1. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: F1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-!
# Evaluation of internal Hom on affine opens

Source: Stacks Project, duality.tex, Tag 0BUZ, lemma-compute-sheafhom-affine.
(blueprint: lem-sc-affine-internal-hom-evaluation-bijective).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A morphism from a quasi-coherent module on an affine open is uniquely
specified by its map on sections, even when the target is not quasi-coherent.

Source: Stacks Project, duality.tex, Tag 0BUZ, lemma-compute-sheafhom-affine;
Mathlib, AlgebraicGeometry.tilde.adjunction.
(blueprint: lem-sc-affine-internal-hom-evaluation-bijective).

Proof: Restrict M and F to U. The over-category description of the internal
Hom identifies its sections on U with morphisms of module sheaves on U.
Identify the affine scheme U with Spec Gamma(U,O). Quasi-coherence of M
makes the counit from the tilde of Gamma(U,M) to M invertible. Precompose
with this counit, and apply the tilde/global-sections adjunction, which
holds for every target module sheaf. Its unit identifies the sections of
the tilde with the original module, so the resulting bijection sends a
morphism to its component at U. Both changes of chart and restriction
preserve these components. Thus evaluation at the terminal object of
Over U is bijective. No finite presentation or quasi-coherence of F is used.
For U empty all section modules are zero and the same argument applies. -/
theorem affine_internalHom_evaluation_bijective
    {X : Scheme.{u}} (M F : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective
      (fun φ : (SheafOfModules.homObj M F).val.obj (op U) ↦
        (φ.app (op (Over.mk (𝟙 U)))).hom) := by
  sorry

end AlgebraicGeometry
