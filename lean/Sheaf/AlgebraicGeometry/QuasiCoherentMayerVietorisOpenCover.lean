/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Topology.OpenModuleCohomology
public import Mathlib.Algebra.Exact.Basic

/-! # Mayer--Vietoris for quasi-coherent modules on an open subscheme

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.8.2, Tag 01EB
(blueprint: lem-sc-mayer-vietoris-open-cover).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme

/-- Mayer--Vietoris on any open subscheme `W` of `X`, for quasi-coherent modules on `W`.
Pairs of opens of `W` are allowed simultaneously; their union is the base of each sequence.
Taking their union to be all of `W` gives the asserted sequence for the original cover.
The product of two abelian groups is their finite direct sum. Injectivity in degree zero
and the three repeating exactness conditions include the convention `H⁻¹ = 0`.
The third conjunct is naturality in the module, and the fourth is compatibility with restriction
of a cover to any smaller open `T`. Cohomology on these opens is computed using resolutions
on `W`; restriction of the resolution identifies it with cohomology of the restricted module.

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.8.2, Tag 01EB
(blueprint: lem-sc-mayer-vietoris-open-cover).

Proof: Apply `lem-sc-mayer-vietoris-ringed-space` to the ringed space underlying `W`.
Its long exact sequence gives the initial injection and the three exactness positions,
with the pair of restriction maps and their difference. Restrict its module-natural
connecting maps to quasi-coherent modules (`pqf-def-coherent`). Its compatibility with
restriction to a smaller open gives the last square, including the connecting maps;
all other squares are the functoriality squares of cohomology restriction. The groups are
the right derived functors of sections (`pqf-def-cohomology`, realized on opens by
`def-sc-open-module-cohomology`). No proof uses quasi-coherence beyond this specialization. -/
theorem quasiCoherent_mayerVietoris_openCover (X : Scheme.{u}) (W : X.Opens) :
    ∃ δ : ∀ (F : SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) [F.IsQuasicoherent]
      (U V : Opens W.toScheme) (p : ℕ),
      (openModuleCohomology W.toScheme.toRingedSpace p (U ⊓ V)).obj F ⟶ (openModuleCohomology
          W.toScheme.toRingedSpace (p + 1) (U ⊔ V)).obj F,
      (∀ (F : SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) [F.IsQuasicoherent]
        (U V : Opens W.toScheme),
        Function.Injective (fun x : (openModuleCohomology W.toScheme.toRingedSpace 0 (U ⊔ V)).obj
          F => ((openModuleCohomologyRestriction W.toScheme.toRingedSpace 0 (homOfLE
          le_sup_left)).app F x, (openModuleCohomologyRestriction W.toScheme.toRingedSpace 0
          (homOfLE le_sup_right)).app F x))) ∧
      (∀ (F : SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) [F.IsQuasicoherent]
        (U V : Opens W.toScheme) (p : ℕ),
        Function.Exact (fun x : (openModuleCohomology W.toScheme.toRingedSpace p (U ⊔ V)).obj F =>
          ((openModuleCohomologyRestriction W.toScheme.toRingedSpace p (homOfLE le_sup_left)).app
          F x, (openModuleCohomologyRestriction W.toScheme.toRingedSpace p (homOfLE
          le_sup_right)).app F x)) (fun x : (openModuleCohomology W.toScheme.toRingedSpace p
          U).obj F × (openModuleCohomology W.toScheme.toRingedSpace p V).obj F =>
          (openModuleCohomologyRestriction W.toScheme.toRingedSpace p (homOfLE inf_le_left)).app F
          x.1 - (openModuleCohomologyRestriction W.toScheme.toRingedSpace p (homOfLE
          inf_le_right)).app F x.2) ∧
        Function.Exact (fun x : (openModuleCohomology W.toScheme.toRingedSpace p U).obj F ×
          (openModuleCohomology W.toScheme.toRingedSpace p V).obj F =>
          (openModuleCohomologyRestriction W.toScheme.toRingedSpace p (homOfLE inf_le_left)).app F
          x.1 - (openModuleCohomologyRestriction W.toScheme.toRingedSpace p (homOfLE
          inf_le_right)).app F x.2) (δ F U V p) ∧
        Function.Exact (δ F U V p) (fun x : (openModuleCohomology W.toScheme.toRingedSpace (p + 1)
          (U ⊔ V)).obj F => ((openModuleCohomologyRestriction W.toScheme.toRingedSpace (p + 1)
          (homOfLE le_sup_left)).app F x, (openModuleCohomologyRestriction
          W.toScheme.toRingedSpace (p + 1) (homOfLE le_sup_right)).app F x))) ∧
      (∀ (F : SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) [F.IsQuasicoherent]
        (G : SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) [G.IsQuasicoherent]
        (f : F ⟶ G) (U V : Opens W.toScheme) (p : ℕ),
        δ F U V p ≫ (openModuleCohomology W.toScheme.toRingedSpace (p + 1) (U ⊔ V)).map f =
          (openModuleCohomology W.toScheme.toRingedSpace p (U ⊓ V)).map f ≫ δ G U V p) ∧
      (∀ (F : SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) [F.IsQuasicoherent]
        (U V : Opens W.toScheme) (T : Opens W.toScheme) (p : ℕ),
        δ F U V p ≫ (openModuleCohomologyRestriction W.toScheme.toRingedSpace (p + 1) (homOfLE
          (sup_le_sup inf_le_left inf_le_left))).app F =
          (openModuleCohomologyRestriction W.toScheme.toRingedSpace p (homOfLE (inf_le_inf
          inf_le_left inf_le_left))).app F ≫
            δ F (U ⊓ T) (V ⊓ T) p) := by
  sorry

end AlgebraicGeometry.Scheme
