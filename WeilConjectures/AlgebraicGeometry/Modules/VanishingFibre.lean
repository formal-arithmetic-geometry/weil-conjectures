/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Fiber
public import WeilConjectures.AlgebraicGeometry.Modules.VanishingPullback

/-!
# Vanishing of a section of a line bundle is vanishing in the fibre

The project has two spellings for "the global section `s` of a sheaf of `𝒪ₓ`-modules `F` does
not vanish at `x`": the germ of `s` at `x` is outside `𝔪ₓ Fₓ`
(`AlgebraicGeometry.Scheme.Modules.VanishesAt`), and the image of `s` in the fibre `F(x)` is
non-zero (`AlgebraicGeometry.Scheme.Modules.fiberMk`). This file proves that for an
**invertible** `F` the two agree.

The comparison `F(x) ≅ Fₓ / 𝔪ₓ Fₓ` which would settle this for an arbitrary `F` is available
neither here nor in Mathlib. For an invertible `L` it can be bypassed: both sides are local at
`x` and invariant under isomorphism, so one may restrict to an open subset over which `L` is
trivial and there read both off from the structure sheaf, where vanishing is the complement of
a basic open subset (`AlgebraicGeometry.Scheme.Modules.vanishesAt_structureModules_iff`) and the
fibre is the residue field
(`AlgebraicGeometry.Scheme.Modules.fiberMk_unit_eq_zero_iff`).

## Main results

- `AlgebraicGeometry.Scheme.Modules.vanishesAt_iff_fiberMk_eq_zero_of_isoUnit`: the two
  spellings agree for a trivial sheaf of modules.
- `AlgebraicGeometry.Scheme.Modules.vanishesAt_iff_fiberMk_eq_zero`: **the two spellings agree
  for an invertible sheaf of modules.**
-/

@[expose] public section

universe u

open CategoryTheory Opposite SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **Vanishing of a section of a trivial sheaf of modules is vanishing in the fibre.** Through
an isomorphism `M ≅ 𝒪ₓ` both sides become the vanishing of the corresponding global function,
namely the complement of its basic open subset. -/
theorem vanishesAt_iff_fiberMk_eq_zero_of_isoUnit {M : X.Modules} (e : M ≅ unit X.ringCatSheaf)
    (t : Γ(M, ⊤)) (x : X) : M.VanishesAt t x ↔ fiberMk M x t = 0 := by
  have hfib : fiberMk M x t = 0 ↔ fiberMk (unit X.ringCatSheaf) x (Hom.app e.hom ⊤ t) = 0 := by
    rw [← fiberMap_fiberMk e.hom x t]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [h]
      simp
    · have hinj : Function.Injective (fiberMap e.hom x) :=
        ((ConcreteCategory.isIso_iff_bijective (fiberMap e.hom x)).1 inferInstance).1
      exact hinj (h.trans (map_zero _).symm)
  rw [← vanishesAt_iff_of_iso e t x, vanishesAt_structureModules_iff, hfib,
    fiberMk_unit_eq_zero_iff, Scheme.Γevaluation_eq_zero_iff_notMem_basicOpen]

/-- **Vanishing of a section of a line bundle is vanishing in the fibre.** For an invertible
sheaf of `𝒪ₓ`-modules `L`, a global section `s` vanishes at `x` in the sense of
`AlgebraicGeometry.Scheme.Modules.VanishesAt` exactly when its image in the fibre `L(x)` is
zero.

Both sides are compatible with restriction to an open neighbourhood of `x`, by
`AlgebraicGeometry.Scheme.Modules.vanishesAt_sectionsPullback_iff_of_isOpenImmersion` and
`AlgebraicGeometry.Scheme.Modules.fiberMk_sectionsPullback_eq_zero_iff`, so the statement follows
from the trivial case on an open subset over which `L` is trivial. -/
theorem vanishesAt_iff_fiberMk_eq_zero {L : X.Modules} (hL : L.Invertible) (s : Γ(L, ⊤))
    (x : X) : L.VanishesAt s x ↔ fiberMk L x s = 0 := by
  obtain ⟨W, hxW, ⟨e⟩⟩ := hL.exists_restrict_iso_unit x
  let y : W.toScheme := ⟨x, hxW⟩
  have e' : (pullback W.ι).obj L ≅ unit W.toScheme.ringCatSheaf :=
    ((restrictFunctorIsoPullback W.ι).app L).symm ≪≫ e
  refine Iff.trans ?_ (fiberMk_sectionsPullback_eq_zero_iff W.ι y L s)
  refine Iff.trans ?_ (vanishesAt_iff_fiberMk_eq_zero_of_isoUnit e' _ y)
  exact (vanishesAt_sectionsPullback_iff_of_isOpenImmersion W.ι L s y).symm

/-- **A section of a line bundle vanishes nowhere exactly when it is non-zero in every
fibre.** -/
theorem forall_not_vanishesAt_iff_forall_fiberMk_ne_zero {L : X.Modules} (hL : L.Invertible)
    (s : Γ(L, ⊤)) : (∀ x : X, ¬ L.VanishesAt s x) ↔ ∀ x : X, fiberMk L x s ≠ 0 :=
  forall_congr' fun x ↦ (vanishesAt_iff_fiberMk_eq_zero hL s x).not

end AlgebraicGeometry.Scheme.Modules
