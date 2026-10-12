/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafTrivialTopIso

/-!
# Invertibility of the top exterior power

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: lem-sc-exterior-sheaf-top-invertible).
-/

@[expose] public section

universe v

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- The top exterior power of a constant-rank finite locally free sheaf is invertible.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: lem-sc-exterior-sheaf-top-invertible).

Proof: Choose a cover trivializing `M` with `r` basis sections. On every subopen of
such a chart the basis identifies the module of sections with a free module of rank `r`.
Its top exterior power has the single basis vector given by the wedge of all basis
sections, by `Module.Basis.exteriorPower`. These rank-one identifications commute
with restriction, since the restrictions of the chosen basis sections are the basis
sections on the smaller open. Thus the sectionwise exterior-power presheaf is locally
isomorphic to the structure sheaf; sheafification preserves these identifications.
Each point thus has an open neighbourhood on which the determinant restricts to the
structure sheaf, which is precisely scheme-module invertibility.
For `r = 0` the basis wedge is the empty wedge and the identification is
`exteriorSheaf_zero_iso`. No assumption on nonemptiness of the scheme or on its
characteristic is used. -/
theorem exteriorSheaf_top_isInvertible {X : Scheme.{v}} (M : X.Modules) (r : ℕ)
    [M.IsFiniteLocallyFreeOfRank r] :
    AlgebraicGeometry.Scheme.Modules.IsInvertible (exteriorSheaf M r) := by
  obtain ⟨ι, U, hU, h⟩ := IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := r)
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := by
    have hx : x ∈ (⨆ i, U i) := by rw [hU]; trivial
    simpa only [TopologicalSpace.Opens.mem_iSup] using hx
  obtain ⟨e⟩ := h i
  obtain ⟨p⟩ := exteriorSheaf_trivial_top_presheaf_iso (M.restrict (U i).ι) r e
  let s := (PresheafOfModules.sheafification (𝟙 (U i).toScheme.ringCatSheaf.obj)).mapIso p
  let c := (asIso (PresheafOfModules.sheafificationAdjunction.{v}
    (𝟙 (U i).toScheme.ringCatSheaf.obj)).counit).app
      (SheafOfModules.unit.{v} (U i).toScheme.ringCatSheaf)
  exact ⟨U i, hi, ⟨((restrictFunctorIsoPullback (U i).ι).app _).symm ≪≫
    (exteriorSheaf_restrict_iso M r (U i)).some ≪≫ s ≪≫ c⟩⟩

end AlgebraicGeometry.Scheme.Modules
