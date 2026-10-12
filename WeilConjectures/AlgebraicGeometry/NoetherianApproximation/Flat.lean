/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
public import WeilConjectures.RingTheory.Flat.NoetherianApproximation

/-!
# Flatness over the base descends to a finite stage

Let `V` be an affine scheme, written as the limit of the spectra of the finitely generated
subrings of `Γ(V, ⊤)` (`AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine`). Let
`p : Y ⟶ Spec Aᵢ` be quasi-compact and of finite presentation over one of the stages and `𝒢` a
module of finite presentation on `Y`. If the pullback of `𝒢` to `Y ×_{Spec Aᵢ} V` is flat over
`V`, then the pullback of `𝒢` to `Y ×_{Spec Aᵢ} Spec Aⱼ` is flat over `Spec Aⱼ` for all
sufficiently large stages `Aⱼ` (EGA IV₃, 11.2.6; Stacks, Tag 00R6).

The algebraic input is `Module.exists_fg_forall_flat_baseChange`, applied to the global sections
of `𝒢` over the members of a finite affine open cover of `Y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.NoetherianApproximation

/-- **Flatness over the base descends to a finite stage** (EGA IV₃, 11.2.6). Let `V` be affine,
`p : Y ⟶ Spec Aᵢ` quasi-compact, quasi-separated and locally of finite presentation over a stage
of the Noetherian approximation `ofIsAffine V` of `V`, and `𝒢` a module of finite presentation on
`Y` whose pullback to `Y ×_{Spec Aᵢ} V` is flat over `V`. Then for some stage `j ⟶ i`, and every
later stage `k`, the pullback of `𝒢` to `Y ×_{Spec Aᵢ} Spec Aₖ` is flat over `Spec Aₖ`. -/
theorem Scheme.Modules.exists_isFlatOver_pullback_ofIsAffine (V : Scheme.{u}) [IsAffine V]
    {i : (ofIsAffine V).I} {Y : Scheme.{u}} (p : Y ⟶ (ofIsAffine V).D.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p] (𝒢 : Y.Modules)
    [𝒢.IsFinitePresentation]
    (h𝒢 : ((Modules.pullback (pullback.fst p ((ofIsAffine V).π.app i))).obj 𝒢).IsFlatOver
      (pullback.snd p ((ofIsAffine V).π.app i))) :
    ∃ (j : (ofIsAffine V).I) (f : j ⟶ i), ∀ (k : (ofIsAffine V).I) (g : k ⟶ j),
      ((Modules.pullback (pullback.fst p ((ofIsAffine V).D.map (g ≫ f)))).obj 𝒢).IsFlatOver
        (pullback.snd p ((ofIsAffine V).D.map (g ≫ f))) :=
  sorry

end AlgebraicGeometry
