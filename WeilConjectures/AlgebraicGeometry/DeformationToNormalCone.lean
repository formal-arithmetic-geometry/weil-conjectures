/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Compactification.StrictTransform

/-!
# Deformation to the normal cone of a section

For a morphism `g : V ⟶ B` with a closed section `s : B ⟶ V`, the *deformation to the normal
cone of the section* is

`𝒟_s V = Bl_{s(B) × {0}} (V ×_B 𝔸¹_B) ∖ (strict transform of V ×_B {0})`,

the blow-up of `V ×_B 𝔸¹_B` along `s(B) × {0}` with the strict transform of the fibre over
`t = 0` removed (blueprint `def-pur-dnc-section-family`). It carries a morphism
`g̃ : 𝒟_s V ⟶ 𝔸¹_B` with a section `s̃ : 𝔸¹_B ⟶ 𝒟_s V`; the fibre of `(g̃, s̃)` over `t = 1` is
`(g, s)` and the fibre over `t = 0` is the normal bundle `(π_N, 0_N)` of the section, so the
deformation interpolates between a smooth morphism with a section and a vector bundle with
its zero section.

Equivalently `𝒟_s V = Spec_V (⨁_{r ∈ ℤ} I_s^r t^{-r})` is the extended Rees construction, with
`I_s^r = 𝒪_V` for `r ≤ 0`: it is the `t`-chart of the blow-up.

## Implementation notes

The deformation space is constructed as in the blueprint, from the blow-up
`AlgebraicGeometry.Scheme.IdealSheafData.blowup` of the ideal sheaf of the centre and the
strict transform `AlgebraicGeometry.Scheme.IdealSheafData.strictTransform` of the closed fibre.

As in the blueprint (`def-pur-normal-bundle`), the normal bundle `N_s` of the section is
*defined* as the fibre of `g̃` over `t = 0`, so the cartesian square at `t = 0` holds by
construction. That `N_s` is the normal cone `Spec_B (⨁_{r ≥ 0} I^r/I^{r+1})`, a vector bundle
of rank `d`, is part of `sk-lem-geometry` (1); since Mathlib has neither relative `Spec` nor
vector bundles over a scheme, only its consequence that `N_s ⟶ B` is smooth of relative
dimension `d` is stated
(`AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_sectionNormalConeProj`).

The section `s̃` is obtained from the universal property of the blow-up: the centre pulls back
along `s × 𝟙 : 𝔸¹_B ⟶ V ×_B 𝔸¹_B` to the ideal `(t)`, which is invertible, and the lift misses
the strict transform. Both facts are recorded as the existence statement
`AlgebraicGeometry.Scheme.Hom.exists_deformationSection`, and `s̃` is the choice it provides.

The punctured trivialisation (3), the standard pair (4) and base change and étale
localization (5) of `sk-lem-geometry` are stated in
`WeilConjectures.AlgebraicGeometry.DeformationToNormalCone.Local`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.deformationAmbient`: `V ×_B 𝔸¹_B`.
- `AlgebraicGeometry.Scheme.Hom.deformationCenter`: the centre `s × 0 : B ⟶ V ×_B 𝔸¹_B`.
- `AlgebraicGeometry.Scheme.Hom.deformationClosedFibre`: `𝟙 × 0 : V ⟶ V ×_B 𝔸¹_B`.
- `AlgebraicGeometry.Scheme.Hom.deformationSpace`: the deformation space `𝒟_s V`.
- `AlgebraicGeometry.Scheme.Hom.deformationProj`: `g̃ : 𝒟_s V ⟶ 𝔸¹_B`.
- `AlgebraicGeometry.Scheme.Hom.deformationSection`: `s̃ : 𝔸¹_B ⟶ 𝒟_s V`.
- `AlgebraicGeometry.Scheme.Hom.sectionNormalCone`: the normal bundle `N_s`, the fibre of `g̃`
  over `t = 0`, with its projection `sectionNormalConeProj` and zero section
  `sectionNormalConeZero`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_deformationSection`
- `AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_deformationProj`
- `AlgebraicGeometry.Scheme.Hom.exists_isPullback_deformationOneFibre`
- `AlgebraicGeometry.Scheme.Hom.isPullback_sectionNormalCone`
- `AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_sectionNormalConeProj`
- `AlgebraicGeometry.Scheme.Hom.isClosedImmersion_sectionNormalConeZero`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {V B : Scheme.{u}}

namespace Scheme.Hom

variable (g : V ⟶ B)

/-- The scheme `V ×_B 𝔸¹_B` that is blown up to form the deformation to the normal cone. -/
noncomputable abbrev deformationAmbient : Scheme.{u} :=
  pullback g (𝔸(ULift.{u} (Fin 1); B) ↘ B)

/-- The closed fibre `𝟙 × 0 : V ⟶ V ×_B 𝔸¹_B` over `t = 0`, whose strict transform is removed
from the blow-up. -/
noncomputable def deformationClosedFibre : V ⟶ deformationAmbient g :=
  pullback.lift (𝟙 V) (g ≫ AffineSpace.zeroSection (ULift.{u} (Fin 1)) B) (by
    rw [Category.assoc, AffineSpace.zeroSection_over, Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
lemma deformationClosedFibre_fst : deformationClosedFibre g ≫ pullback.fst _ _ = 𝟙 V :=
  pullback.lift_fst _ _ _

instance : IsClosedImmersion (deformationClosedFibre g) := by
  have : IsClosedImmersion (deformationClosedFibre g ≫ pullback.fst _ _) := by
    rw [deformationClosedFibre_fst]; infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst _ _)

variable (s : B ⟶ V) (hs : s ≫ g = 𝟙 B)

/-- The centre `s × 0 : B ⟶ V ×_B 𝔸¹_B` of the blow-up: the section `s` placed in the fibre
over `t = 0`. -/
noncomputable def deformationCenter : B ⟶ deformationAmbient g :=
  pullback.lift s (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B) (by
    rw [hs, AffineSpace.zeroSection_over])

@[reassoc (attr := simp)]
lemma deformationCenter_fst : deformationCenter g s hs ≫ pullback.fst _ _ = s :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma deformationCenter_snd :
    deformationCenter g s hs ≫ pullback.snd _ _ = AffineSpace.zeroSection (ULift.{u} (Fin 1)) B :=
  pullback.lift_snd _ _ _

instance [IsClosedImmersion s] : IsClosedImmersion (deformationCenter g s hs) := by
  have : IsClosedImmersion (deformationCenter g s hs ≫ pullback.fst _ _) := by
    rw [deformationCenter_fst]; infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst _ _)

/-- The ideal sheaf of the centre `s(B) × {0}` on `V ×_B 𝔸¹_B`. -/
noncomputable def deformationCenterIdeal [IsClosedImmersion s] :
    (deformationAmbient g).IdealSheafData :=
  (deformationCenter g s hs).ker

/-- The open complement, in the blow-up of `V ×_B 𝔸¹_B` along the centre, of the strict
transform of the closed fibre `V ×_B {0}`. -/
noncomputable def deformationOpen [IsClosedImmersion s] :
    (deformationCenterIdeal g s hs).blowup.Opens :=
  ⟨(Set.range (strictTransformMap (deformationClosedFibre g)
      (deformationCenterIdeal g s hs).blowupMap
      (deformationCenterIdeal g s hs).support.compl).base)ᶜ,
    (strictTransformMap (deformationClosedFibre g) (deformationCenterIdeal g s hs).blowupMap
      (deformationCenterIdeal g s hs).support.compl).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- Blueprint `sk-def-purity-conv` (`def-pur-dnc-section-family`): the deformation to the
normal cone of the section `s`,

`𝒟_s V = Bl_{s(B) × {0}} (V ×_B 𝔸¹_B) ∖ (strict transform of V ×_B {0})`. -/
noncomputable def deformationSpace [IsClosedImmersion s] : Scheme.{u} :=
  (deformationOpen g s hs).toScheme

/-- The structure morphism `g̃ : 𝒟_s V ⟶ 𝔸¹_B`: the inclusion into the blow-up, the blow-up
map, and the projection `V ×_B 𝔸¹_B ⟶ 𝔸¹_B`. -/
noncomputable def deformationProj [IsClosedImmersion s] :
    deformationSpace g s hs ⟶ 𝔸(ULift.{u} (Fin 1); B) :=
  (deformationOpen g s hs).ι ≫ (deformationCenterIdeal g s hs).blowupMap ≫ pullback.snd _ _

/-- The section `s × 𝟙 : 𝔸¹_B ⟶ V ×_B 𝔸¹_B` of the projection to `𝔸¹_B`, which the section
`s̃` of the deformation lifts. -/
noncomputable def deformationSectionAmbient :
    𝔸(ULift.{u} (Fin 1); B) ⟶ deformationAmbient g :=
  pullback.lift ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ s) (𝟙 _) (by
    rw [Category.assoc, hs, Category.comp_id, Category.id_comp])

/-- Blueprint `sk-def-purity-conv` (`def-pur-dnc-section-family`): the section `s̃` exists.

The centre pulls back along `s × 𝟙 : 𝔸¹_B ⟶ V ×_B 𝔸¹_B` to the ideal `(t)` of the zero section
of `𝔸¹_B`, which is invertible, so `s × 𝟙` lifts to the blow-up by its universal property
(`AlgebraicGeometry.Scheme.IdealSheafData.exists_lift_blowup`); the lift misses the strict
transform of `V ×_B {0}`, so it lands in `𝒟_s V`, and it is a section of `g̃`. -/
theorem exists_deformationSection [IsClosedImmersion s] :
    ∃ σ : 𝔸(ULift.{u} (Fin 1); B) ⟶ deformationSpace g s hs,
      σ ≫ deformationProj g s hs = 𝟙 _ ∧
        σ ≫ (deformationOpen g s hs).ι ≫ (deformationCenterIdeal g s hs).blowupMap =
          deformationSectionAmbient g s hs :=
  sorry

/-- The section `s̃ : 𝔸¹_B ⟶ 𝒟_s V` of `g̃`, lifting `s × 𝟙`. -/
noncomputable def deformationSection [IsClosedImmersion s] :
    𝔸(ULift.{u} (Fin 1); B) ⟶ deformationSpace g s hs :=
  (exists_deformationSection g s hs).choose

@[reassoc (attr := simp)]
lemma deformationSection_proj [IsClosedImmersion s] :
    deformationSection g s hs ≫ deformationProj g s hs = 𝟙 _ :=
  (exists_deformationSection g s hs).choose_spec.1

/-- Blueprint `sk-def-purity-conv` (`def-pur-normal-bundle`): the normal bundle `N_s` of the
section `s`, the fibre of `g̃ : 𝒟_s V ⟶ 𝔸¹_B` over the zero section `t = 0`. That it is the
normal cone `Spec_B (⨁_{r ≥ 0} I^r/I^{r+1})` is `sk-lem-geometry` (1). -/
noncomputable def sectionNormalCone [IsClosedImmersion s] : Scheme.{u} :=
  pullback (deformationProj g s hs) (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)

/-- The projection `π_N : N_s ⟶ B`. -/
noncomputable def sectionNormalConeProj [IsClosedImmersion s] : sectionNormalCone g s hs ⟶ B :=
  pullback.snd _ _

/-- The inclusion `ι₀ : N_s ⟶ 𝒟_s V` of the fibre over `t = 0`. -/
noncomputable def sectionNormalConeι [IsClosedImmersion s] :
    sectionNormalCone g s hs ⟶ deformationSpace g s hs :=
  pullback.fst _ _

/-- The zero section `0_N : B ⟶ N_s`: the restriction of `s̃` to `t = 0`. -/
noncomputable def sectionNormalConeZero [IsClosedImmersion s] : B ⟶ sectionNormalCone g s hs :=
  pullback.lift (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B ≫ deformationSection g s hs)
    (𝟙 B) (by rw [Category.assoc, deformationSection_proj, Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
lemma sectionNormalConeZero_proj [IsClosedImmersion s] :
    sectionNormalConeZero g s hs ≫ sectionNormalConeProj g s hs = 𝟙 B :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma sectionNormalConeZero_ι [IsClosedImmersion s] :
    sectionNormalConeZero g s hs ≫ sectionNormalConeι g s hs =
      AffineSpace.zeroSection (ULift.{u} (Fin 1)) B ≫ deformationSection g s hs :=
  pullback.lift_fst _ _ _

/-- Blueprint `sk-lem-geometry`: Geometry of the deformation of a section

*The fibre over `t = 0`* (clause (1)). The square

```
  N_s ---ι₀---> 𝒟_s V
   |              |
  π_N             g̃
   v              v
   B  ---i₀---> 𝔸¹_B
```

is cartesian, and `ι₀` carries the zero section `0_N` to `s̃`
(`AlgebraicGeometry.Scheme.Hom.sectionNormalConeZero_ι`). Both hold by the definition of `N_s`.
-/
theorem isPullback_sectionNormalCone [IsClosedImmersion s] :
    IsPullback (sectionNormalConeι g s hs) (sectionNormalConeProj g s hs)
      (deformationProj g s hs) (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B) :=
  IsPullback.of_hasPullback _ _

/-- Blueprint `sk-lem-geometry`: Geometry of the deformation of a section

*The fibre over `t = 1`* (clause (1)). There is `ι₁ : V ⟶ 𝒟_s V` making

```
  V ---ι₁---> 𝒟_s V
  |             |
  g             g̃
  v             v
  B ---i₁---> 𝔸¹_B
```

cartesian and carrying `s` to `s̃`. Away from `t = 0` the blow-up is an isomorphism
(`AlgebraicGeometry.Scheme.IdealSheafData.isIso_blowupMap_restrict_support_compl`) and the
strict transform of `V ×_B {0}` lies over `t = 0`, so the fibre of `g̃` over `t = 1` is that of
`V ×_B 𝔸¹_B ⟶ 𝔸¹_B`, which is `V`. -/
theorem exists_isPullback_deformationOneFibre [IsClosedImmersion s] :
    ∃ ι₁ : V ⟶ deformationSpace g s hs,
      IsPullback ι₁ g (deformationProj g s hs) (AffineSpace.oneSection (ULift.{u} (Fin 1)) B) ∧
        s ≫ ι₁ = AffineSpace.oneSection (ULift.{u} (Fin 1)) B ≫ deformationSection g s hs :=
  sorry

/-- Blueprint `sk-lem-geometry`: Geometry of the deformation of a section

*Smoothness of the family* (clause (2)). If `g` is smooth of pure relative dimension `d`, so is
`g̃ : 𝒟_s V ⟶ 𝔸¹_B`: étale-locally there are relative coordinates `x₁, …, x_d` on `V` in which
`s` is `x_i = 0`, and on the deformation chart `u_i = x_i / t` the deformation space is
`𝔸^d × 𝔸¹` over the base, with `g̃` the last projection. -/
theorem smoothOfRelativeDimension_deformationProj (d : ℕ) [SmoothOfRelativeDimension d g]
    [IsClosedImmersion s] : SmoothOfRelativeDimension d (deformationProj g s hs) :=
  sorry

/-- Blueprint `sk-lem-geometry`: Geometry of the deformation of a section

*The normal bundle is a vector bundle of rank `d`*, in the form expressible here: if `g` is
smooth of pure relative dimension `d`, then `π_N : N_s ⟶ B` is smooth of relative dimension
`d`. It is the base change of `g̃` along the zero section of `𝔸¹_B`, so this follows from
`AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_deformationProj`. The blueprint states
more, that `N_s` is a vector bundle of rank `d` (`sk-lem-geometry` (1)), which is not expressible
here. -/
theorem smoothOfRelativeDimension_sectionNormalConeProj (d : ℕ) [SmoothOfRelativeDimension d g]
    [IsClosedImmersion s] : SmoothOfRelativeDimension d (sectionNormalConeProj g s hs) :=
  sorry

/-- Blueprint `sk-def-purity-conv` (`def-pur-normal-bundle`): the zero section `0_N` of the
normal bundle is a closed immersion. -/
theorem isClosedImmersion_sectionNormalConeZero [IsClosedImmersion s] :
    IsClosedImmersion (sectionNormalConeZero g s hs) :=
  sorry

end Scheme.Hom

end AlgebraicGeometry
