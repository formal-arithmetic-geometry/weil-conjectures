/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Affine.BaseChange
public import WeilConjectures.Blowup.Extension
public import WeilConjectures.Blowup.Principalization
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-!

# The blow-up of a pulled-back ideal is a closed subscheme of the base change

For a morphism of schemes `f : Y ⟶ X` and an ideal sheaf `I` on `X`, the blow-up of the
pulled-back ideal `I.comap f` maps to the fibre product `Y ×_X Bl_I(X)` via its
structure morphism and any lift `ρ : Bl_{I·O_Y}(Y) ⟶ Bl_I(X)` provided by the
universal property of the blow-up (Stacks Project Tag 0806; such a lift exists because
the pullback of `I` to `Bl_{I·O_Y}(Y)` is the invertible exceptional ideal, and it is
unique). We show that this canonical morphism is a **closed immersion** — the global
closed-immersion half of Stacks Project Tag 080E; the identification of its image with
the strict transform is in `WeilConjectures.Compactification.StrictTransformBlowup`.

The proof reduces to the affine case
`AlgebraicGeometry.AffineBlowup.isClosedImmersion_pullbackLift` over the opens of
`Y ×_X Bl_I(X)` spanned by an affine open `V ⊆ Y` lying over an affine open `U ⊆ X`
and the blow-up chart of `Bl_I(X)` over `U`, using that being a closed immersion is
Zariski-local on the target.

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap`

## Blueprint

Part of `thm:nagata-strict-transform-is-blowup` (Stacks Project Tag 080E),
closed-immersion half.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- **The blow-up of a pulled-back ideal is a closed subscheme of the base-changed
blow-up** (Stacks Project Tag 080E, closed-immersion half; blueprint:
`thm:nagata-strict-transform-is-blowup`): for `f : Y ⟶ X`, an ideal sheaf `I` on `X`
and a lift `ρ` of `(I.comap f).blowupMap ≫ f` along `I.blowupMap` — provided by the
universal property of the blow-up, since the pullback of `I` to the blow-up of
`I.comap f` is the invertible exceptional ideal — the induced morphism
`Bl_{I·O_Y}(Y) ⟶ Y ×_X Bl_I(X)` is a closed immersion. -/
theorem isClosedImmersion_pullbackLift_blowup_comap (I : X.IdealSheafData) (f : Y ⟶ X)
    {ρ : (I.comap f).blowup ⟶ I.blowup}
    (hρ : (I.comap f).blowupMap ≫ f = ρ ≫ I.blowupMap) :
    IsClosedImmersion (pullback.lift (I.comap f).blowupMap ρ hρ) := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
