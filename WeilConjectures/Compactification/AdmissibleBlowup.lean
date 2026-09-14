/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict

/-!

# Transport of a compactification along an admissible blow-up

A compactification `f = i ≫ g` can be transported along any blow-up of the ambient scheme
which is admissible for the open `i.opensRange`: such a blow-up is an isomorphism over that
open, so the open immersion `i` lifts uniquely through it.

```
        (c.admissibleBlowup B).i
   X ──────────────────────────→ B.I.blowup
    ╲                            │
 c.i ╲                           │ B.I.blowupMap
      ↘                          ↓
                                c.Z
```

## Main definitions

- `AlgebraicGeometry.Compactification.admissibleBlowup`: the transported compactification, with
  ambient scheme the blow-up and structure morphism `B.I.blowupMap ≫ c.g`.

## Main results

- `AlgebraicGeometry.Compactification.admissibleBlowup_opensRange_i`: the copy of `X` in the
  blow-up is the full inverse image of the copy of `X` in `c.Z`;
- `AlgebraicGeometry.Compactification.admissibleBlowup_image_preimage`: images of subsets of `X`
  in the blow-up are the full inverse images of their images in `c.Z`.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Compactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  (B : IsAdmissible c.Z c.i.opensRange)

/-- **Transport of a compactification along an admissible blow-up of the ambient scheme**: the
blow-up is proper and an isomorphism over the copy of `X`, so the open immersion `c.i` lifts
uniquely to the blow-up (`AlgebraicGeometry.liftOfIsIsoRestrict`), and the composite of the
blow-up with the structure morphism is again proper. -/
def admissibleBlowup : Compactification f :=
  letI := B.isProper_blowupMap
  letI := B.isIso_blowupMap_restrict
  { Z := B.I.blowup
    g := B.I.blowupMap ≫ c.g
    i := liftOfIsIsoRestrict B.I.blowupMap c.i
    comm := by
      rw [← Category.assoc, liftOfIsIsoRestrict_comp]
      exact c.comm
    isProper := inferInstance
    isOpenImmersion := inferInstance }

@[simp]
lemma admissibleBlowup_Z : (c.admissibleBlowup B).Z = B.I.blowup := rfl

@[simp]
lemma admissibleBlowup_g : (c.admissibleBlowup B).g = B.I.blowupMap ≫ c.g := rfl

/-- The copy of `X` in the blow-up lies over the copy of `X` in the original ambient scheme;
this determines it, by uniqueness of the lift (`AlgebraicGeometry.eq_liftOfIsIsoRestrict`). -/
@[reassoc (attr := simp)]
lemma admissibleBlowup_i_comp : (c.admissibleBlowup B).i ≫ B.I.blowupMap = c.i :=
  letI := B.isIso_blowupMap_restrict
  liftOfIsIsoRestrict_comp _ _

/-- **The copy of `X` in the blow-up is the full inverse image of the copy of `X`**: the
blow-up is an isomorphism over the latter. -/
@[simp]
lemma admissibleBlowup_opensRange_i :
    (c.admissibleBlowup B).i.opensRange = B.I.blowupMap ⁻¹ᵁ c.i.opensRange :=
  letI := B.isIso_blowupMap_restrict
  opensRange_eq_preimage_opensRange_of_comp_eq B.I.blowupMap _ (c.admissibleBlowup_i_comp B)

/-- **Images in the blow-up are full inverse images of images**: the image in the blow-up of a
subset `A` of `X` is the inverse image under the blow-up of the image of `A` in the original
ambient scheme. -/
lemma admissibleBlowup_image_preimage (A : Set X) :
    (c.admissibleBlowup B).i '' A = B.I.blowupMap ⁻¹' (c.i '' A) :=
  letI := B.isIso_blowupMap_restrict
  image_eq_preimage_image_of_comp_eq B.I.blowupMap _ (c.admissibleBlowup_i_comp B) A

end AlgebraicGeometry.Compactification
