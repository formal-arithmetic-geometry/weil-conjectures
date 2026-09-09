/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!

# Transport of scheme-theoretic images through admissible blow-ups

This file records the transport of scheme-theoretic images through an admissible blow-up
(Stacks Project Tag 0F3Y; blueprint `lemma:nagata-scheme-image-strict-transform`; proof
order item 31):

- `AlgebraicGeometry.IsAdmissible.blowupBaseChange` and
  `AlgebraicGeometry.IsAdmissible.preservedOpenPullback`: the base change
  `X' ×_S Y ⟶ X ×_S Y` of a `U`-admissible blow-up along the first projection, and the
  open of `X ×_S Y` over which it is an isomorphism, both of which appear in the
  statement below;
- `AlgebraicGeometry.ker_eq_ker_strictTransformMap_of_isAdmissible`: the scheme-theoretic
  image of a lift along a `U`-admissible blow-up is the strict transform of the
  scheme-theoretic image.

It is the input the graph-extension step (Stacks Project Tag 0F3Z) uses.

The theorem is the specialization to admissible blow-ups of
`AlgebraicGeometry.ker_eq_ker_strictTransformMap`: the base-changed blow-up
`B.blowupBaseChange f g : X' ×_S Y ⟶ X ×_S Y` is an isomorphism over the open
`B.preservedOpenPullback f g` of `X ×_S Y`, which contains the range of `h`. In
particular the lift `h'` exists and is unique: it is
`AlgebraicGeometry.Scheme.Hom.liftOfIsIsoRestrict` of the base-changed blow-up.

Differences from the informal statement. The two closed subschemes of `X' ×_S Y` are
recorded by the kernels of the corresponding closed immersions, so the statement is in
kernel ideal sheaf form. The Stacks Project and the blueprint also assume `h`
quasi-separated; Mathlib's kernel ideal sheaf theory only needs quasi-compactness, so
that hypothesis is dropped here. Conversely the right-hand side is a strict transform,
so the finiteness data of `WeilConjectures.Compactification.StrictTransform` is needed:
quasi-separatedness of `SIm(h) ×_{X ×_S Y} (X' ×_S Y)` and quasi-compactness of the
preserved open of `X ×_S Y`, which together discharge the standing quasi-compactness
assumption of the strict-transform comparison API.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace IsAdmissible

variable {X : Scheme.{u}} {U : X.Opens} (B : IsAdmissible X U) {S Y : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S)

/-- The base change of a `U`-admissible blow-up along the first projection of a fibre
product: the morphism `X' ×_S Y ⟶ X ×_S Y` induced by `B.I.blowupMap : X' ⟶ X`. -/
abbrev blowupBaseChange : pullback (B.I.blowupMap ≫ f) g ⟶ pullback f g :=
  pullbackCompFstMap f g B.I.blowupMap

/-- The preimage of the preserved open under the first projection of a fibre product:
the open of `X ×_S Y` over which the base-changed blow-up is an isomorphism. -/
abbrev preservedOpenPullback : (pullback f g).Opens :=
  pullback.fst f g ⁻¹ᵁ B.preservedOpen

/-- **The base-changed blow-up is an isomorphism over the preserved open**: the blow-up
is an isomorphism over the complement of its center, and this persists under the base
change along the first projection. -/
instance isIso_blowupBaseChange_restrict :
    IsIso (B.blowupBaseChange f g ∣_ B.preservedOpenPullback f g) :=
  have := B.I.isIso_blowupMap_restrict_support_compl
  isIso_morphismRestrict_of_isPullback
    (isPullback_pullbackCompFstMap f g B.I.blowupMap) B.preservedOpen

end IsAdmissible

variable {S X Y V : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

/-- **Scheme-theoretic images and admissible blow-ups** (Stacks Project Tag 0F3Y;
blueprint: `lemma:nagata-scheme-image-strict-transform`; proof order item 31): if
`h : V ⟶ X ×_S Y` is quasi-compact and its first projection lands in the open `U ⊆ X`,
and `h'` is a lift of `h` along the base change `ρ` of a `U`-admissible blow-up `π`,
then the scheme-theoretic image of `h'` is the strict transform of the scheme-theoretic
image of `h`.

```
                V
           h' ↙   ↘ h
            ↙       ↘
    X' ×_S Y --ρ--> X ×_S Y
        |               |
        ↓               ↓
        X' ---- π ----> X
```

Here `π = B.I.blowupMap` and `ρ = B.blowupBaseChange f g`, and both scheme-theoretic
images are recorded by their kernel ideal sheaves.

Both kernels are ideal sheaves on the same scheme `X' ×_S Y`, since `h'` and the
strict-transform projection share that codomain. So the conclusion says that the two
scheme-theoretic images are *equal as closed subschemes of* `X' ×_S Y`, with the same
inclusion morphism into it, and not merely that they are isomorphic schemes; see the
discussion in the docstring of
`AlgebraicGeometry.ker_eq_ker_strictTransformMap`. -/
theorem ker_eq_ker_strictTransformMap_of_isAdmissible {U : X.Opens} (B : IsAdmissible X U)
    (h : V ⟶ pullback f g) [QuasiCompact h]
    (hfac : Set.range (h ≫ pullback.fst f g) ⊆ (U : Set X))
    (h' : V ⟶ pullback (B.I.blowupMap ≫ f) g) (hlift : h' ≫ B.blowupBaseChange f g = h)
    [QuasiSeparatedSpace ↥(pullback h.imageι (B.blowupBaseChange f g))]
    (hcpt : IsCompact ((B.preservedOpenPullback f g : Set ↥(pullback f g)))) :
    h'.ker = (strictTransformMap h.imageι (B.blowupBaseChange f g)
      (B.preservedOpenPullback f g)).ker := by
  -- `h` lands over the preserved open, because it lands over `U ≤ B.preservedOpen`.
  have hrange : Set.range h ⊆ (B.preservedOpenPullback f g : Set ↥(pullback f g)) := by
    rintro _ ⟨v, rfl⟩
    exact B.le_preservedOpen (by simpa [Scheme.Hom.comp_apply] using hfac ⟨v, rfl⟩)
  -- the standing quasi-compactness assumption, from the finiteness data
  have hqcπ : QuasiCompact B.I.blowupMap := B.quasiCompact_blowupMap
  have hqcι : QuasiCompact (strictTransformOpen h.imageι (B.blowupBaseChange f g)
      (B.preservedOpenPullback f g)).ι :=
    quasiCompact_strictTransformOpen_ι _ _ _ hcpt
  exact ker_eq_ker_strictTransformMap _ _ h hrange h' hlift

end AlgebraicGeometry
