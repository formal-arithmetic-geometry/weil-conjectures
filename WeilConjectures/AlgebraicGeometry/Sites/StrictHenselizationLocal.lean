/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

/-!
# The strict henselization is a strictly henselian local ring

Let `s : Spec Ω ⟶ S` be a geometric point of a scheme `S`. The strict henselization
`𝒪^{sh}_{S,s}`, the colimit of the rings of the affine pointed étale neighbourhoods of `s`, is
a henselian local ring with separably closed residue field, and the geometric point `s` factors
through the closed point of the strict localization `S_(s) = Spec 𝒪^{sh}_{S,s}`.

## References

- Stacks Project, Lemma 59.33.1, <https://stacks.math.columbia.edu/tag/04HX>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- The strict henselization is a local ring. -/
instance isLocalRing_strictHenselization : IsLocalRing (strictHenselization s) :=
  sorry

/-- The strict henselization is a henselian local ring. -/
instance henselianLocalRing_strictHenselization : HenselianLocalRing (strictHenselization s) :=
  sorry

/-- The residue field of the strict henselization is separably closed. -/
instance isSepClosed_residueField_strictHenselization :
    IsSepClosed (IsLocalRing.ResidueField (strictHenselization s)) :=
  sorry

/-- The geometric point `s` factors through the closed point of the strict localization: there
is an embedding `φ` of the residue field of `𝒪^{sh}_{S,s}` into `Ω` such that `s` is the
composite `Spec Ω ⟶ Spec κ ⟶ S_(s) ⟶ S`. -/
theorem exists_residueField_hom_strictLocalization :
    ∃ φ : IsLocalRing.ResidueField (strictHenselization s) →+* Ω,
      Spec.map (CommRingCat.ofHom (φ.comp (IsLocalRing.residue _))) ≫
        strictLocalizationToBase s = s :=
  sorry

end AlgebraicGeometry.Scheme
