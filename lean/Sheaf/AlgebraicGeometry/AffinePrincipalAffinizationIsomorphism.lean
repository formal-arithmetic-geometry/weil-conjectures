/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q121
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Affinization on an affine principal open

Source: Stacks Project, Properties, Tag 01P8, lemma-invert-f-affine, and Tag 01P7,
lemma-invert-f-sections (blueprint: lem-a1-affine-principal-affinization-isomorphism).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- On an affine principal open of a qcqs scheme, the canonical affinization morphism
restricts to an isomorphism onto the corresponding distinguished open of the spectrum.
Its section map, after the canonical identification with the localization, is the ring
isomorphism sending `a / f ^ n` to the restriction of `a` times the inverse of the
restriction of `f`, raised to the power `n`.

Source: Stacks Project, Properties, Tag 01P8, lemma-invert-f-affine.
(blueprint: lem-a1-affine-principal-affinization-isomorphism).

Proof:
The qcqs section-localization theorem makes `X.toSpecΓ.app D(f)` an isomorphism.
Transport along the basic-open preimage equality and the canonical top-section
identifications to get an isomorphism on global sections of the restricted morphism.
Both its source and target are affine, so the affine spectrum/global-sections
comparison makes the restricted morphism an isomorphism. Composing with the standard
isomorphism `D(f) ≅ Spec (Localization.Away f)` gives `X.toSpecAway f`, hence the
ring equivalence underlying `X.awayToBasicOpen f`. Its fraction formula follows
by multiplying by the unit `(f|_{X_f})^n` and using `IsLocalization.mk'_spec`. -/
theorem affine_principal_affinization_isomorphism (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (f : Γ(X, ⊤))
    (hf : IsAffineOpen (X.basicOpen f)) :
    X.toSpecΓ ⁻¹ᵁ (PrimeSpectrum.basicOpen f) = X.basicOpen f ∧
      IsIso (X.toSpecΓ.resLE (PrimeSpectrum.basicOpen f) (X.basicOpen f)
        (X.toSpecΓ_preimage_basicOpen f).ge) ∧
      ∃ e : Localization.Away f ≃+* Γ((X.basicOpen f).toScheme, ⊤),
        e.toRingHom = (X.awayToBasicOpen f).hom ∧
        ∀ (a : Γ(X, ⊤)) (n : ℕ),
          e (IsLocalization.mk' (Localization.Away f) a (Submonoid.pow f n)) =
            (X.basicOpen f).ι.appTop a *
              Ring.inverse ((X.basicOpen f).ι.appTop f) ^ n := by
  let U : (Spec Γ(X, ⊤)).Opens := PrimeSpectrum.basicOpen f
  let V := X.basicOpen f
  let g := X.toSpecΓ.resLE U V (X.toSpecΓ_preimage_basicOpen f).ge
  have hpre := X.toSpecΓ_preimage_basicOpen f
  have : IsIso (X.toSpecΓ.appLE U V hpre.ge) := by
    have : IsIso (homOfLE hpre.ge) := homOfLE_isIso_of_eq _ hpre.symm
    dsimp [Scheme.Hom.appLE, U, V]
    infer_instance
  have : IsIso g.appTop := by
    dsimp [g, Scheme.Hom.appTop]
    rw [Scheme.Hom.resLE_app_top]
    infer_instance
  have : IsAffine V.toScheme := hf
  have : IsAffine U.toScheme := IsAffineOpen.Spec_basicOpen f
  have hg : IsIso g := by
    rw [← MorphismProperty.isomorphisms.iff,
      (MorphismProperty.isomorphisms _).arrow_mk_iso_iff (arrowIsoSpecΓOfIsAffine g),
      MorphismProperty.isomorphisms.iff]
    infer_instance
  have : IsIso (X.toSpecAway f) := by
    dsimp [Scheme.toSpecAway]
    infer_instance
  have : IsIso (X.awayToBasicOpen f) := by
    dsimp [Scheme.awayToBasicOpen]
    infer_instance
  let e := (asIso (X.awayToBasicOpen f)).commRingCatIsoToRingEquiv
  refine ⟨hpre, hg, e, rfl, ?_⟩
  intro a n
  apply ((X.isUnit_ι_appTop_basicOpen f).pow n).mul_right_cancel
  change X.awayToBasicOpen f (IsLocalization.mk' (Localization.Away f) a
    (Submonoid.pow f n)) * _ = _
  have hfrac := IsLocalization.mk'_spec (Localization.Away f) a (Submonoid.pow f n)
  change IsLocalization.mk' (Localization.Away f) a (Submonoid.pow f n) *
    algebraMap Γ(X, ⊤) (Localization.Away f) (f ^ n) = _ at hfrac
  rw [← map_pow, ← X.awayToBasicOpen_algebraMap f (f ^ n), ← map_mul, hfrac,
    X.awayToBasicOpen_algebraMap, X.awayToBasicOpen_algebraMap]
  rw [map_pow, mul_assoc, ← mul_pow,
    Ring.inverse_mul_cancel _ (X.isUnit_ι_appTop_basicOpen f), one_pow, mul_one]

end AlgebraicGeometry
