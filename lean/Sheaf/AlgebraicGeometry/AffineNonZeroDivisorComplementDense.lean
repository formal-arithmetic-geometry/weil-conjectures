/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Density of a principal nonzerodivisor complement

Source: Stacks Project, Divisors, Lemma 31.14.4 (Tag 07ZU), affine-local calculation
(blueprint: lem-pc-affine-nonzerodivisor-complement-dense).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
/-- For a nonzerodivisor `a`, the restriction of the structure sheaf of `Spec A` to
the principal open `D(a)` is injective on every open, and `D(a)` is dense.

Source: Stacks Project, Divisors, Lemma 31.14.4 (Tag 07ZU), affine-local calculation
(blueprint: lem-pc-affine-nonzerodivisor-complement-dense).

Proof: On each principal open `D(g)`, restriction to `D(a)` is localization
`A_g → (A_g)_a`. Localization preserves nonzerodivisors
([lem-pc-localization-preserves-nonzerodivisor]), and localization at a nonzerodivisor
is injective ([lem-pc-affine-localization-injective]). Injectivity on this basis gives
injectivity of the restriction sheaf morphism. The principal open is dense by
[lem-pc-principal-open-dense-of-nonzerodivisor]. -/
theorem PrimeSpectrum.basicOpen_app_injective_and_dense_of_nonZeroDivisor
    (A : Type u) [CommRing A] (a : A) (ha : a ∈ nonZeroDivisors A) :
    (∀ V : (Spec (.of A)).Opens,
      Function.Injective
        ((Scheme.Opens.ι (X := Spec (.of A)) (PrimeSpectrum.basicOpen a)).app V)) ∧
    DenseRange (Scheme.Opens.ι (X := Spec (.of A)) (PrimeSpectrum.basicOpen a)) := by
  let φ : CommRingCat.of A ⟶ CommRingCat.of (Localization.Away a) :=
    CommRingCat.ofHom (algebraMap A (Localization.Away a))
  have hφ : Function.Injective φ :=
    IsLocalization.injective _ (Submonoid.powers_le.mpr ha)
  have hf : Function.Injective (Spec.map φ).appTop := by
    have he : (Spec.map φ).appTop =
        (Scheme.ΓSpecIso (.of A)).hom ≫ φ ≫ (Scheme.ΓSpecIso _).inv := by
      rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [he]
    exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).1.comp hφ).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).hom).1
  have : IsSchemeTheoreticallyDominant (Spec.map φ) := by
    constructor
    apply Scheme.IdealSheafData.ext_of_isAffine
    simpa [(Spec.map φ).ker_apply ⟨⊤, isAffineOpen_top _⟩,
      ← RingHom.injective_iff_ker_eq_bot] using hf
  have : IsSchemeTheoreticallyDominant
      (Scheme.Opens.ι (X := Spec (.of A)) (PrimeSpectrum.basicOpen a)) := by
    rw [← basicOpenIsoSpecAway_hom_SpecMap (R := .of A) a]
    infer_instance
  have : IsAffine (Scheme.Opens.toScheme (X := Spec (.of A))
      (PrimeSpectrum.basicOpen a)) := IsAffineOpen.Spec_basicOpen (R := .of A) a
  exact ⟨fun V ↦ Scheme.Hom.app_injective _ V, Scheme.Hom.denseRange _⟩

end AlgebraicGeometry
