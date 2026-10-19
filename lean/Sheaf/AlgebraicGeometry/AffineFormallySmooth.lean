/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.FormallySmooth
public import Mathlib.RingTheory.RingHom.Smooth
import all WeilConjectures.AlgebraicGeometry.UniversalThickeningAffineCase

/-!
# Affine formal smoothness and the square-zero lifting property

Source: Stacks Project, More on Morphisms, Lemma 37.11.5 (Tag 02H4),
Algebra Definition 10.137.1 (Tag 00TI) (blueprint:
lem-weil-pbc-affine-formally-smooth-iff-ring-lifting).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A surjective ring map with square-zero kernel defines a first order thickening. -/
private theorem firstOrderThickening_spec {B C : Type u} [CommRing B] [CommRing C]
    (q : B →+* C) (hq : Function.Surjective q) (hK : RingHom.ker q ^ 2 = ⊥) :
    IsFirstOrderThickening (Spec.map (CommRingCat.ofHom q)) := by
  have hi : IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) :=
    IsClosedImmersion.spec_of_surjective _ hq
  refine ⟨hi, ?_⟩
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply,
    Scheme.IdealSheafData.ideal_bot]
  change RingHom.ker (Spec.map (CommRingCat.ofHom q)).appTop.hom ^ 2 = ⊥
  have heq : RingHom.ker (Spec.map (CommRingCat.ofHom q)).appTop.hom =
      (RingHom.ker q).comap (Scheme.ΓSpecIso (.of B)).hom.hom := by
    rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso (.of C)).commRingCatIsoToRingEquiv]
    rw [RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom,
      ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality,
      CommRingCat.hom_comp, RingHom.comap_ker]
    rfl
  rw [heq]
  apply le_bot_iff.mp
  exact (Ideal.le_comap_pow _ _).trans (by
    rw [hK]
    exact (Ideal.comap_bot_of_injective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of B)).hom).1).le)

/-- (blueprint: lem-weil-pbc-affine-formally-smooth-iff-ring-lifting)
The morphism of affine schemes induced by a ring homomorphism is formally smooth
exactly when the ring homomorphism has the square-zero lifting property, i.e. is
formally smooth in the ring-theoretic sense of Stacks Tag 00TI
(`RingHom.FormallySmooth`, equivalent to the lifting property by
`Algebra.FormallySmooth.iff_comp_surjective`).

Proof (Stacks 02H4, immediate from the definitions via the equivalence of rings
and affine schemes, Tag 01I2): morphisms `Spec B ⟶ Spec A` are `Spec` of unique
ring maps `A → B`, and `Spec h` lies over `Spec R` iff `h` is an `R`-algebra map.
For `N ⊆ D` with `N ^ 2 = 0`, `Spec (D ⧸ N) ⟶ Spec D` is a first order thickening
of affine schemes over `Spec R`; conversely every first order thickening of affine
schemes over `Spec R` is isomorphic, compatibly with the maps to `Spec R`, to one
of this form, and the lifting problems transport along such isomorphisms. Under
this dictionary the scheme lifting problem for `Spec φ` along `Spec (D ⧸ N) ⟶ Spec D`
is the ring lifting problem for `φ` along `D → D ⧸ N`, which gives both directions. -/
theorem formallySmooth_spec_iff_ringHom_formallySmooth
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    FormallySmooth (Scheme.Spec.map (CommRingCat.ofHom φ).op) ↔
      RingHom.FormallySmooth φ := by
  change FormallySmooth (Spec.map (CommRingCat.ofHom φ)) ↔ RingHom.FormallySmooth φ
  let : Algebra R S := φ.toAlgebra
  constructor
  · intro H
    apply Algebra.FormallySmooth.of_comp_surjective
    intro B _ _ I hI g
    let q := Ideal.Quotient.mk I
    let b := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let : (Spec (.of B)).Over (Spec (.of R)) := ⟨b⟩
    have hi : IsFirstOrderThickening (Spec.map (CommRingCat.ofHom q)) :=
      firstOrderThickening_spec q Ideal.Quotient.mk_surjective (by
        simpa only [q, Ideal.mk_ker] using hI)
    have hcomm : Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom q) ≫ b := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      apply congrArg Spec.map
      exact CommRingCat.hom_ext g.comp_algebraMap
    obtain ⟨a', ha', hb'⟩ := H (Spec.map (CommRingCat.ofHom q)) hi
      (Spec.map (CommRingCat.ofHom g.toRingHom)) hcomm
    change a' ≫ Spec.map (CommRingCat.ofHom φ) = b at hb'
    obtain ⟨h, hh⟩ := Spec.map_surjective a'
    have hR : h.hom.comp φ = algebraMap R B := by
      have hc : CommRingCat.ofHom φ ≫ h = CommRingCat.ofHom (algebraMap R B) :=
        Spec.map_injective (by simpa only [Spec.map_comp, hh] using hb')
      exact congrArg CommRingCat.Hom.hom hc
    let hₐ : S →ₐ[R] B := ⟨h.hom, RingHom.congr_fun hR⟩
    refine ⟨hₐ, ?_⟩
    have hc : h ≫ CommRingCat.ofHom q = CommRingCat.ofHom g.toRingHom :=
      Spec.map_injective (by simpa only [Spec.map_comp, hh] using ha')
    exact AlgHom.ext (RingHom.congr_fun (congrArg CommRingCat.Hom.hom hc))
  · intro H
    let : Algebra.FormallySmooth R S := H
    intro T T' i _ _ _ hi a ha
    have : IsClosedImmersion i := hi.1
    let A := Γ(T', ⊤)
    let q : A →+* Γ(T, ⊤) := i.appTop.hom
    have hq : Function.Surjective q := i.app_surjective ⊤ (isAffineOpen_top T')
    have hI : RingHom.ker q ^ 2 = ⊥ := by
      simpa only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
        Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] using
        congrArg (fun J ↦ J.ideal ⟨⊤, isAffineOpen_top T'⟩) hi.2
    let β := specRingHom (T' ↘ Spec (.of R))
    let : Algebra R A := β.toAlgebra
    let : Algebra R Γ(T, ⊤) := (q.comp β).toAlgebra
    let α := specRingHom a
    have hα : α.comp φ = q.comp β := by
      have hh := congrArg specRingHom ha
      rw [specRingHom_spec, specRingHom_comp] at hh
      exact hh
    let αₐ : S →ₐ[R] Γ(T, ⊤) := ⟨α, RingHom.congr_fun hα⟩
    let qₐ : A →ₐ[R] Γ(T, ⊤) := ⟨q, fun _ ↦ rfl⟩
    have hn : IsNilpotent (RingHom.ker qₐ.toRingHom) := ⟨2, hI⟩
    let l := Algebra.FormallySmooth.liftOfSurjective αₐ qₐ hq hn
    obtain ⟨a', ha'⟩ := specRingHom_lift l.toRingHom
    refine ⟨a', ?_, ?_⟩
    · apply specRingHom_injective
      rw [specRingHom_comp, ha']
      exact congrArg AlgHom.toRingHom
        (Algebra.FormallySmooth.comp_liftOfSurjective αₐ qₐ hq hn)
    · apply specRingHom_injective
      rw [specRingHom_spec, ha']
      exact l.comp_algebraMap

end AlgebraicGeometry
