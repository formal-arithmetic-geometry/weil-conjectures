/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Thickening

/-!
# Locally finitely presented morphisms with unique infinitesimal lifts are étale

Source: Stacks Project, More on Morphisms, Tag 02HM (blueprint:
lem-sfb-lfp-unique-infinitesimal-lifts-etale).
-/

universe u

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

private theorem firstOrder_spec {D E : CommRingCat.{u}} (q : D ⟶ E)
    (hq : Function.Surjective q) (hK : RingHom.ker q.hom ^ 2 = ⊥) :
    IsFirstOrderThickening (Spec.map q) := by
  refine ⟨IsClosedImmersion.spec_of_surjective _ hq, ?_⟩
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply,
    Scheme.IdealSheafData.ideal_bot]
  change RingHom.ker (Spec.map q).appTop.hom ^ 2 = ⊥
  have heq : RingHom.ker (Spec.map q).appTop.hom =
      (RingHom.ker q.hom).comap (Scheme.ΓSpecIso D).hom.hom := by
    rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso E).commRingCatIsoToRingEquiv]
    rw [RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom,
      ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality,
      CommRingCat.hom_comp, RingHom.comap_ker]
  rw [heq]
  apply le_bot_iff.mp
  exact (Ideal.le_comap_pow _ _).trans (by
    rw [hK]
    exact (Ideal.comap_bot_of_injective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso D).hom).1).le)

private theorem firstOrder_surjective {T₀ T : Scheme.{u}} (j : T₀ ⟶ T)
    (hj : IsFirstOrderThickening j) : Function.Surjective j := by
  have : IsClosedImmersion j := hj.1
  have hs : j.ker.support = ⊤ := by
    rw [← Scheme.IdealSheafData.support_pow_succ j.ker 1, hj.2]
    exact Scheme.IdealSheafData.support_bot
  apply Set.range_eq_univ.mp
  rw [← j.isClosedEmbedding.isClosed_range.closure_eq, ← j.support_ker, hs]
  rfl

-- Preserve the existing named proof binder in the lifting hypothesis.
set_option linter.unusedVariables false in
/--
A locally finitely presented morphism of schemes with a unique lift against every
first-order thickening of affine schemes is étale. This is the converse implication
in Stacks Project, More on Morphisms, Lemma 37.13.2 (Tag 02HM), using the affine
first-order lifting formulation of formal étaleness (Tag 02HG).

Proof:
1. For any affine opens `V ⊆ W`, `U ⊆ Z` with `c(V) ⊆ U`, local finite
   presentation gives finite presentation of `Γ(Z, U) → Γ(W, V)`.
2. For a square-zero ideal `I` in a test algebra `D`, the spectrum of the quotient
   map is a first-order thickening: its kernel ideal sheaf has square zero.
   Apply the given lifting property after composing the affine chart inclusions.
3. The thickening is surjective on points. Hence the image of the lift lies in
   `V`, and the open immersion `Spec Γ(W, V) → W` gives its factorization.
   Full faithfulness of `Spec` translates the two triangles into the algebra
   structure equation and the equation saying that the algebra map lifts the
   prescribed map modulo `I`. Uniqueness follows from the original uniqueness
   after cancelling the open immersion.
4. `Algebra.FormallyEtale.iff_comp_bijective` gives formal étaleness of the chart
   algebra. Together with finite presentation, this gives `Algebra.Etale`.
5. These are exactly the affine section maps in the definition of `Etale c`.
   No nonemptiness or separation hypothesis is needed.
(blueprint: lem-sfb-lfp-unique-infinitesimal-lifts-etale)
(blueprint: lem-per-lfp-unique-infinitesimal-lifts-etale)
-/
theorem lfp_unique_infinitesimal_lifts_etale
    {W Z : Scheme.{u}} (c : W ⟶ Z) [LocallyOfFinitePresentation c]
    (h : ∀ (T₀ T : Scheme.{u}) (j : T₀ ⟶ T)
      [IsAffine T₀] [IsAffine T]
      (hj : IsFirstOrderThickening j)
      (a₀ : T₀ ⟶ W) (b : T ⟶ Z),
      a₀ ≫ c = j ≫ b →
      ∃! a : T ⟶ W, j ≫ a = a₀ ∧ a ≫ c = b) :
    Etale c := by
  classical
  constructor
  intro U hU V hV e
  let φ := c.appLE U V e
  let := φ.hom.toAlgebra
  have hfp : Algebra.FinitePresentation Γ(Z, U) Γ(W, V) := c.finitePresentation_appLE hU hV e
  have hfe : Algebra.FormallyEtale Γ(Z, U) Γ(W, V) := by
    apply Algebra.FormallyEtale.iff_comp_bijective.mpr
    intro D _ _ I hI
    let q : CommRingCat.of D ⟶ CommRingCat.of (D ⧸ I) :=
      CommRingCat.ofHom (Ideal.Quotient.mkₐ Γ(Z, U) I).toRingHom
    have hj : IsFirstOrderThickening (Spec.map q) :=
      firstOrder_spec q Ideal.Quotient.mk_surjective (by simpa [q] using hI)
    have hjs := firstOrder_surjective (Spec.map q) hj
    have hφ (v : Γ(W, V) →ₐ[Γ(Z, U)] D) :
        c.appLE U V e ≫ CommRingCat.ofHom v.toRingHom =
          CommRingCat.ofHom (algebraMap Γ(Z, U) D) :=
      CommRingCat.hom_ext v.comp_algebraMap
    have huφ (v : Γ(W, V) →ₐ[Γ(Z, U)] D ⧸ I) :
        c.appLE U V e ≫ CommRingCat.ofHom v.toRingHom =
          CommRingCat.ofHom (algebraMap Γ(Z, U) (D ⧸ I)) :=
      CommRingCat.hom_ext v.comp_algebraMap
    have hqcomp (v : Γ(W, V) →ₐ[Γ(Z, U)] D) :
        CommRingCat.ofHom v.toRingHom ≫ q =
          CommRingCat.ofHom ((Ideal.Quotient.mkₐ Γ(Z, U) I).comp v).toRingHom := rfl
    have hbase : CommRingCat.ofHom (algebraMap Γ(Z, U) (D ⧸ I)) =
        CommRingCat.ofHom (algebraMap Γ(Z, U) D) ≫ q := rfl
    have hex (v : Γ(W, V) →ₐ[Γ(Z, U)] D ⧸ I) := h
      (Spec (.of (D ⧸ I))) (Spec (.of D)) (Spec.map q) hj
      (Spec.map (CommRingCat.ofHom v.toRingHom) ≫ hV.fromSpec)
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Z, U) D)) ≫ hU.fromSpec)
      (by
        rw [Category.assoc, ← hU.SpecMap_appLE_fromSpec c hV e,
          ← Spec.map_comp_assoc, huφ v, hbase, Spec.map_comp_assoc])
    constructor
    · intro v₁ v₂ hv
      have hvSpec : Spec.map q ≫ Spec.map (CommRingCat.ofHom v₁.toRingHom) ≫ hV.fromSpec =
          Spec.map q ≫ Spec.map (CommRingCat.ofHom v₂.toRingHom) ≫ hV.fromSpec := by
        rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hqcomp, hqcomp, hv]
      obtain ⟨a, _, haUnique⟩ := hex ((Ideal.Quotient.mkₐ Γ(Z, U) I).comp v₁)
      have h₁ : Spec.map (CommRingCat.ofHom v₁.toRingHom) ≫ hV.fromSpec = a := by
        apply haUnique
        constructor
        · rw [← Spec.map_comp_assoc, hqcomp]
        · rw [Category.assoc, ← hU.SpecMap_appLE_fromSpec c hV e,
            ← Spec.map_comp_assoc, hφ]
      have h₂ : Spec.map (CommRingCat.ofHom v₂.toRingHom) ≫ hV.fromSpec = a := by
        apply haUnique
        constructor
        · rw [← hvSpec, ← Spec.map_comp_assoc, hqcomp]
        · rw [Category.assoc, ← hU.SpecMap_appLE_fromSpec c hV e,
            ← Spec.map_comp_assoc, hφ]
      have he := (cancel_mono hV.fromSpec).mp (h₁.trans h₂.symm)
      exact AlgHom.ext fun x => congr($(Spec.map_injective he) x)
    · intro v
      obtain ⟨a, ha, _⟩ := hex v
      have hrange : Set.range a ⊆ Set.range hV.fromSpec := by
        rintro _ ⟨t, rfl⟩
        obtain ⟨t₀, rfl⟩ := hjs t
        rw [← Scheme.Hom.comp_apply, ha.1]
        exact ⟨_, rfl⟩
      let l := IsOpenImmersion.lift hV.fromSpec a hrange
      have hl : l ≫ hV.fromSpec = a := IsOpenImmersion.lift_fac _ _ _
      let r := Spec.preimage l
      have hr : Spec.map r = l := Spec.map_preimage l
      have hrφ : φ ≫ r = CommRingCat.ofHom (algebraMap Γ(Z, U) D) := by
        change c.appLE U V e ≫ r = _
        apply Spec.map_injective
        apply (cancel_mono hU.fromSpec).mp
        rw [Spec.map_comp, hr, Category.assoc, hU.SpecMap_appLE_fromSpec c hV e,
          ← Category.assoc, hl, ha.2]
      let v' : Γ(W, V) →ₐ[Γ(Z, U)] D :=
        ⟨r.hom, fun x => congr($(hrφ) x)⟩
      refine ⟨v', ?_⟩
      apply AlgHom.ext
      intro x
      have hrq : r ≫ q = CommRingCat.ofHom v.toRingHom := by
        apply Spec.map_injective
        apply (cancel_mono hV.fromSpec).mp
        simpa only [Spec.map_comp, Category.assoc, hr, hl] using ha.1
      exact congr($(hrq) x)
  exact (show Algebra.Etale Γ(Z, U) Γ(W, V) from ⟨hfe, hfp⟩)

end AlgebraicGeometry

end
