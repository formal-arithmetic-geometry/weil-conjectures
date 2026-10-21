/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import WeilConjectures.RingTheory.ProEtale.IndEtale
import Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # The canonical coordinate ring of a geometric strict-local base is ind-etale
Source: Stacks Project, Tags 0EZV and 04HX, strict-local affine presentation and base change.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The canonical K-algebra of the geometric strict-local base is ind-etale.
Source: Stacks Project, Tags 0EZV and 04HX.
(blueprint: lem-weil-pbc-strict-local-base-ind-etale).

Proof: choose an affine chart at the image of the closed point. The local spectrum
factors through that chart. Its canonical ring map R to A is ind-etale by the existing
strict-henselization affine-chart theorem. Cancel the monomorphic chart inclusion to
regard the requested pullback as a pullback over Spec R. Its top-section ring square
is a pushout, since both factors and the chart are affine. Transport R to A through the
canonical Gamma-Spec isomorphisms; ind-etale ring maps are stable under isomorphisms.
Base change in this ring pushout gives the ind-etale map from Gamma(Spec K) to Gamma(E).
Precompose with the canonical K to Gamma(Spec K) isomorphism. The result is exactly
the ring map specified in the statement. No separable-closedness hypothesis on K is used. -/
theorem strictLocalBase_indEtale {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (K : Type u) [Field K]
    (u : Spec (.of K) ⟶ Scheme.strictHenselizationScheme s) :
    ((Scheme.ΓSpecIso (.of K)).inv ≫
      (pullback.snd (Scheme.strictHenselizationStructuralMap s)
        (u ≫ Scheme.strictHenselizationStructuralMap s)).appTop).hom.IndEtale := by
  classical
  let : Algebra (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
  obtain ⟨hlocal, _, hclosed, _, _⟩ := strictHenselizationResidue s rfl
  let := hlocal
  obtain ⟨R, i, hi, y, hy⟩ := S.exists_Spec_apply_eq (s (IsLocalRing.closedPoint Ω))
  let := hi
  have hrange : Set.range (Scheme.strictHenselizationStructuralMap s) ⊆ Set.range i := by
    have hc : IsLocalRing.closedPoint (Scheme.strictHenselizationRing s) ∈
        (Scheme.strictHenselizationStructuralMap s) ⁻¹ᵁ i.opensRange := by
      change Scheme.strictHenselizationStructuralMap s
        (IsLocalRing.closedPoint (Scheme.strictHenselizationRing s)) ∈ Set.range i
      rw [hclosed]
      exact ⟨y, hy⟩
    have htop := (IsLocalRing.closedPoint_mem_iff _).mp hc
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ (Scheme.strictHenselizationStructuralMap s) ⁻¹ᵁ i.opensRange :=
      htop ▸ trivial
    exact hz
  let b := IsOpenImmersion.lift i (Scheme.strictHenselizationStructuralMap s) hrange
  have hb : b ≫ i = Scheme.strictHenselizationStructuralMap s :=
    IsOpenImmersion.lift_fac _ _ _
  let A := Scheme.strictHenselizationRing s
  let ρ : R →+* A := (Spec.preimage b).hom
  have hρ : ρ.IndEtale := by
    have h := Scheme.smallStrictHenselization_indEtale_of_affine_chart
      s R i ⟨y, hy⟩ (Iso.refl _) ρ (by
        change Spec.map (Spec.preimage b) ≫ i = 𝟙 _ ≫ _
        simpa only [Spec.map_preimage, Category.id_comp] using hb)
    exact h
  let H := IsPullback.of_hasPullback (Scheme.strictHenselizationStructuralMap s)
    (u ≫ Scheme.strictHenselizationStructuralMap s)
  have hp := IsPullback.of_isLimit
    (PullbackCone.isLimitOfFactors _ _ i b (u ≫ b) hb
      (by simp only [Category.assoc, hb]) H.cone H.isLimit)
  have : IsAffine (Scheme.strictHenselizationScheme s) :=
    inferInstanceAs (IsAffine (Spec (Scheme.strictHenselizationRing s)))
  have hpush := isPushout_appTop_of_isPullback hp
  let P := MorphismProperty.ind.{u} CommRingCat.etale
  have hPρ : P (Spec.preimage b) :=
    (RingHom.IndEtale.iff_ind_etale ρ).mp hρ
  have heq : b.appTop = (Scheme.ΓSpecIso R).hom ≫ Spec.preimage b ≫
      (Scheme.ΓSpecIso A).inv := by
    apply (cancel_epi (Scheme.ΓSpecIso R).inv).mp
    simp only [Iso.inv_hom_id_assoc]
    simpa only [Spec.map_preimage] using
      (Scheme.ΓSpecIso_inv_naturality (Spec.preimage b)).symm
  have hPb : P b.appTop := by
    rw [heq]
    exact P.comp_mem _ _ (P.of_isIso _) (P.comp_mem _ _ hPρ (P.of_isIso _))
  have hPa : P (pullback.snd (Scheme.strictHenselizationStructuralMap s)
      (u ≫ Scheme.strictHenselizationStructuralMap s)).appTop := by
    exact MorphismProperty.of_isPushout hpush.flip hPb
  have hPα : P ((Scheme.ΓSpecIso (.of K)).inv ≫
      (pullback.snd (Scheme.strictHenselizationStructuralMap s)
        (u ≫ Scheme.strictHenselizationStructuralMap s)).appTop) :=
    P.comp_mem _ _ (P.of_isIso _) hPa
  exact (RingHom.IndEtale.iff_ind_etale _).mpr hPα

end AlgebraicGeometry.Etale
