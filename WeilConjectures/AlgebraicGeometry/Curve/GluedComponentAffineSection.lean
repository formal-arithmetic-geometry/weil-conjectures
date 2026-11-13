/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.AlgebraicGeometry.Ample.AmpleFinitePrincipalAffine
import WeilConjectures.AlgebraicGeometry.GlueComponentLineBundles
import WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower
import WeilConjectures.AlgebraicGeometry.AffineLocusOfCompatibleComponentSections

/-! # An affine section around component intersections

Source: Stacks Project, Varieties, Lemma 09NX, first two paragraphs.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option linter.unusedVariables false in
/-- Ample modules on the components can be powered and glued, with an affine section
neighbourhood of their intersections. This constructs the bundle but does not assert
its ampleness on the ambient scheme.

Source: Stacks Project, Varieties, Lemma 09NX, first two paragraphs; Properties,
Lemma 09NV; Varieties, Lemma 09NE; Limits, Lemma 09NL. -/
theorem exists_glued_component_affine_section
    (X : Scheme.{u}) [IsReduced X] (r : ℕ)
    (C : Fin r → Scheme.{u}) (i : ∀ a, C a ⟶ X)
    [∀ a, IsClosedImmersion (i a)]
    (hcover : (⋃ a, Set.range (i a)) = Set.univ)
    (T : Set X)
    (hT : T = {x | ∃ a b : Fin r, a ≠ b ∧
      x ∈ Set.range (i a) ∩ Set.range (i b)})
    (hfinite : T.Finite) (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X))
    (M : ∀ a, (C a).Modules) [∀ a, (M a).IsInvertible]
    (hM : ∀ a, IsAmple (C a) (M a)) :
    ∃ (L : X.Modules) (hL : L.IsInvertible),
      (∀ a, ∃ h : ((tensorPullback (i a)).obj L).IsInvertible,
        @IsAmple (C a) ((tensorPullback (i a)).obj L) h) ∧
      ∃ s : (L.tensorPow 1).val.presheaf.obj (Opposite.op ⊤),
        ∃ U : X.Opens, T ⊆ (U : Set X) ∧ IsAffineOpen U ∧
          (U : Set X) = nonvanishingLocus (L.tensorPow 1) s := by
  classical
  have hpre (a : Fin r) : (i a ⁻¹' T).Finite :=
    hfinite.preimage (i a).isClosedEmbedding.injective.injOn
  have hchoice (a : Fin r) := exists_affine_section_neighbourhood_of_finite
    (C a) (M a) (hM a) (i a ⁻¹' T) (hpre a) ⊤ (by simp)
  choose n hn s V hTV hVtop hVaff hVlocus using hchoice
  let P (a : Fin r) := (M a).tensorPow (n a)
  have (a : Fin r) : (P a).IsInvertible := inferInstance
  have hPT (a : Fin r) : i a ⁻¹' T ⊆ nonvanishingLocus (P a) (s a) := by
    intro x hx
    exact (hVlocus a x).1 (hTV a hx)
  have hover (a b : Fin r) (hab : a ≠ b) :
      Set.range (i a) ∩ Set.range (i b) ⊆ T := by
    intro x hx
    rw [hT]
    exact ⟨a, b, hab, hx⟩
  have hdiscrete (a b : Fin r) (hab : a ≠ b) :
      DiscreteTopology ↥(Set.range (i a) ∩ Set.range (i b)) := by
    let S := Set.range (i a) ∩ Set.range (i b)
    have : Finite S := (hfinite.subset (hover a b hab)).to_subtype
    have : T1Space S := ⟨fun x ↦ by
      have hc : IsClosed ((Subtype.val : S → X) ⁻¹' {x.1}) :=
        (hclosed x.1 (hover a b hab x.2)).preimage continuous_subtype_val
      have heq : (Subtype.val : S → X) ⁻¹' {x.1} = {x} := by
        ext y
        exact Subtype.val_injective.eq_iff
      rwa [heq] at hc⟩
    infer_instance
  have hs (a b : Fin r) (hab : a ≠ b) :
      Set.range (i a) ∩ Set.range (i b) ⊆ i a '' nonvanishingLocus (P a) (s a) := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx.1
    exact ⟨y, hPT a (hover a b hab hx), rfl⟩
  obtain ⟨L, t, hL, he⟩ :=
    (glueComponentLineBundles C i hcover hdiscrete P).2 s hs
  let : L.IsInvertible := hL
  have hamp (a : Fin r) : IsAmple (C a) (P a) :=
    isAmple_positive_tensorPow (M a) (hM a) (n a) (hn a)
  have hresamp (a : Fin r) : ∃ h : ((tensorPullback (i a)).obj L).IsInvertible,
      @IsAmple (C a) ((tensorPullback (i a)).obj L) h := by
    obtain ⟨e, _⟩ := he a
    let h' : ((tensorPullback (i a)).obj L).IsInvertible := IsInvertible.of_iso e.symm
    exact ⟨h', (isAmple_iff_of_iso e).mpr (hamp a)⟩
  obtain ⟨q, U, hTU, hU, hUq⟩ := affine_locus_of_compatible_component_sections
    X r C i hcover T L t P s V hPT (fun a ↦ Set.ext (hVlocus a)) hVaff he
  exact ⟨L, (show L.IsInvertible from hL), hresamp, q, U, hTU, hU, hUq⟩

end AlgebraicGeometry.Scheme.Modules
