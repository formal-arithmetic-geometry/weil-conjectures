/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Sections of pro-etale covers of w-contractible affine schemes

Source: Stacks Project, Tag 098F, forward implication, with Tags 098D and 0981
(blueprint: lem-weil-pbc-wcontractible-cover-section).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A pro-etale covering of an affine scheme whose faithfully flat weakly etale
algebras all retract admits a section into its covering coproduct.
Source: Stacks Project, Tag 098F, forward implication, and Tags 098D and 0981
(blueprint: lem-weil-pbc-wcontractible-cover-section).

Proof:
1. Apply the covering condition to the whole affine target to obtain a finite
   jointly surjective refinement by affine opens of the cover members (098D).
   Weak etaleness restricts to these opens by source locality
   (lem-weil-pbc-weakly-etale-source-locality).
2. Their finite coproduct is the spectrum of the product of their rings
   (lem-weil-pbc-finite-affine-coproduct-spectrum). Source locality makes its
   map to the target weakly etale, and the refinement makes it surjective.
3. Write that map as Spec of a ring map. Flatness follows from
   lem-weil-pbc-flat-ring-map-iff-flat-affine; surjectivity gives faithful
   flatness by lem-weil-pbc-flat-surjective-spectrum-faithfully-flat.
   The spectrum/ring weak-etaleness equivalence gives a weakly etale algebra.
   Apply the retraction hypothesis and take Spec to obtain a section of the
   finite affine coproduct map.
4. The refinement maps induce a map from the finite coproduct to the original
   coproduct (lem-weil-pbc-scheme-coproduct-family). Coproduct uniqueness shows
   its composite to the target is the finite covering map. Composing the
   section from step 3 with this refinement map proves the asserted identity.
   The empty refinement and zero ring cases obey the same construction. -/
theorem exists_section_proetaleCover_of_ring_retractions
    (A : Type u) [CommRing A]
    (hsplit : ∀ (B : Type u) [CommRing B] [Algebra A B],
      Module.FaithfullyFlat A B → Algebra.WeaklyEtale A B →
        ∃ r : B →+* A, r.comp (algebraMap A B) = RingHom.id A)
    (I : Type u) (T : I → Scheme.{u}) (f : ∀ i : I, T i ⟶ Spec (.of A))
    (hcover : Presieve.ofArrows T f ∈ Scheme.proetalePrecoverage (Spec (.of A))) :
    ∃ σ : Spec (.of A) ⟶ ∐ T, σ ≫ Sigma.desc f = 𝟙 (Spec (.of A)) := by
  classical
  let 𝒰 : (Spec (.of A)).Cover (Scheme.propQCPrecoverage @WeaklyEtale) :=
    { I₀ := I, X := T, f := f, mem₀ := hcover }
  have : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp 𝒰.mem₀.1
  obtain ⟨𝒱, h, hfinite, _⟩ := QuasiCompactCover.exists_hom 𝒰.forgetQc
  have := hfinite
  let Q : Scheme.{u} := ∐ fun j : 𝒱.I₀ ↦ Spec (𝒱.X j)
  let q : Q ⟶ Spec (.of A) := Sigma.desc 𝒱.f
  have : IsAffine Q := inferInstance
  have : WeaklyEtale q := IsZariskiLocalAtSource.sigmaDesc 𝒱.map_prop
  have : Surjective q := by
    constructor
    intro x
    obtain ⟨y, hy⟩ := 𝒱.covers x
    refine ⟨Sigma.ι (fun j ↦ Spec (𝒱.X j)) (𝒱.idx x) y, ?_⟩
    rw [← Scheme.Hom.comp_apply, show Sigma.ι _ (𝒱.idx x) ≫ q = 𝒱.f (𝒱.idx x)
      from Sigma.ι_comp_desc 𝒱.f (𝒱.idx x)]
    exact hy
  let φ := Spec.preimage ((Scheme.isoSpec Q).inv ≫ q)
  let := φ.hom.toAlgebra
  have hφ : Spec.map φ = (Scheme.isoSpec Q).inv ≫ q := Spec.map_preimage _
  have : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A Γ(Q, ⊤)))) := by
    change WeaklyEtale (Spec.map φ)
    rw [hφ]
    infer_instance
  have : Algebra.WeaklyEtale A Γ(Q, ⊤) := weaklyEtale_SpecMap_algebraMap_iff.mp inferInstance
  have : Module.Flat A Γ(Q, ⊤) := by
    rw [← RingHom.flat_algebraMap_iff]
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp inferInstance
  have : Module.FaithfullyFlat A Γ(Q, ⊤) := by
    apply Module.FaithfullyFlat.of_comap_surjective
    have : Surjective (Spec.map φ) := by rw [hφ]; infer_instance
    exact (Spec.map φ).surjective
  obtain ⟨r, hr⟩ := hsplit Γ(Q, ⊤) inferInstance inferInstance
  let s : Spec (.of A) ⟶ Q := Spec.map (CommRingCat.ofHom r) ≫ (Scheme.isoSpec Q).inv
  have hs : s ≫ q = 𝟙 _ := by
    dsimp only [s]
    rw [Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    exact CommRingCat.hom_ext hr
  let g : Q ⟶ ∐ T := Sigma.desc (fun j ↦ h.h₀ j ≫ Sigma.ι T (h.s₀ j))
  have hg : g ≫ Sigma.desc f = q := by
    apply Sigma.hom_ext
    intro j
    simp only [g, q, Sigma.ι_comp_desc_assoc, Category.assoc, Sigma.ι_comp_desc]
    exact h.w₀ j
  exact ⟨s ≫ g, by rw [Category.assoc, hg, hs]⟩

end AlgebraicGeometry
