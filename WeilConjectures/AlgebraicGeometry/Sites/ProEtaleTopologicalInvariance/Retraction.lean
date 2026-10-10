/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Cover
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC

/-!
# Retractions of étale covers along universal homeomorphisms

Let `A → B` be a ring map such that `Spec B ⟶ Spec A` is a universal homeomorphism. If every
faithfully flat étale `A`-algebra has a retraction, then so does every faithfully flat étale
`B`-algebra. This is a consequence of property (C) of [Stacks 04DW]: an étale `B`-algebra `F`
receives a surjective map from the base change `B ⊗[A] G` of an étale `A`-algebra `G`, and a
retraction of `G` induces one of `F`.

This is used in the topological invariance of the small pro-étale site, to show that the base
change of a w-strictly local ring along a universal homeomorphism is again w-strictly local.

## Main statements

- `Algebra.IsUniversalHomeomorphism.exists_retraction_of_etale`: retractions of faithfully
  flat étale algebras transfer along universal homeomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Algebra.IsUniversalHomeomorphism

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [_root_.Algebra.IsUniversalHomeomorphism A B]

/-- **Retractions transfer along universal homeomorphisms**: if every faithfully flat étale
`A`-algebra has a retraction and `Spec B ⟶ Spec A` is a universal homeomorphism, then every
faithfully flat étale `B`-algebra has a retraction. -/
theorem exists_retraction_of_etale
    (H : ∀ (G : Type u) [CommRing G] [Algebra A G], _root_.Algebra.Etale A G →
      Function.Surjective (PrimeSpectrum.comap (algebraMap A G)) →
      ∃ ρ : G →+* A, ρ.comp (algebraMap A G) = RingHom.id A)
    (F : Type u) [CommRing F] [Algebra B F] [_root_.Algebra.Etale B F]
    (hF : Function.Surjective (PrimeSpectrum.comap (algebraMap B F))) :
    ∃ ρ : F →+* B, ρ.comp (algebraMap B F) = RingHom.id B := by
  let f : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g : Spec (.of F) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom (algebraMap B F))
  have : AlgebraicGeometry.Etale g :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr ‹_›)
  -- property (C): an affine étale `W ⟶ Spec A` with a surjection `W ×_{Spec A} Spec B ⟶ Spec F`
  obtain ⟨W, hW, p, hp, h, hhg, hh⟩ := exists_etale_surjective_of_forall f g
    (fun u ↦ Scheme.Hom.exists_etale_hom_mem_range f g u)
  have hpsurj : Function.Surjective p := by
    intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    obtain ⟨u, hu⟩ := hF x
    obtain ⟨w, rfl⟩ := hh u
    refine ⟨pullback.fst p f w, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← hhg]
    exact congrArg f hu
  -- the étale `A`-algebra `G = Γ(W)` is faithfully flat, hence has a retraction
  let _ := p.ΓAlgebra
  have hG : _root_.Algebra.Etale A Γ(W, ⊤) := (p.etale_iff_etale_ΓAlgebra).mp hp
  have hGsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A Γ(W, ⊤))) := by
    intro y
    obtain ⟨w, rfl⟩ := hpsurj y
    refine ⟨W.isoSpec.hom w, ?_⟩
    have := congr($(p.isoSpec_inv_comp) (W.isoSpec.hom w))
    have e : W.isoSpec.inv (W.isoSpec.hom w) = w := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
    rw [Scheme.Hom.comp_apply, e] at this
    rw [this, p.algebraMap_ΓAlgebra]
    rfl
  obtain ⟨ρ, hρ⟩ := H Γ(W, ⊤) hG hGsurj
  let ρ' : Γ(W, ⊤) →ₐ[A] A :=
    { ρ with commutes' := fun a ↦ congr($hρ a) }
  -- the section `σ : Spec A ⟶ W` of `p`
  let σ := (p.overHomEquivAlgHom A).symm ρ'
  have hσ : σ.left ≫ p = 𝟙 (Spec (.of A)) := by
    have := Over.w σ
    simp only [Over.mk_left, Over.mk_hom] at this
    rw [this, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  -- the induced section of `Spec F ⟶ Spec B`
  let s : Spec (.of B) ⟶ pullback p f :=
    pullback.lift (f ≫ σ.left) (𝟙 _) (by rw [Category.assoc, hσ, Category.comp_id,
      Category.id_comp])
  let t : Spec (.of B) ⟶ Spec (.of F) := s ≫ h
  have ht : t ≫ g = 𝟙 _ := by
    simp only [t, s, Category.assoc, hhg, pullback.lift_snd]
  refine ⟨(Spec.preimage t).hom, ?_⟩
  have h₁ : Spec.map (CommRingCat.ofHom (algebraMap B F) ≫ Spec.preimage t) =
      Spec.map (𝟙 (CommRingCat.of B)) := by
    rw [Spec.map_comp, Spec.map_preimage, ht, Spec.map_id]
  exact congr(($(Spec.map_injective h₁)).hom)

end AlgebraicGeometry.Algebra.IsUniversalHomeomorphism
