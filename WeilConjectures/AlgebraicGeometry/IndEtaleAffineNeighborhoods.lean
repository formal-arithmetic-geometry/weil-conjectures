/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport

/-! # Affine neighborhoods for relative pro-etale presentations -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MorphismProperty
namespace AlgebraicGeometry
open Scheme

private theorem acrossUniverses_of_indEtale {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IndEtale) : RingHom.IndEtaleAcrossUniverses f := by
  change (RingHom.ulift.{u, u} f).IndEtale
  rw [RingHom.IndEtale.iff_ind_etale] at hf ⊢
  change (MorphismProperty.ind.{u} CommRingCat.etale)
    (((ULift.ringEquiv : ULift.{u} R ≃+* R).toCommRingCatIso).hom ≫
      CommRingCat.ofHom f ≫
      ((ULift.ringEquiv : ULift.{u} S ≃+* S).toCommRingCatIso).inv)
  simpa only [MorphismProperty.cancel_left_of_respectsIso,
    MorphismProperty.cancel_right_of_respectsIso] using hf

/-- Restrict an affine relative pro-etale presentation over an affine neighborhood.
Each stage becomes absolutely affine, and its global-sections map is ind-etale.
Source: Stacks, Tag 01ZM; the affine presentation step of Bhatt--Scholze 6.3.16.
(blueprint: lem-weil-pbc-ind-etale-affine-neighborhoods). -/
theorem affine_indEtale_neighborhoods {X U : Scheme.{u}}
    (f : U ⟶ X) [IsAffineHom f]
    (hf : MorphismProperty.pro.{u} (@Etale ⊓ @IsAffineHom) f) :
    ∀ t : U, ∃ (V : U.Opens) (W : X.Opens),
      t ∈ V ∧ IsAffine V.toScheme ∧ IsAffine W.toScheme ∧
      ∃ e : V.toScheme ⟶ W.toScheme,
        e ≫ W.ι = V.ι ≫ f ∧ RingHom.IndEtaleAcrossUniverses e.appTop.hom := by
  intro t
  obtain ⟨_, ⟨W : X.Opens, hW, rfl⟩, ht, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f t)) isOpen_univ
  have : IsAffine W.toScheme := hW
  let V : U.Opens := f ⁻¹ᵁ W
  let e := f ∣_ W
  have : IsAffineHom e := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict f W).flip ‹IsAffineHom f›
  have : IsAffine V.toScheme := isAffine_of_isAffineHom e
  have he : MorphismProperty.pro.{u} (@Etale ⊓ @IsAffineHom) e :=
    MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullback
      (isPullback_morphismRestrict f W).flip hf
  have hp : proAffineEtale e := by
    obtain ⟨J, hJ, hco, D, a, s, hs, ha⟩ := he
    refine ⟨J, hJ, hco, D, a, s, hs, fun j ↦ ⟨?_, (ha j).2⟩⟩
    have : IsAffine (((Functor.const J).obj W.toScheme).obj j) := by
      change IsAffine W.toScheme
      infer_instance
    have : IsAffineHom (a.app j) := (ha j).1.2
    exact ⟨(ha j).1.1, ⟨isAffine_of_isAffineHom (a.app j), trivial⟩⟩
  exact ⟨V, W, ht, inferInstance, inferInstance, e, morphismRestrict_ι f W,
    acrossUniverses_of_indEtale e.appTop.hom (proAffineEtale_iff_appTop.mp hp)⟩
end AlgebraicGeometry
