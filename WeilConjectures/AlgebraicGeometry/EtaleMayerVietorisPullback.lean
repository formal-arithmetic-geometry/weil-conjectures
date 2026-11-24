/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyOpenRestrictionNaturality
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisConnectingPullback

/-!
# Pullback compatibility of the étale Mayer–Vietoris sequence

## References

* Stacks Project, Tag 0A50
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The two Mayer-Vietoris sequences, for `G` on `X` and for `g⁻¹G` on `Y`, are compatible with
pullback: all squares commute in every degree (Stacks, Tag 0A50). The maps `pU`, `pV`, `pI`
are restricted pullback followed by the inverse-image composition identifications. -/
theorem etale_mayerVietoris_pullback
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ rXU : ∀ q : ℕ, Sheaf.H G q →+ Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (U.ι)).obj G) q,
    ∃ rXV : ∀ q : ℕ, Sheaf.H G q →+ Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (V.ι)).obj G) q,
    ∃ rXIU : ∀ q : ℕ, Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (U.ι)).obj G) q →+ Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} ((U ⊓ V).ι)).obj G) q,
    ∃ rXIV : ∀ q : ℕ, Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (V.ι)).obj G) q →+ Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} ((U ⊓ V).ι)).obj G) q,
    ∃ rYU : ∀ q : ℕ, Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g)).obj G) q →+ Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ U).ι)).obj ((upperStar AddCommGrpCat.{u + 1}
        (g)).obj G)) q,
    ∃ rYV : ∀ q : ℕ, Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g)).obj G) q →+ Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ V).ι)).obj ((upperStar AddCommGrpCat.{u + 1}
        (g)).obj G)) q,
    ∃ rYIU : ∀ q : ℕ, Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ U).ι)).obj ((upperStar
        AddCommGrpCat.{u + 1} (g)).obj G)) q →+ Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ
        (U ⊓ V)).ι)).obj ((upperStar AddCommGrpCat.{u + 1} (g)).obj G)) q,
    ∃ rYIV : ∀ q : ℕ, Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ V).ι)).obj ((upperStar
        AddCommGrpCat.{u + 1} (g)).obj G)) q →+ Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ
        (U ⊓ V)).ι)).obj ((upperStar AddCommGrpCat.{u + 1} (g)).obj G)) q,
    ∃ pU : ∀ q : ℕ, Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (U.ι)).obj G) q →+ Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ U).ι)).obj ((upperStar AddCommGrpCat.{u + 1}
        (g)).obj G)) q,
    ∃ pV : ∀ q : ℕ, Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (V.ι)).obj G) q →+ Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ V).ι)).obj ((upperStar AddCommGrpCat.{u + 1}
        (g)).obj G)) q,
    ∃ pI : ∀ q : ℕ, Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((U ⊓ V).ι)).obj G) q →+ Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ (U ⊓ V)).ι)).obj ((upperStar AddCommGrpCat.{u +
        1} (g)).obj G)) q,
    ∃ δX : ∀ q : ℕ, Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((U ⊓ V).ι)).obj G) q →+ Sheaf.H G
        (q + 1),
    ∃ δY : ∀ q : ℕ, Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ (U ⊓ V)).ι)).obj ((upperStar
        AddCommGrpCat.{u + 1} (g)).obj G)) q →+ Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g)).obj
        G) (q + 1),
    (∀ q, rXU q = cohomologyMap U.ι G q) ∧
    (∀ q, rXV q = cohomologyMap V.ι G q) ∧
    (∀ q, rXIU q = (Sheaf.H.map
        ((upperStarComp AddCommGrpCat.{u + 1} (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) U.ι
          (U ⊓ V).ι (X.homOfLE_ι (inf_le_left : U ⊓ V ≤ U)).symm).inv.app G) q).comp
        (cohomologyMap (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) ((upperStar AddCommGrpCat.{u + 1}
        (U.ι)).obj G) q)) ∧
    (∀ q, rXIV q = (Sheaf.H.map
        ((upperStarComp AddCommGrpCat.{u + 1} (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) V.ι
          (U ⊓ V).ι (X.homOfLE_ι (inf_le_right : U ⊓ V ≤ V)).symm).inv.app G) q).comp
        (cohomologyMap (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) ((upperStar AddCommGrpCat.{u + 1}
        (V.ι)).obj G) q)) ∧
    (∀ q, rYU q = cohomologyMap (g ⁻¹ᵁ U).ι ((upperStar AddCommGrpCat.{u + 1} (g)).obj G) q) ∧
    (∀ q, rYV q = cohomologyMap (g ⁻¹ᵁ V).ι ((upperStar AddCommGrpCat.{u + 1} (g)).obj G) q) ∧
    (∀ q, rYIU q = (Sheaf.H.map
        ((upperStarComp AddCommGrpCat.{u + 1} (Y.homOfLE (g.preimage_mono (inf_le_left : U ⊓ V ≤
        U))) (g ⁻¹ᵁ U).ι
          (g ⁻¹ᵁ (U ⊓ V)).ι (Y.homOfLE_ι (g.preimage_mono (inf_le_left : U ⊓ V ≤
        U))).symm).inv.app ((upperStar AddCommGrpCat.{u + 1} (g)).obj G)) q).comp
        (cohomologyMap (Y.homOfLE (g.preimage_mono (inf_le_left : U ⊓ V ≤ U))) ((upperStar
        AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ U).ι)).obj ((upperStar AddCommGrpCat.{u + 1} (g)).obj G))
        q)) ∧
    (∀ q, rYIV q = (Sheaf.H.map
        ((upperStarComp AddCommGrpCat.{u + 1} (Y.homOfLE (g.preimage_mono (inf_le_right : U ⊓ V ≤
        V))) (g ⁻¹ᵁ V).ι
          (g ⁻¹ᵁ (U ⊓ V)).ι (Y.homOfLE_ι (g.preimage_mono (inf_le_right : U ⊓ V ≤
        V))).symm).inv.app ((upperStar AddCommGrpCat.{u + 1} (g)).obj G)) q).comp
        (cohomologyMap (Y.homOfLE (g.preimage_mono (inf_le_right : U ⊓ V ≤ V))) ((upperStar
        AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ V).ι)).obj ((upperStar AddCommGrpCat.{u + 1} (g)).obj G))
        q)) ∧
    (∀ q, pU q = (Sheaf.H.map
        (((upperStarComp AddCommGrpCat.{u + 1} (g ∣_ U) U.ι
            ((g ⁻¹ᵁ U).ι ≫ g) (morphismRestrict_ι g U).symm).inv ≫
          (upperStarComp AddCommGrpCat.{u + 1} (g ⁻¹ᵁ U).ι g).hom).app G) q).comp
        (cohomologyMap (g ∣_ U) ((upperStar AddCommGrpCat.{u + 1} (U.ι)).obj G) q)) ∧
    (∀ q, pV q = (Sheaf.H.map
        (((upperStarComp AddCommGrpCat.{u + 1} (g ∣_ V) V.ι
            ((g ⁻¹ᵁ V).ι ≫ g) (morphismRestrict_ι g V).symm).inv ≫
          (upperStarComp AddCommGrpCat.{u + 1} (g ⁻¹ᵁ V).ι g).hom).app G) q).comp
        (cohomologyMap (g ∣_ V) ((upperStar AddCommGrpCat.{u + 1} (V.ι)).obj G) q)) ∧
    (∀ q, pI q = (Sheaf.H.map
        (((upperStarComp AddCommGrpCat.{u + 1} (g ∣_ (U ⊓ V)) (U ⊓ V).ι
            ((g ⁻¹ᵁ (U ⊓ V)).ι ≫ g) (morphismRestrict_ι g (U ⊓ V)).symm).inv ≫
          (upperStarComp AddCommGrpCat.{u + 1} (g ⁻¹ᵁ (U ⊓ V)).ι g).hom).app G) q).comp
        (cohomologyMap (g ∣_ (U ⊓ V)) ((upperStar AddCommGrpCat.{u + 1} ((U ⊓ V).ι)).obj G) q)) ∧
    Function.Injective (fun x : Sheaf.H G 0 => (rXU 0 x, rXV 0 x)) ∧
    (∀ q : ℕ, Function.Exact (fun x : Sheaf.H G q => (rXU q x, rXV q x))
        (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (U.ι)).obj G) q × Sheaf.H ((upperStar
        AddCommGrpCat.{u + 1} (V.ι)).obj G) q =>
          rXIU q x.1 - rXIV q x.2) ∧
      Function.Exact (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (U.ι)).obj G) q × Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} (V.ι)).obj G) q =>
          rXIU q x.1 - rXIV q x.2) (δX q) ∧
      Function.Exact (δX q)
        (fun x => (rXU (q + 1) x, rXV (q + 1) x))) ∧
    Function.Injective (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g)).obj G) 0 => (rYU 0
        x, rYV 0 x)) ∧
    (∀ q : ℕ, Function.Exact (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g)).obj G) q =>
        (rYU q x, rYV q x))
        (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ U).ι)).obj ((upperStar
        AddCommGrpCat.{u + 1} (g)).obj G)) q × Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ
        V).ι)).obj ((upperStar AddCommGrpCat.{u + 1} (g)).obj G)) q =>
          rYIU q x.1 - rYIV q x.2) ∧
      Function.Exact (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ U).ι)).obj
        ((upperStar AddCommGrpCat.{u + 1} (g)).obj G)) q × Sheaf.H ((upperStar AddCommGrpCat.{u +
        1} ((g ⁻¹ᵁ V).ι)).obj ((upperStar AddCommGrpCat.{u + 1} (g)).obj G)) q =>
          rYIU q x.1 - rYIV q x.2) (δY q) ∧
      Function.Exact (δY q)
        (fun x => (rYU (q + 1) x, rYV (q + 1) x))) ∧
    (∀ q : ℕ, ∀ x : Sheaf.H G q,
      rYU q (cohomologyMap g G q x) = pU q (rXU q x) ∧
      rYV q (cohomologyMap g G q x) = pV q (rXV q x)) ∧
    (∀ q : ℕ, ∀ x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (U.ι)).obj G) q × Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} (V.ι)).obj G) q,
      rYIU q (pU q x.1) - rYIV q (pV q x.2) =
        pI q (rXIU q x.1 - rXIV q x.2)) ∧
    (∀ q : ℕ, ∀ x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((U ⊓ V).ι)).obj G) q,
      δY q (pI q x) = cohomologyMap g G (q + 1) (δX q x)) := by
  obtain ⟨δX, δY, hX0, hX, hY0, hY, hδ⟩ :=
    etale_mayerVietoris_connecting_pullback g U V hcover G
  refine ⟨cohomologyMap U.ι G, cohomologyMap V.ι G,
    openCohomologyRestriction (inf_le_left : U ⊓ V ≤ U) G,
    openCohomologyRestriction (inf_le_right : U ⊓ V ≤ V) G,
    cohomologyMap (g ⁻¹ᵁ U).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G),
    cohomologyMap (g ⁻¹ᵁ V).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G),
    openCohomologyRestriction (g.preimage_mono (inf_le_left : U ⊓ V ≤ U))
      ((upperStar AddCommGrpCat.{u + 1} g).obj G),
    openCohomologyRestriction (g.preimage_mono (inf_le_right : U ⊓ V ≤ V))
      ((upperStar AddCommGrpCat.{u + 1} g).obj G),
    openCohomologyPullback g U G, openCohomologyPullback g V G,
    openCohomologyPullback g (U ⊓ V) G, δX, δY, ?_⟩
  refine ⟨fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl,
    fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl,
    fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, hX0, hX, hY0, hY, ?_, ?_, hδ⟩
  · intro q x
    exact ⟨openCohomologyPullback_restrict g U G q x,
      openCohomologyPullback_restrict g V G q x⟩
  · intro q x
    rw [openCohomologyPullback_restriction g (inf_le_left : U ⊓ V ≤ U),
      openCohomologyPullback_restriction g (inf_le_right : U ⊓ V ≤ V)]
    exact (openCohomologyPullback g (U ⊓ V) G q).map_sub _ _ |>.symm

end AlgebraicGeometry.Etale
