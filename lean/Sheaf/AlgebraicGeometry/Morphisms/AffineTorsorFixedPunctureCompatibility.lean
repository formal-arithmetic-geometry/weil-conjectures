module

public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Comma.Over.Basic

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The descended affine isomorphism has the required projection compatibility.

Source: Stacks Project, Tags 03SF and 0EYG. Under the identifications used in the
geometric fixed-orbit construction, all maps are over H; functoriality of pullback
and the universal property of the principal open therefore give the displayed
projection equation. This is the compatibility step left from the descent argument.
(blueprint: lem-sbc-affine-torsor-fixed-puncture-compatibility)
-/
theorem affine_torsor_fixed_orbits_compatibility
    {R H : CommRingCat.{u}} {ι : R →+* H}
    {Y : Scheme.{u}} {p : Y ⟶ Spec R}
    {B : Type u} [CommRing B] [Algebra H B]
    {V : (Spec (CommRingCat.of B)).Opens}
    (θ : Over.mk (pullback.snd p (Spec.map (CommRingCat.ofHom ι))) ≅
      Over.mk (V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H B)))) :
    θ.hom.left ≫ V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H B)) =
      pullback.snd p (Spec.map (CommRingCat.ofHom ι)) := by
  exact Over.w θ.hom

/-- A counterexample using the swap of the two components of Spec (ℤ × ℤ).
This proof uses only Mathlib; it does not use the disputed theorem. -/
private theorem fixed_orbits_compatibility_counterexample :
    let H := CommRingCat.of (ℤ × ℤ)
    let a := Spec.map (CommRingCat.ofHom (RingHom.id (ℤ × ℤ)))
    let V : (Spec H).Opens := ⊤
    ∃ (θ : pullback (𝟙 (Spec H)) a ≅ V.toScheme) (q : Spec H ⟶ Spec H),
      θ.hom ≫ V.ι ≫ q ≠ pullback.snd (𝟙 (Spec H)) a := by
  dsimp only
  let X := Spec (CommRingCat.of (ℤ × ℤ))
  let a := Spec.map (CommRingCat.ofHom (RingHom.id (ℤ × ℤ)))
  let θ := asIso (pullback.snd (𝟙 X) a) ≪≫ X.topIso.symm
  let q := Spec.map (CommRingCat.ofHom
    (RingEquiv.prodComm : ℤ × ℤ ≃+* ℤ × ℤ).toRingHom)
  refine ⟨θ, q, ?_⟩
  change θ.hom ≫ X.topIso.hom ≫ q ≠ pullback.snd (𝟙 X) a
  have he : θ.hom ≫ X.topIso.hom = pullback.snd (𝟙 X) a := by
    change pullback.snd (𝟙 X) a ≫ X.topIso.inv ≫ X.topIso.hom = _
    rw [Iso.inv_hom_id, Category.comp_id]
  intro h
  rw [← Category.assoc, he] at h
  have hq : q = 𝟙 X := (cancel_epi (pullback.snd (𝟙 X) a)).mp
    (h.trans (Category.comp_id _).symm)
  have hr : CommRingCat.ofHom
      (RingEquiv.prodComm : ℤ × ℤ ≃+* ℤ × ℤ).toRingHom =
      CommRingCat.ofHom (RingHom.id (ℤ × ℤ)) := by
    apply Spec.map_injective
    simpa [q, X] using hq
  have hz := congrArg (fun f => f.hom (0, 1)) hr
  have : (1 : ℤ) = 0 := congrArg Prod.fst hz
  exact one_ne_zero this

end AlgebraicGeometry.Scheme
