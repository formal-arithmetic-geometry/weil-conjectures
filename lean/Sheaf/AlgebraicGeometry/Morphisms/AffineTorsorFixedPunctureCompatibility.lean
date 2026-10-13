module

public import Mathlib.AlgebraicGeometry.Limits

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
    (θ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅ V.toScheme)
    (q : Spec (CommRingCat.of B) ⟶ Spec H) :
    θ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom ι)) := by
  sorry

end AlgebraicGeometry.Scheme
