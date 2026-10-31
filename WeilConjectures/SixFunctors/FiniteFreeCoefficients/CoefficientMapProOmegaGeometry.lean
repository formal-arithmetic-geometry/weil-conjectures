/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientSitePullCube
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDualitySiteComparison

/-! # Transport of the dualizing coefficient square to the pro-etale site -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/-- The prescribed dualizing site bridge is invertible on the regular coefficient unit.
Source: blueprint latest, coefficient-extension proof, site transport paragraph.
(blueprint: lem-sf-coefficient-pro-omega-geometry-of-ordinary).
Proof: the comparison-adjunction unit is invertible on the degree-zero regular
coefficient sheaf. Its composition with the degree-zero unit transport is therefore
invertible. Apply the exceptional functor and then exact site pullback to this
isomorphism. These are exactly the two functors defining omegaBridge. -/
theorem coefficient_omega_bridge_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f) :
    IsIso (Sites.omegaBridge A c) := by
  have := ProEtale.isIso_baseUnit (ModuleCat.{u + 1} A) S
    (ProEtale.comparisonUpperStarUnitIso A S).hom
  unfold Sites.omegaBridge
  infer_instance

/-- The ordinary dualizing square transports through the actual site comparisons.
Source: blueprint latest, coefficient-extension proof, final paragraph.
(blueprint: lem-sf-coefficient-pro-omega-geometry-of-ordinary).
Proof: the four unit bridges are invertible. Expand proOmegaMap and proOmegaPull
and cancel the two adjacent bridge/inverse pairs. Scalar/site naturality moves
ordinary dualizing base change through scalarSite. The scalar/site/pullback cube
then reduces the middle factors to site pullback of the ordinary dualizing square.
Use sitePull naturality at the ordinary coefficient map, and scalar/pullback
naturality at the inverse bridge. This gives the second transported composite. -/
theorem coefficient_map_pro_omega_geometry_of_ordinary
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
    (c : Compactification f)
    (ho : letI := c.hasCompactification
      ∀ (S' : Scheme.{u}) (e : S' ≅ S),
        (Etale.scalarExtension φ (pullback f e.hom)).map
            (Etale.smoothDualizingBaseChangeMap A f e.hom) ≫
          omegaMap φ (c.baseChange e.hom) =
        (Sites.scalarPull φ (pullback.fst f e.hom)).inv.app (omega A c) ≫
          (Sites.pull B (pullback.fst f e.hom)).map (omegaMap φ c) ≫
          Etale.smoothDualizingBaseChangeMap B f e.hom) :
    Sites.ProOmegaGeometry φ c := by
  let := c.hasCompactification
  intro S' e
  let h := pullback.fst f e.hom
  let U := pullback f e.hom
  let W := omega A c
  let V := omega B c
  let W' := omega A (c.baseChange e.hom)
  let V' := omega B (c.baseChange e.hom)
  let α := omegaMap φ c
  let α' := omegaMap φ (c.baseChange e.hom)
  let β : (Sites.pull A h).obj W ⟶ W' :=
    Etale.smoothDualizingBaseChangeMap A f e.hom
  let β' : (Sites.pull B h).obj V ⟶ V' :=
    Etale.smoothDualizingBaseChangeMap B f e.hom
  have := coefficient_omega_bridge_isIso A c
  have := coefficient_omega_bridge_isIso B c
  have := coefficient_omega_bridge_isIso A (c.baseChange e.hom)
  have := coefficient_omega_bridge_isIso B (c.baseChange e.hom)
  let w := asIso (Sites.omegaBridge A c)
  let v := asIso (Sites.omegaBridge B c)
  let w' := asIso (Sites.omegaBridge A (c.baseChange e.hom))
  let v' := asIso (Sites.omegaBridge B (c.baseChange e.hom))
  have hw : Sites.inverseOnDomain (Sites.omegaBridge A c) = w.inv := by
    simp only [Sites.inverseOnDomain, dif_pos (inferInstance : IsIso
      (Sites.omegaBridge A c))]
    rfl
  have hv : Sites.inverseOnDomain (Sites.omegaBridge B c) = v.inv := by
    simp only [Sites.inverseOnDomain, dif_pos (inferInstance : IsIso
      (Sites.omegaBridge B c))]
    rfl
  have hw' : Sites.inverseOnDomain (Sites.omegaBridge A (c.baseChange e.hom)) =
      w'.inv := by
    simp only [Sites.inverseOnDomain, dif_pos (inferInstance : IsIso
      (Sites.omegaBridge A (c.baseChange e.hom)))]
    rfl
  have hn := (Sites.scalarSite φ U).hom.naturality β
  have hp := (Sites.sitePull B h).hom.naturality α
  have hl := (Sites.proScalarPull φ h).inv.naturality w.inv
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hp hl
  have hc := congrArg (fun z ↦
    (Sites.proScalarPull φ h).inv.app ((Sites.nu A X).obj W) ≫ z)
    (coefficient_site_pull_cube φ h W)
  simp only [Iso.inv_hom_id_app_assoc] at hc
  have hm := congrArg (fun z ↦ (Sites.nu B U).map z) (ho S' e)
  simp only [Functor.map_comp] at hm
  unfold Sites.proOmegaPull Sites.proOmegaMap
  rw [hw, hv, hw']
  simp only [Functor.map_comp, Category.assoc]
  change (Sites.scalar true φ U).map ((Sites.proPull A h).map w.inv) ≫
      (Sites.scalar true φ U).map ((Sites.sitePull A h).hom.app W) ≫
      (Sites.scalar true φ U).map ((Sites.nu A U).map β) ≫
      (Sites.scalar true φ U).map w'.hom ≫
      (Sites.scalar true φ U).map w'.inv ≫
      (Sites.scalarSite φ U).hom.app W' ≫ (Sites.nu B U).map α' ≫ v'.hom =
    (Sites.proScalarPull φ h).inv.app (Sites.omega true A c) ≫
      (Sites.proPull B h).map ((Sites.scalar true φ X).map w.inv) ≫
      (Sites.proPull B h).map ((Sites.scalarSite φ X).hom.app W) ≫
      (Sites.proPull B h).map ((Sites.nu B X).map α) ≫
      (Sites.proPull B h).map v.hom ≫ (Sites.proPull B h).map v.inv ≫
      (Sites.sitePull B h).hom.app V ≫ (Sites.nu B U).map β' ≫ v'.hom
  rw [← (Sites.scalar true φ U).map_comp_assoc w'.hom w'.inv,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← (Sites.proPull B h).map_comp_assoc v.hom v.inv,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [reassoc_of% hn, reassoc_of% hc]
  erw [reassoc_of% hm]
  rw [← (Sites.nu B U).map_comp_assoc
    ((Sites.scalarPull φ h).hom.app W) ((Sites.scalarPull φ h).inv.app W),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← reassoc_of% hp, reassoc_of% hl]

end WeilConjectures.FiniteFreeCoefficients
