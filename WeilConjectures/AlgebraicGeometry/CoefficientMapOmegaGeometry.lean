/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeCoefficientExtensionData
import all WeilConjectures.AlgebraicGeometry.CoefficientExceptionalGeometryOfCube
import all WeilConjectures.CategoryTheory.ExchangeMateCube
import WeilConjectures.CategoryTheory.PointwiseExchangeMateCube
import WeilConjectures.AlgebraicGeometry.EtaleScalarPullbackUnitCoherence

/-! # The coefficient-unit specialization of exceptional geometric compatibility -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

private theorem exceptional_coefficient_naturality_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    {N M : Cat A S} (a : N ⟶ M) (ha : IsIso a) :
    (scalarExtension φ X).map ((rightDerivedUpperShriek A f).map a) ≫
        ExceptionalCoefficients.mateMap φ f M =
      ExceptionalCoefficients.mateMap φ f N ≫
        (rightDerivedUpperShriek B f).map ((scalarExtension φ S).map a) := by
  exact pointwiseExchangeMate_naturality_iso
    (rightDerivedUpperShriekAdjunction A f) (rightDerivedUpperShriekAdjunction B f)
    (compactCoefficientInv φ f)
    (fun b hb ↦ compactCoefficientInv_naturality_iso φ f b hb) a ha

private theorem exceptional_geometric_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S S' : Scheme.{u}} (f : X ⟶ S) [HasCompactification f] [QuasiCompact f]
    (g : S' ⟶ S) {N M : Cat A S} (a : N ⟶ M) :
    (Sites.pull A (pullback.fst f g)).map ((rightDerivedUpperShriek A f).map a) ≫
        smoothExceptionalBaseChangeMap A f g M =
      smoothExceptionalBaseChangeMap A f g N ≫
        (rightDerivedUpperShriek A (pullback.snd f g)).map ((Sites.pull A g).map a) := by
  let sq := IsPullback.of_hasPullback f g
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  let θ := (asIso (rightDerivedLowerShriekBaseChangeMap A sq)).inv
  have h := (mateEquiv (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction A (pullback.snd f g))
    (TwoSquare.mk _ _ _ _ θ)).natTrans.naturality a
  simpa only [Functor.comp_map, mate_app_eq_adjunct,
    smoothExceptionalBaseChangeMap, θ, asIso_inv, NatIso.isIso_inv_app,
    Functor.id_obj, Sites.pull, sq] using h

/-- Unit coherence turns exceptional geometric compatibility into dualizing compatibility.
Source: blueprint latest, coefficient-extension proof, final paragraph.
(blueprint: lem-sf-coefficient-omega-geometry-of-exceptional).
Proof: expand each dualizing arrow into its exceptional coefficient or geometric
map followed by the coefficient-unit identification. Naturality of the coefficient
mate along the pullback-unit isomorphism moves that identification to the target.
The scalar/pullback unit law identifies the two resulting unit maps. Substitute
the exceptional square at the unit, then use naturality of exceptional geometric
base change at the scalar-unit identification. The remaining factors are exactly
the two asserted dualizing composites. -/
theorem coefficient_map_omega_geometry_of_exceptional
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
    (c : Compactification f) (S' : Scheme.{u}) (e : S' ≅ S)
    (he : letI := c.hasCompactification
      ExceptionalCoefficients.BaseChangeCompatibility φ f e.hom (𝟙_ _)) :
    let := c.hasCompactification
    (scalarExtension φ (pullback f e.hom)).map
        (smoothDualizingBaseChangeMap A f e.hom) ≫
      omegaMap φ (c.baseChange e.hom) =
    (Sites.scalarPull φ (pullback.fst f e.hom)).inv.app (omega A c) ≫
      (Sites.pull B (pullback.fst f e.hom)).map (omegaMap φ c) ≫
      smoothDualizingBaseChangeMap B f e.hom := by
  let := c.hasCompactification
  let g := e.hom
  let h := pullback.fst f g
  let j := pullback.snd f g
  let Q := scalarExtension φ (pullback f g)
  let G := rightDerivedUpperShriek B j
  let uA := (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g).hom
  let uB := (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} B) g).hom
  let s := (ExceptionalCoefficients.unitIso φ S).hom
  let s' := (ExceptionalCoefficients.unitIso φ S').hom
  have hu : (scalarExtension φ S').map uA ≫ s' =
      (Sites.scalarPull φ g).inv.app (𝟙_ (Cat A S)) ≫
        (Sites.pull B g).map s ≫ uB := by
    apply (cancel_epi ((Sites.scalarPull φ g).hom.app (𝟙_ _))).1
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, uA, uB, s, s',
      Sites.scalarPull, Sites.pull] using etaleScalarPullback_unit φ g
  have hn := exceptional_coefficient_naturality_iso φ j uA (inferInstance)
  have hb := exceptional_geometric_naturality B f g s
  dsimp only [ExceptionalCoefficients.BaseChangeCompatibility] at he
  dsimp only [omegaMap, smoothDualizingBaseChangeMap, omega, upper, dualizingComplex]
  dsimp only [Sites.pull, Sites.scalarPull] at hu hb ⊢
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [← G.map_comp, hu, G.map_comp, G.map_comp]
  rw [reassoc_of% he]
  rw [← reassoc_of% hb]

end WeilConjectures.FiniteFreeCoefficients
