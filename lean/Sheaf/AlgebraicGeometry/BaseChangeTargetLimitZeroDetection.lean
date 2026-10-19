/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeStalkTransition
import Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison
import Sheaf.AlgebraicGeometry.BaseChangeTargetLimitGeometry

/-! # Finite-stage detection of zero in target stalks

Source: Stacks Project Tag 09Z1 and the limit step of Tag 0F07.
(blueprint: lem-sbc-target-limit-zero-detection)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X S T : Scheme.{u}} [IsAffine S]
variable (p : X ⟶ S) (g : T ⟶ S) (q : ℤ)
variable (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over T)
variable [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
variable [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]

/-- A target-stalk element that dies at the limit dies after a transition in the diagram.

Source: Stacks Tag 09Z1, applied to the target side in Tag 0F07 condition (2).
(blueprint: lem-sbc-target-limit-zero-detection)

Proof: Base change the cone of schemes along p. The resulting cone is a limit cone,
and its transition maps are affine. The structure maps to X are base changes of the
qcqs stage maps to the affine S, so they and the limit structure map are qcqs. On the
resulting system pull back the fixed sheaf F from Y = T ×_S X. The inverse-image
composition isomorphisms identify these coefficients with e_i^* (π_i^* F), and identify
the restriction maps with baseChangeTargetStalkMap. Higher-direct-image continuity
therefore expresses the limit target sheaf as the filtered colimit of the stage target
sheaves. Taking the geometric stalk preserves this colimit. The elementwise zero
criterion for a filtered colimit of modules says that a representative whose image is
zero is already zero at some later stage. In negative degree the target sheaves are
zero and one can take j = i and the identity. This is the asserted criterion.
-/
theorem baseChange_target_limit_zero_detection (c : Cone D)
    (hc : IsLimit ((Over.forget T).mapCone c)) (i : I)
    (ζ : baseChangeTargetStalk Λ p g q F x (D.obj i))
    (hζ : (baseChangeTargetStalkMap Λ p g q F x (c.π.app i)).hom ζ = 0) :
    ∃ (j : I) (f : j ⟶ i),
      (baseChangeTargetStalkMap Λ p g q F x (D.map f)).hom ζ = 0 := by
  let B := Over.pullback (pullback.fst g p)
  let G := ((pullback.fst g p)^*[ModuleCat.{u + 1} Λ]).obj F
  obtain ⟨ha, hqc, hqs, hlqc, hlqs, hlim⟩ :=
    baseChange_target_limit_geometry p g D c hc
  let : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((D ⋙ B).map f).left := ha
  let : ∀ i, QuasiCompact (((D ⋙ B).obj i).hom ≫ pullback.snd g p) := hqc
  let : ∀ i, QuasiSeparated (((D ⋙ B).obj i).hom ≫ pullback.snd g p) := hqs
  let : QuasiCompact ((B.mapCone c).pt.hom ≫ pullback.snd g p) := hlqc
  let : QuasiSeparated ((B.mapCone c).pt.hom ≫ pullback.snd g p) := hlqs
  obtain ⟨E, hE⟩ := baseChange_target_stalk_higher_image_comparison Λ p g q F x
  have hz : ((X.uliftPointSmallEtale x).sheafFiber.map
      (higherDirectImageOverMap Λ (pullback.snd g p) G q
        ((B.mapCone c).π.app i))).hom ((E (D.obj i)).hom.hom ζ) = 0 := by
    have hw := congrArg (fun f ↦ f.hom ζ) (hE c.pt (D.obj i) (c.π.app i))
    dsimp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hw
    change (E c.pt).hom.hom
      ((baseChangeTargetStalkMap Λ p g q F x (c.π.app i)).hom ζ) = _ at hw
    rw [hζ, map_zero] at hw
    exact hw.symm
  obtain ⟨j, f, hf⟩ :=
    (higherDirectImage_limit Λ (pullback.snd g p) G (D ⋙ B) (B.mapCone c)
      hlim.some q x).2 i ((E (D.obj i)).hom.hom ζ) hz
  refine ⟨j, f, ?_⟩
  have hw := congrArg (fun h ↦ h.hom ζ) (hE (D.obj j) (D.obj i) (D.map f))
  have he : (E (D.obj j)).hom.hom
      ((baseChangeTargetStalkMap Λ p g q F x (D.map f)).hom ζ) = 0 := by
    dsimp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hw
    change _ = ((X.uliftPointSmallEtale x).sheafFiber.map
      (higherDirectImageOverMap Λ (pullback.snd g p) G q
        ((D ⋙ B).map f))).hom ((E (D.obj i)).hom.hom ζ) at hw
    rw [hf] at hw
    exact hw
  exact (ConcreteCategory.bijective_of_isIso (E (D.obj j)).hom).1
    (by simpa only [map_zero] using he)


end AlgebraicGeometry.Etale
