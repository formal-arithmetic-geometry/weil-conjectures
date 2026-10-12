/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GeometricGenericFibre
public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-!
# Geometric generic restriction and exceptional restriction to a closed subscheme

Over a smooth integral curve `B`, pullback `g` to the geometric generic fibre commutes with
the exceptional restriction `Ri^!` along a closed immersion `i`
(`lem-weil-geometric-generic-exchange`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]

section GeometricGenericFibre

variable {B : Scheme.{u}} [IsIntegral B]

/-- The geometric generic fibre square of a `B`-morphism `h : T ⟶ X` is cartesian:
`T_η̄ = T ×_X X_η̄`. -/
lemma isPullback_geometricGenericFibreMap {X T : Scheme.{u}} {πX : X ⟶ B} {πT : T ⟶ B}
    (h : T ⟶ X) (hh : h ≫ πX = πT) :
    IsPullback (pullback.fst πT B.geometricGenericPoint) (geometricGenericFibreMap h hh) h
      (pullback.fst πX B.geometricGenericPoint) := by
  subst hh
  refine IsPullback.of_bot ?_ (geometricGenericFibreMap_commSq h rfl).w
    (IsPullback.of_hasPullback πX B.geometricGenericPoint)
  simpa [geometricGenericFibreMap] using
    IsPullback.of_hasPullback (h ≫ πX) B.geometricGenericPoint

/-- The base change `h_η̄` of an open immersion `h` is an open immersion. -/
instance isOpenImmersion_geometricGenericFibreMap {X T : Scheme.{u}} {πX : X ⟶ B}
    {πT : T ⟶ B} (h : T ⟶ X) [IsOpenImmersion h] (hh : h ≫ πX = πT) :
    IsOpenImmersion (geometricGenericFibreMap h hh) :=
  MorphismProperty.of_isPullback (isPullback_geometricGenericFibreMap h hh) inferInstance

/-- The range of `h_η̄` is the inverse image of the range of `h` in the geometric generic
fibre. -/
lemma range_geometricGenericFibreMap {X T : Scheme.{u}} {πX : X ⟶ B} {πT : T ⟶ B}
    (h : T ⟶ X) (hh : h ≫ πX = πT) :
    Set.range (geometricGenericFibreMap h hh) =
      pullback.fst πX B.geometricGenericPoint ⁻¹' Set.range h := by
  have hp := isPullback_geometricGenericFibreMap h hh
  have hsurj : Function.Surjective ⇑hp.isoPullback.hom := by
    have := (Scheme.homeoOfIso hp.isoPullback).surjective
    rwa [Scheme.coe_homeoOfIso] at this
  rw [← hp.isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_snd]

end GeometricGenericFibre

section Exchange

variable {B : Scheme.{u}} [IsIntegral B] (b : B ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 b]

include b

/-- The supported localization triangle commutes with geometric generic pullback: for a closed
immersion `i : Z ⟶ X` of `B`-schemes and `M ∈ Dᵇc(X, Λ)`, the supported part
`g_X^* Ri_! Ri^! M` is isomorphic to `Ri_{η̄ !} Ri_{η̄}^! g_X^* M`.

The pullback of the supported localization triangle of `M` maps to the supported localization
triangle of `g_X^* M` by the identity of `g_X^* M` and the base change isomorphism
`g_X^* Rj_* j^* M ≅ Rj_{η̄ *} j_{η̄}^* g_X^* M` for the open complement `j` (the first
comparison), which is compatible with the adjunction units. -/
theorem nonempty_iso_leftDerivedUpperStar_rightDerivedLowerShriek_rightDerivedUpperShriek
    {X Z : Scheme.{u}} (πX : X ⟶ B) [LocallyOfFiniteType πX] [QuasiCompact πX] (i : Z ⟶ X)
    [IsClosedImmersion i]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
    Nonempty ((L((pullback.fst πX B.geometricGenericPoint)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj M)) ≅
      (R(geometricGenericFibreMap (πX := πX) i rfl)_![ModuleCat.{u + 1} Λ]).obj
        ((R(geometricGenericFibreMap (πX := πX) i rfl)^![ModuleCat.{u + 1} Λ]).obj
          ((L((pullback.fst πX B.geometricGenericPoint)^*[ModuleCat.{u + 1} Λ])).obj M))) := by
  let A := ModuleCat.{u + 1} Λ
  let j := i.openComplement.ι
  let gX := pullback.fst πX B.geometricGenericPoint
  let i' := geometricGenericFibreMap (πX := πX) i rfl
  let j' := geometricGenericFibreMap (πX := πX) j rfl
  have hij : Set.range i.base = (Set.range j.base)ᶜ := i.range_eq_compl_range_openComplement_ι
  have hij' : Set.range i'.base = (Set.range j'.base)ᶜ := by
    rw [range_geometricGenericFibreMap, range_geometricGenericFibreMap, hij, Set.preimage_compl]
  have := SmoothOfRelativeDimension.smooth 1 b
  have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian b
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian πX
  -- base change along `j`, by the first comparison
  have sqj := geometricGenericFibreMap_commSq (πX := πX) j rfl
  have : IsIso ((derivedBaseChangeMap A sqj).app ((L((j)^*[A])).obj M)) :=
    isIso_derivedBaseChangeMap_geometricGenericPoint Λ b πX (j ≫ πX) j rfl
      (boundedConstructible_leftDerivedUpperStar _ j hM)
  -- compare the pulled back supported localization triangle with that of the generic fibre
  have hT := (L((gX)^*[A])).map_distinguished _
    (supportedLocalizationTriangle_mem_distTriang A i j hij M)
  have hT' := supportedLocalizationTriangle_mem_distTriang A i' j' hij' ((L((gX)^*[A])).obj M)
  let c := (derivedBaseChangeMap A sqj).app ((L((j)^*[A])).obj M) ≫
    (R((j')_*[A])).map ((derivedSquareUpperStarIso A sqj).inv.app M)
  have hc : (L((gX)^*[A])).map ((derivedUpperStarLowerStarAdjunction A j).unit.app M) ≫ c =
      (derivedUpperStarLowerStarAdjunction A j').unit.app ((L((gX)^*[A])).obj M) := by
    refine (map_unit_derivedBaseChangeMap_app_assoc A sqj M _).trans ?_
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  obtain ⟨a, ha₁, ha₃⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁ _ _ hT hT'
    (𝟙 _) c (hc.trans (Category.id_comp _).symm)
  have : IsIso a := Pretriangulated.isIso₁_of_isIso₂₃ (T := _) (T' := _)
    { hom₁ := a, hom₂ := 𝟙 _, hom₃ := c, comm₁ := ha₁,
      comm₂ := hc.trans (Category.id_comp _).symm, comm₃ := ha₃ } hT hT'
    (by dsimp; infer_instance) (by dsimp [c]; infer_instance)
  exact ⟨asIso a⟩

/-- Blueprint `lem-weil-geometric-generic-exchange`: Restriction to the geometric generic fibre.

Let `B` be a smooth integral curve over `k`, `η̄` its geometric generic point and `g` the
geometric generic pullback on `B`-schemes of finite type. For a closed immersion `i : Z ⟶ X`
of `B`-schemes and `M ∈ Dᵇc(X, Λ)`, the exceptional restriction commutes with `g`:
`g_Z^* Ri^! M ≅ Ri_{η̄}^! g_X^* M`.

Proper base change identifies `g_X^* Ri_! Ri^! M` with `Ri_{η̄ !} g_Z^* Ri^! M`, and the
supported localization triangle with `Ri_{η̄ !} Ri_{η̄}^! g_X^* M`
(`nonempty_iso_leftDerivedUpperStar_rightDerivedLowerShriek_rightDerivedUpperShriek`); conclude
by full faithfulness of `Ri_{η̄ !}`. -/
theorem nonempty_iso_leftDerivedUpperStar_rightDerivedUpperShriek_geometricGenericPoint
    {X Z : Scheme.{u}} (πX : X ⟶ B) [LocallyOfFiniteType πX] [QuasiCompact πX] (i : Z ⟶ X)
    [IsClosedImmersion i]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
    Nonempty ((L((pullback.fst (i ≫ πX) B.geometricGenericPoint)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(i)^![ModuleCat.{u + 1} Λ]).obj M) ≅
      (R(geometricGenericFibreMap i rfl)^![ModuleCat.{u + 1} Λ]).obj
        ((L((pullback.fst πX B.geometricGenericPoint)^*[ModuleCat.{u + 1} Λ])).obj M)) := by
  let A := ModuleCat.{u + 1} Λ
  let i' := geometricGenericFibreMap (πX := πX) i rfl
  have hi' := isPullback_geometricGenericFibreMap (πX := πX) i rfl
  let N := (R(i)^![A]).obj M
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite hi'
  have : IsIso ((derivedBaseChangeMap A hi'.toCommSq).app N) := NatIso.isIso_app_of_isIso _ _
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_rightDerivedLowerShriek_rightDerivedUpperShriek
    Λ b πX i hM
  have := isIso_rightDerivedUpperShriekAdjunction_unit_app A i'
  have : IsIso (rightDerivedUpperShriekAdjunction A i').unit := NatIso.isIso_of_isIso_app _
  exact ⟨(rightDerivedUpperShriekAdjunction A i').fullyFaithfulLOfIsIsoUnit.preimageIso
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar A i').app _ ≪≫
      (asIso ((derivedBaseChangeMap A hi'.toCommSq).app N)).symm ≪≫
      (L((pullback.fst πX B.geometricGenericPoint)^*[A])).mapIso
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar A i).app N).symm ≪≫ e)⟩

end Exchange

end Etale

end AlgebraicGeometry
