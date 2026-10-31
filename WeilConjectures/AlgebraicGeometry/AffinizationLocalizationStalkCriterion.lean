/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.AlgebraicGeometry.RingedSubspace
import WeilConjectures.Topology.InverseImageStalk
import Mathlib.Geometry.RingedSpace.OpenImmersion

/-!
# Stalk criterion for affinization from stage prime localizations

Source: Stacks Project, Tag 0API, proof of `lemma-sits-in-functions`, the sentence
beginning "For any e" and the restricted structure-sheaf identification.
(blueprint: lem-a1-affinization-localization-stalk-criterion)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

set_option backward.isDefEq.respectTransparency false in
private theorem localization_stages_bijective
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (A : I ⥤ CommRingCat.{u}) (C : CommRingCat.{u})
    (r : A ⟶ (Functor.const I).obj C) (hc : IsColimit (Cocone.mk C r))
    (p : Ideal C) [p.IsPrime]
    (S : Type u) [CommRing S] [Algebra C S] [IsLocalization p.primeCompl S]
    (B : CommRingCat.{u}) (f : S →+* B)
    (hs : ∀ i : I,
      ∃ θ : Localization.AtPrime (p.comap (r.app i).hom) →+* B,
        θ.comp (algebraMap (A.obj i) _) = (f.comp (algebraMap C S)).comp (r.app i).hom ∧
        Function.Bijective θ) : Function.Bijective f := by
  classical
  let k (i : I) : Localization.AtPrime (p.comap (r.app i).hom) →+* S :=
    IsLocalization.lift (S := Localization.AtPrime (p.comap (r.app i).hom))
      (g := (algebraMap C S).comp (r.app i).hom)
      (fun (s : (p.comap (r.app i).hom).primeCompl) ↦ IsLocalization.map_units S
        (⟨r.app i s, s.property⟩ : p.primeCompl))
  have hk (i : I) (a : A.obj i) :
      k i (algebraMap (A.obj i) _ a) = algebraMap C S (r.app i a) :=
    IsLocalization.lift_eq _ a
  have hfk (i : I) : Function.Bijective (f.comp (k i)) := by
    obtain ⟨θ, hθ, hbij⟩ := hs i
    have he : f.comp (k i) = θ := by
      apply IsLocalization.ringHom_ext (p.comap (r.app i).hom).primeCompl
      ext a
      change f (k i (algebraMap (A.obj i) _ a)) = θ (algebraMap (A.obj i) _ a)
      rw [hk]
      exact (DFunLike.congr_fun hθ a).symm
    rwa [he]
  constructor
  · apply (injective_iff_map_eq_zero f).2
    intro x hx
    obtain ⟨⟨c, s⟩, he⟩ := IsLocalization.surj p.primeCompl x
    obtain ⟨i, a, ha⟩ := Concrete.isColimit_exists_rep A hc c
    have hz : f (algebraMap C S c) = 0 := by
      rw [← he, map_mul, hx, zero_mul]
    have hz' : algebraMap (A.obj i) (Localization.AtPrime (p.comap (r.app i).hom)) a = 0 := by
      apply (hfk i).1
      simpa only [RingHom.comp_apply, hk, ha, map_zero] using hz
    have hz'' : algebraMap C S c = 0 := by
      rw [← ha, ← hk, hz', map_zero]
    exact (IsLocalization.map_units S s).mul_right_cancel
      (by simpa only [zero_mul] using he.trans hz'')
  · obtain ⟨i⟩ := ‹Nonempty I›
    intro b
    obtain ⟨a, ha⟩ := (hfk i).2 b
    exact ⟨k i a, ha⟩

set_option backward.isDefEq.respectTransparency false in
/-- The canonical affinization is an isomorphism on stalks when every stage prime
localization maps isomorphically to the stalk. If its base is a homeomorphism onto a
subset, it factors through that subset with precisely the inverse-image structure sheaf.
Source: Stacks Project, Tag 0API, proof of `lemma-sits-in-functions`.
(blueprint: lem-a1-affinization-localization-stalk-criterion)

Proof:
1. For each z, use the spectrum-stalk localization and the affine adjunction's
   germ square to identify the global germ with the actual stalk map after C → C_q.
2. Lift each stage localization to the spectrum stalk. Localization uniqueness
   identifies its composite with the actual stalk map with the given stage isomorphism.
3. Surjectivity follows from any one stage. To prove injectivity, clear the denominator
   of a kernel element and lift its numerator to a stage by filtered-colimit
   representation. The stage isomorphism forces that numerator to vanish in the stage
   localization, hence in the spectrum stalk. Cancel the invertible denominator.
4. The inverse-image stalk theorem makes the canonical ringed-subspace inclusion
   an isomorphism on stalks. Transfer the local-ring structures along these maps.
5. The inverse-image adjunction factors the sheaf map of the affinization over h.
   Its unit equation proves the factorization equation, including the sheaf maps.
6. The composition equation makes the factor map an isomorphism on stalks.
   Mathlib's sheafed-space stalk criterion over a homeomorphism makes it an isomorphism.
   Lift it to locally ringed spaces and use faithfulness for the factorization equation.
-/
theorem affinization_localization_stalk_criterion
    (Z : LocallyRingedSpace.{u})
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (A : I ⥤ CommRingCat.{u})
    (r : A ⟶ (Functor.const I).obj (Γ.obj (op Z)))
    (_hcolim : IsColimit (Cocone.mk (Γ.obj (op Z)) r))
    (_hstage : ∀ (z : Z) (i : I),
      ∃ θ : CommRingCat.of (Localization.AtPrime
          ((Z.toΓSpecFun z).comap (r.app i).hom).asIdeal) ⟶ Z.presheaf.stalk z,
        CommRingCat.ofHom (algebraMap (A.obj i) (Localization.AtPrime
            ((Z.toΓSpecFun z).comap (r.app i).hom).asIdeal)) ≫ θ =
          r.app i ≫ Z.presheaf.Γgerm z ∧ IsIso θ) :
    (∀ z : Z, IsIso (Z.toΓSpec.stalkMap z) ∧
      IsIso (CommRingCat.ofHom
        (StructureSheaf.stalkIso (Γ.obj (op Z)) (Z.toΓSpecFun z)).toRingHom ≫
          Z.toΓSpec.stalkMap z)) ∧
    (∀ (F : Set (Spec.locallyRingedSpaceObj (Γ.obj (op Z))))
        (h : Z ≃ₜ F),
      (∀ z : Z, (h z).val = Z.toΓSpec.base z) →
      ∃ hlocal : ∀ x : F, IsLocalRing
          ((ringedSubspace (Spec.locallyRingedSpaceObj (Γ.obj (op Z))) F).presheaf.stalk x),
        ∃ (e : Z ≅ locallyRingedSubspace
            (Spec.locallyRingedSpaceObj (Γ.obj (op Z))) F hlocal)
          (ι : locallyRingedSubspace
            (Spec.locallyRingedSpaceObj (Γ.obj (op Z))) F hlocal ⟶
              Spec.locallyRingedSpaceObj (Γ.obj (op Z))),
          ι.toShHom = ringedSubspaceι (Spec.locallyRingedSpaceObj (Γ.obj (op Z))) F ∧
          e.hom ≫ ι = Z.toΓSpec) := by
  have hstalk : ∀ z : Z, IsIso (Z.toΓSpec.stalkMap z) := by
    intro z
    apply (ConcreteCategory.isIso_iff_bijective _).2
    apply localization_stages_bijective A (Γ.obj (op Z)) r _hcolim
      (Z.toΓSpecFun z).asIdeal
      ((Spec.structureSheaf (Γ.obj (op Z))).presheaf.stalk (Z.toΓSpecFun z))
      (Z.presheaf.stalk z) (Z.toΓSpec.stalkMap z).hom
    intro i
    obtain ⟨θ, hθ, hi⟩ := _hstage z i
    refine ⟨θ.hom, ?_, (ConcreteCategory.isIso_iff_bijective θ).1 hi⟩
    apply CommRingCat.hom_ext_iff.mp
    change CommRingCat.ofHom (algebraMap (A.obj i) _) ≫ θ =
      r.app i ≫ (StructureSheaf.toStalk _ _ ≫ Z.toΓSpec.stalkMap z)
    erw [Z.toStalk_stalkMap_toΓSpec]
    exact hθ
  refine ⟨fun z ↦ ⟨hstalk z, ?_⟩, ?_⟩
  · have := hstalk z
    have : IsIso (CommRingCat.ofHom
        (StructureSheaf.stalkIso (Γ.obj (op Z)) (Z.toΓSpecFun z)).toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).2
        (StructureSheaf.stalkIso (Γ.obj (op Z)) (Z.toΓSpecFun z)).bijective
    infer_instance
  · intro F h hh
    classical
    let Y := Spec.locallyRingedSpaceObj (Γ.obj (op Z))
    let i := subspaceInclusion Y F
    let H : Z.toTopCat ≅ TopCat.of F := TopCat.isoOfHomeo h
    have hw : H.hom ≫ i = Z.toΓSpec.base := by
      ext z
      exact hh z
    have hi (x : F) : IsIso ((ringedSubspaceι Y F).hom.stalkMap x) := by
      obtain ⟨c, hc, _⟩ := TopCat.Sheaf.exists_inverseImage_stalk_iso_commRing i x
      have he : (ringedSubspaceι Y F).hom.stalkMap x = (c.app Y.sheaf).hom := by
        apply TopCat.Presheaf.stalk_hom_ext
        intro V hV
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro s
        rw [PresheafedSpace.stalkMap_germ]
        exact (hc Y.sheaf V hV s).symm
      rw [he]
      infer_instance
    let hl : ∀ x : F, IsLocalRing ((ringedSubspace Y F).presheaf.stalk x) := fun x ↦
      (asIso ((ringedSubspaceι Y F).hom.stalkMap x)).commRingCatIsoToRingEquiv.isLocalRing
    let L := locallyRingedSubspace Y F hl
    have hiLocal (x : F) : IsLocalHom ((ringedSubspaceι Y F).hom.stalkMap x).hom :=
      isLocalHom_of_isIso _
    let incl : L ⟶ Y := homMk (ringedSubspaceι Y F) hiLocal
    let c : Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat i).obj
        ((TopCat.Sheaf.pushforward CommRingCat H.hom).obj Z.sheaf) :=
      ⟨Z.toΓSpec.c ≫ eqToHom (by rw [← hw]; rfl)⟩
    let α := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat i).homEquiv
      Y.sheaf ((TopCat.Sheaf.pushforward CommRingCat H.hom).obj Z.sheaf)).symm c
    have hα : ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat i).unit.app
        Y.sheaf) ≫ (TopCat.Sheaf.pushforward CommRingCat i).map α = c := by
      exact ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat i).homEquiv
        _ _).apply_symm_apply c
    let f : Z.toSheafedSpace ⟶ ringedSubspace Y F :=
      InducedCategory.homMk { base := H.hom, c := α.hom }
    have hcomp : f ≫ ringedSubspaceι Y F = Z.toΓSpec.toShHom := by
      apply InducedCategory.hom_ext
      apply PresheafedSpace.Hom.ext _ _ hw
      change (f ≫ ringedSubspaceι Y F).hom.c ≫ _ = Z.toΓSpec.c
      have he := congrArg (fun q ↦ q.hom) hα
      change (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat i).unit.app
        Y.sheaf) ≫ (TopCat.Sheaf.pushforward CommRingCat i).map α).hom ≫ _ = _
      rw [he]
      dsimp only [c]
      have ht : Functor.whiskerRight (eqToHom
          (show (TopologicalSpace.Opens.map (H.hom ≫ i)).op =
            (TopologicalSpace.Opens.map Z.toΓSpec.base).op by rw [hw])) Z.presheaf =
          eqToHom (by rw [hw]) := by
        ext U
        simp only [Functor.whiskerRight_app, eqToHom_app, eqToHom_map]
      rw [ht]
      simp
    have hfs (z : Z) : IsIso (f.hom.stalkMap z) := by
      have := hi (H.hom z)
      have ht : IsIso ((f ≫ ringedSubspaceι Y F).hom.stalkMap z) := by
        rw [hcomp]
        exact hstalk z
      change IsIso ((f.hom ≫ (ringedSubspaceι Y F).hom).stalkMap z) at ht
      rw [PresheafedSpace.stalkMap.comp] at ht
      exact IsIso.of_isIso_comp_left
        ((ringedSubspaceι Y F).hom.stalkMap (f.hom.base z)) (f.hom.stalkMap z)
    have hfOpen : Topology.IsOpenEmbedding f.hom.base := h.isOpenEmbedding
    have hf : SheafedSpace.IsOpenImmersion f :=
      SheafedSpace.IsOpenImmersion.of_stalk_iso f hfOpen
    have hbase : IsIso f.hom.base := H.isIso_hom
    have hfIso : IsIso f := SheafedSpace.IsOpenImmersion.to_iso f
    let e : Z ≅ L := isoOfSheafedSpaceIso (asIso f)
    refine ⟨hl, e, incl, rfl, ?_⟩
    apply (forgetToSheafedSpace.map_injective)
    exact hcomp

end AlgebraicGeometry.LocallyRingedSpace
