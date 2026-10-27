/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.FieldSeparableCechCoordinates
import Sheaf.Paper.ContinuousCoefficientModuleEncoding
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Analysis.Normed.Group.Ultra
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstantHom
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Continuous coefficient sections in Galois coordinates

Source: Hemo--Richarz--Scholbach, Example 3.1, p. 6; Bhatt--Scholze,
Lemma 4.2.12; the cumulative-vertex Cech calculation.
(blueprint: lem-sfb-galois-continuous-section-naturality).

The coordinates, the internal coefficient ring, its section rings, and its
canonical adjunction comparison are the existing library constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj Simplicial

namespace AlgebraicGeometry.ProEtale
namespace GaloisContinuousSection

/-- Sections of the actual pulled-back coefficient ring on a profinite test object.
Source: HRS Example 3.1, p. 6, the second displayed section ring in the node.
(blueprint: lem-sfb-galois-continuous-section-naturality). -/
abbrev profiniteSections (Ω A : Type u) [Field Ω] [NormedField A] (S : Profinite.{u}) :
    CommRingCat.{u + 1} :=
  (InternalAbelianSheafModule.sectionRingSheaf (Scheme.ProEt.topology (Spec (.of Ω)))
    (condensedRingObj (Profinite.continuousCoefficientRingObj A) (Spec (.of Ω)))).obj.obj
      (op ((profiniteToProEtOf (Spec (.of Ω))).obj S))

/-- Global sections over the separably closed point, evaluated at the final site object.
Source: HRS Example 3.1, p. 6, the assertion Γ(Spec Ω,R_A)=A.
(blueprint: lem-sfb-galois-continuous-section-naturality). -/
abbrev pointSections (Ω A : Type u) [Field Ω] [NormedField A] : CommRingCat.{u + 1} :=
  (InternalAbelianSheafModule.sectionRingSheaf (Scheme.ProEt.topology (Spec (.of Ω)))
    (condensedRingObj (Profinite.continuousCoefficientRingObj A) (Spec (.of Ω)))).obj.obj
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))))

private lemma lc_specMap_map {R B : Type u} [CommRing R] [CommRing B]
    (S : Profinite.{u}) (ψ : LocallyConstant S R →+* B) :
    LocallyConstant.specMap
      (ψ.comp (LocallyConstant.mapRingHom (Int.castRingHom R))) =
      LocallyConstant.specMap ψ := by
  ext p
  obtain ⟨⟨s, q⟩, h⟩ :=
    (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := R)).surjective
      (PrimeSpectrum.comap ψ p)
  change (LocallyConstant.homeomorphPrimeSpectrum.symm
      (PrimeSpectrum.comap (LocallyConstant.mapRingHom (Int.castRingHom R))
        (PrimeSpectrum.comap ψ p))).1 =
    (LocallyConstant.homeomorphPrimeSpectrum.symm (PrimeSpectrum.comap ψ p)).1
  rw [← h]
  change (LocallyConstant.homeomorphPrimeSpectrum.symm
      (LocallyConstant.homeomorphPrimeSpectrum
        (s, PrimeSpectrum.comap (Int.castRingHom R) q))).1 =
    (LocallyConstant.homeomorphPrimeSpectrum.symm
      (LocallyConstant.homeomorphPrimeSpectrum (s, q))).1
  simp only [Homeomorph.symm_apply_apply]

private lemma lc_pushout (R : Type u) [CommRing R] (S : Profinite.{u}) :
    IsPushout
      (CommRingCat.ofHom ((Int.castRingHom (LocallyConstant S ℤ)).comp
        ULift.ringEquiv.toRingHom))
      (CommRingCat.ofHom ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom))
      (CommRingCat.ofHom (LocallyConstant.mapRingHom (Int.castRingHom R)))
      (CommRingCat.ofHom (algebraMap R (LocallyConstant S R))) := by
  let i : CommRingCat.of (ULift.{u} ℤ) ⟶ CommRingCat.of (LocallyConstant S ℤ) :=
    CommRingCat.ofHom ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom)
  let j : CommRingCat.of (ULift.{u} ℤ) ⟶ CommRingCat.of R :=
    CommRingCat.ofHom ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom)
  have hc : i ≫ CommRingCat.ofHom (LocallyConstant.mapRingHom (Int.castRingHom R)) =
      j ≫ CommRingCat.ofHom (algebraMap R (LocallyConstant S R)) := by ext; rfl
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hc) ?_
  refine PushoutCocone.IsColimit.mk _
    (fun s ↦ CommRingCat.ofHom
      (LocallyConstant.liftPrimeSpectrum s.inr.hom (LocallyConstant.specMap s.inl.hom)))
    (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_)
  · apply CommRingCat.hom_ext
    apply LocallyConstant.ringHom_ext_of_specMap (RingHom.ext_int _ _)
    change LocallyConstant.specMap
      ((LocallyConstant.liftPrimeSpectrum s.inr.hom (LocallyConstant.specMap s.inl.hom)).comp
        (LocallyConstant.mapRingHom (Int.castRingHom R))) = _
    rw [lc_specMap_map, LocallyConstant.specMap_liftPrimeSpectrum]
  · ext r
    exact LocallyConstant.liftPrimeSpectrum_algebraMap _ _ r
  · apply CommRingCat.hom_ext
    apply LocallyConstant.ringHom_ext_of_specMap
    · ext r
      change m.hom (algebraMap R (LocallyConstant S R) r) =
        LocallyConstant.liftPrimeSpectrum s.inr.hom
          (LocallyConstant.specMap s.inl.hom) (algebraMap R (LocallyConstant S R) r)
      rw [LocallyConstant.liftPrimeSpectrum_algebraMap]
      exact congrArg (fun f ↦ f.hom r) h₂
    · ext p
      have h := congrArg (fun f ↦ LocallyConstant.specMap f.hom p) h₁
      change LocallyConstant.specMap
        (m.hom.comp (LocallyConstant.mapRingHom (Int.castRingHom R))) p = _ at h
      rw [lc_specMap_map] at h
      change LocallyConstant.specMap m.hom p =
        LocallyConstant.specMap
          (LocallyConstant.liftPrimeSpectrum s.inr.hom (LocallyConstant.specMap s.inl.hom)) p
      rw [LocallyConstant.specMap_liftPrimeSpectrum]
      exact h

private lemma lc_square (R : Type u) [CommRing R] (S : Profinite.{u}) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (LocallyConstant.mapRingHom (Int.castRingHom R))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (LocallyConstant S R))))
      (toSpecZ (profiniteToScheme.obj S)) (toSpecZ (Spec (.of R))) := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _ (lc_pushout R S)
  convert h using 1 <;> first | rfl | exact specULiftZIsTerminal.hom_ext _ _

private def testHomeo (Ω : Type u) [Field Ω] (S : Profinite.{u}) :
    ((profiniteToProEtOf (Spec (.of Ω))).obj S).left ≃ₜ S :=
  (Scheme.homeoOfIso (lc_square Ω S).isoPullback.symm).trans
    (LocallyConstant.homeomorphPrimeSpectrum.symm.trans
      (Homeomorph.prodUnique S (PrimeSpectrum Ω)))

private lemma testHomeo_apply (Ω : Type u) [Field Ω] (S : Profinite.{u})
    (x : ((profiniteToProEtOf (Spec (.of Ω))).obj S).left) :
    testHomeo Ω S x = profiniteTestProjection (Spec (.of Ω)) S x := by
  obtain ⟨p, rfl⟩ := (Scheme.homeoOfIso (lc_square Ω S).isoPullback).surjective x
  have hp := congrArg (fun f ↦ f p) (lc_square Ω S).isoPullback_hom_fst
  change (LocallyConstant.homeomorphPrimeSpectrum.symm
    ((Scheme.homeoOfIso (lc_square Ω S).isoPullback).symm
      ((Scheme.homeoOfIso (lc_square Ω S).isoPullback) p))).1 = _
  rw [Homeomorph.symm_apply_apply]
  change (LocallyConstant.homeomorphPrimeSpectrum.symm p).1 =
    (LocallyConstant.homeomorphPrimeSpectrum.symm
      ((pullback.fst (toSpecZ (profiniteToScheme.obj S))
        (toSpecZ (Spec (.of Ω)))) ((lc_square Ω S).isoPullback.hom p))).1
  change (pullback.fst (toSpecZ (profiniteToScheme.obj S))
    (toSpecZ (Spec (.of Ω)))) ((lc_square Ω S).isoPullback.hom p) = _ at hp
  erw [hp]
  obtain ⟨⟨s, q⟩, rfl⟩ :=
    (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := Ω)).surjective p
  change (LocallyConstant.homeomorphPrimeSpectrum.symm
      (LocallyConstant.homeomorphPrimeSpectrum (s, q))).1 =
    (LocallyConstant.homeomorphPrimeSpectrum.symm
      (LocallyConstant.homeomorphPrimeSpectrum
        (s, PrimeSpectrum.comap (Int.castRingHom Ω) q))).1
  simp only [Homeomorph.symm_apply_apply]

private def precompEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (A : Type u) [NormedField A] : C(X, A) ≃+* C(Y, A) where
  toFun f := f.comp ⟨h.symm, h.symm.continuous⟩
  invFun f := f.comp ⟨h, h.continuous⟩
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private def sectionEquiv (X : Scheme.{u}) (A : Type u) [NormedField A]
    (hA : IsNonarchimedean (norm : A → ℝ)) (U : X.ProEt) :
    (InternalAbelianSheafModule.sectionRingSheaf (Scheme.ProEt.topology X)
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) X)).obj.obj (op U) ≃+*
        C(U.left, A) := by
  let : IsUltrametricDist A :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm hA
  have : IsIso (ContinuousRingUniverse.comparison X A) :=
    ContinuousRingUniverse.comparison_isIso X A
  let R := continuousCoefficientRingSheaf X A
  have : IsCommMonObj ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R) :=
    Sheaf.isCommMonObj_sheafCompose_obj (Scheme.ProEt.topology X) R
      (fun U (a b : ULift.{u + 1} C(U.unop.left, A)) ↦ mul_comm a b)
  let H := (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapCommMon ⋙
    (Monoidal.commMonFunctorCategoryEquivalence X.ProEtᵒᵖ Ab.{u + 1}).functor
  let z : CommMon.mk (condensedRingObj (Profinite.continuousCoefficientRingObj A) X) ⟶
      CommMon.mk ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R) :=
    CommMon.homMk (Mon.ofHom (ContinuousRingUniverse.comparison X A))
  let f := ((H.map z).app (op U)).hom.hom
  let r : (InternalAbelianSheafModule.sectionRingSheaf (Scheme.ProEt.topology X)
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) X)).obj.obj (op U) →+*
      (InternalAbelianSheafModule.sectionRingSheaf (Scheme.ProEt.topology X)
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)).obj.obj (op U) :=
    InternalAbelianSheafModule.ringHom f
  let g := ((CondensedRing.reconstructedRingIso X R).hom.hom.app (op U)).hom
  have hb : Function.Bijective (g.comp r) := by
    change Function.Bijective ((ContinuousRingUniverse.comparison X A).hom.app (op U))
    exact ConcreteCategory.bijective_of_isIso
      ((ContinuousRingUniverse.comparison X A).hom.app (op U))
  exact (RingEquiv.ofBijective (g.comp r) hb).trans ULift.ringEquiv

private lemma sectionEquiv_apply (X : Scheme.{u}) (A : Type u) [NormedField A]
    (hA : IsNonarchimedean (norm : A → ℝ)) (U : X.ProEt)
    (f : (InternalAbelianSheafModule.sectionRingSheaf (Scheme.ProEt.topology X)
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) X)).obj.obj (op U)) :
    sectionEquiv X A hA U f =
      ((ContinuousRingUniverse.comparison X A).hom.app (op U) f).down := rfl

private def functionMap (X : Scheme.{u}) {A B : Type u}
    [NormedField A] [NormedField B] (φ : A →+* B) (hφ : Continuous φ) :
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf X A)) ⟶
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf X B)) :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
      { toFun := fun f ↦ ULift.up ((⟨φ, hφ⟩ : C(A, B)).comp f.down)
        map_zero' := by apply ULift.ext; ext x; exact φ.map_zero
        map_add' := by intro f g; apply ULift.ext; ext x; exact φ.map_add _ _ }
     naturality := by intros; rfl }⟩

private lemma comparison_coefficient (X : Scheme.{u}) {A B : Type u}
    [NormedField A] [NormedField B] (φ : A →+* B) (hφ : Continuous φ) :
    FieldSeparableCech.coefficientMap X φ hφ ≫ ContinuousRingUniverse.comparison X B =
      ContinuousRingUniverse.comparison X A ≫ functionMap X φ hφ := by
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _
    ((pointUpperStar ⋙ upperStar Ab.{u + 1} (toSpecZ X)).map
      (Profinite.continuousMapRingObjMapOfUniverse φ hφ) ≫
        ContinuousRingUniverse.comparison X B) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [ContinuousRingUniverse.comparison, adj]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

private lemma comparison_coefficient_apply (X : Scheme.{u}) {A B : Type u}
    [NormedField A] [NormedField B] (φ : A →+* B) (hφ : Continuous φ)
    (U : X.ProEt) (f : (condensedRingObj
      (Profinite.continuousCoefficientRingObj A) X).obj.obj (op U)) (x : U.left) :
    ((ContinuousRingUniverse.comparison X B).hom.app (op U)
      ((FieldSeparableCech.coefficientMap X φ hφ).hom.app (op U) f)).down x =
        φ (((ContinuousRingUniverse.comparison X A).hom.app (op U) f).down x) := by
  exact congrArg (fun z : ULift.{u + 1} C(U.left, B) ↦ z.down x)
    (ConcreteCategory.congr_hom (congr_app
      (congrArg (fun z ↦ z.hom) (comparison_coefficient X φ hφ)) (op U)) f)

private def profiniteEquiv (Ω A : Type u) [Field Ω] [NormedField A]
    (hA : IsNonarchimedean (norm : A → ℝ)) (S : Profinite.{u}) :
    profiniteSections Ω A S ≃+* C(S, A) :=
  (sectionEquiv (Spec (.of Ω)) A hA _).trans (precompEquiv (testHomeo Ω S) A)

private lemma profiniteEquiv_apply (Ω A : Type u) [Field Ω] [NormedField A]
    (hA : IsNonarchimedean (norm : A → ℝ)) (S : Profinite.{u})
    (f : profiniteSections Ω A S)
    (x : ((profiniteToProEtOf (Spec (.of Ω))).obj S).left) :
    profiniteEquiv Ω A hA S f (profiniteTestProjection (Spec (.of Ω)) S x) =
      ((ContinuousRingUniverse.comparison (Spec (.of Ω)) A).hom.app
        (op ((profiniteToProEtOf (Spec (.of Ω))).obj S)) f).down x := by
  rw [← testHomeo_apply]
  change (sectionEquiv (Spec (.of Ω)) A hA _ f) ((testHomeo Ω S).symm
    (testHomeo Ω S x)) = _
  rw [Homeomorph.symm_apply_apply, sectionEquiv_apply]

private def pointEquiv (Ω A : Type u) [Field Ω] [NormedField A]
    (hA : IsNonarchimedean (norm : A → ℝ)) : pointSections Ω A ≃+* A :=
  (sectionEquiv (Spec (.of Ω)) A hA _).trans
    (RingEquiv.ofBijective
      (ContinuousMap.evalAlgHom ℤ A (IsLocalRing.closedPoint Ω)).toRingHom
      ⟨fun f g h ↦ by
        ext x
        have hx : (x : PrimeSpectrum Ω) = IsLocalRing.closedPoint Ω :=
          Subsingleton.elim (α := PrimeSpectrum Ω) _ _
        change f (IsLocalRing.closedPoint Ω) = g (IsLocalRing.closedPoint Ω) at h
        rw [hx]
        exact h,
       fun a ↦ ⟨ContinuousMap.const _ a, rfl⟩⟩)

private lemma testPoint_projection (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω] (q : ℕ) (g : FieldSeparableCech.power k Ω q) :
    profiniteTestProjection (Spec (.of Ω)) (FieldSeparableCech.power k Ω q)
      (FieldSeparableCech.testPoint k Ω q g (IsLocalRing.closedPoint Ω)) = g := by
  let S := FieldSeparableCech.power k Ω q
  have hp := congrArg (fun f ↦ f (IsLocalRing.closedPoint Ω))
    (pullback.lift_fst (f := toSpecZ (profiniteToScheme.obj S))
      (g := toSpecZ (Spec (.of Ω)))
      (Spec.map (CommRingCat.ofHom ((Int.castRingHom Ω).comp
        (LocallyConstant.evalRingHom g)))) (𝟙 (Spec (.of Ω)))
      (specULiftZIsTerminal.hom_ext _ _))
  change (pullback.fst (toSpecZ (profiniteToScheme.obj S))
    (toSpecZ (Spec (.of Ω)))) (FieldSeparableCech.testPoint k Ω q g
      (IsLocalRing.closedPoint Ω)) = _ at hp
  change (LocallyConstant.homeomorphPrimeSpectrum.symm
    ((pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ (Spec (.of Ω))))
      (FieldSeparableCech.testPoint k Ω q g (IsLocalRing.closedPoint Ω)))).1 = g
  erw [hp]
  change (LocallyConstant.homeomorphPrimeSpectrum.symm
    (LocallyConstant.homeomorphPrimeSpectrum
      (g, PrimeSpectrum.comap (Int.castRingHom Ω) (IsLocalRing.closedPoint Ω)))).1 = g
  rw [Homeomorph.symm_apply_apply]

private def cechEquiv (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω]
    (e : ∀ q : ℕ, (FieldSeparableCech.object k Ω q).left ≅
      ((profiniteToProEtOf (Spec (.of Ω))).obj (FieldSeparableCech.power k Ω q)).left)
    (A : Type u) [NormedField A] (hA : IsNonarchimedean (norm : A → ℝ)) (q : ℕ) :
    FieldSeparableCech.sections k Ω A q ≃+* C(FieldSeparableCech.power k Ω q, A) :=
  (sectionEquiv (Spec (.of k)) A hA _).trans
    (precompEquiv ((Scheme.homeoOfIso (e q)).trans
      (testHomeo Ω (FieldSeparableCech.power k Ω q))) A)

private lemma cechEquiv_apply (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω]
    (e : ∀ q : ℕ, (FieldSeparableCech.object k Ω q).left ≅
      ((profiniteToProEtOf (Spec (.of Ω))).obj (FieldSeparableCech.power k Ω q)).left)
    (A : Type u) [NormedField A] (hA : IsNonarchimedean (norm : A → ℝ)) (q : ℕ)
    (f : FieldSeparableCech.sections k Ω A q) (g : FieldSeparableCech.power k Ω q) :
    cechEquiv k Ω e A hA q f g =
      ((ContinuousRingUniverse.comparison (Spec (.of k)) A).hom.app
        (op (FieldSeparableCech.object k Ω q)) f).down
          ((FieldSeparableCech.testPoint k Ω q g ≫ (e q).inv)
            (IsLocalRing.closedPoint Ω)) := by
  let h := (Scheme.homeoOfIso (e q)).trans
    (testHomeo Ω (FieldSeparableCech.power k Ω q))
  change (sectionEquiv (Spec (.of k)) A hA _ f) (h.symm g) = _
  rw [sectionEquiv_apply]
  congr 1
  apply h.injective
  rw [Homeomorph.apply_symm_apply]
  change g = testHomeo Ω _ ((e q).hom
    ((e q).inv (FieldSeparableCech.testPoint k Ω q g (IsLocalRing.closedPoint Ω))))
  erw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  change g = testHomeo Ω _ (FieldSeparableCech.testPoint k Ω q g
    (IsLocalRing.closedPoint Ω))
  rw [testHomeo_apply, testPoint_projection]

private lemma telescope {G : Type u} [Group G] {n : ℕ} (h : Fin (n + 1) → G)
    (j : Fin (n + 1)) :
    h 0 * ((List.ofFn (fun i : Fin n ↦ (h i.castSucc)⁻¹ * h i.succ)).take j.val).prod =
      h j := by
  obtain ⟨j, hj⟩ := j
  induction j with
  | zero => simp
  | succ j ih =>
    have hjn : j < n := by omega
    rw [List.prod_take_succ _ j (by simpa using hjn), List.getElem_ofFn]
    rw [← mul_assoc, ih (by omega)]
    simp

private lemma face_coordinates (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω]
    (e : ∀ q : ℕ, (FieldSeparableCech.object k Ω q).left ≅
      ((profiniteToProEtOf (Spec (.of Ω))).obj (FieldSeparableCech.power k Ω q)).left)
    (he : FieldSeparableCech.AreCoordinates k Ω e) (n m : ℕ)
    (α : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (g : FieldSeparableCech.power k Ω m) :
    FieldSeparableCech.testPoint k Ω m g ≫ (e m).inv ≫
        ((FieldSeparableCech.closureArrow k Ω).cechNerve.map α.op).left =
      Spec.map (CommRingCat.ofHom
        (FieldSeparableCech.cumulative k Ω g (α.toOrderHom 0).val).toRingHom) ≫
        FieldSeparableCech.testPoint k Ω n (FieldSeparableCech.reindex k Ω α g) ≫
          (e n).inv := by
  let F := Scheme.ProEt.forget (Spec (.of k)) ⋙ Over.forget (Spec (.of k))
  let D := WidePullbackShape.wideCospan (FieldSeparableCech.closureArrow k Ω).right
    (fun _ : Fin (n + 1) ↦ (FieldSeparableCech.closureArrow k Ω).left)
    (fun _ ↦ (FieldSeparableCech.closureArrow k Ω).hom)
  have hproj (j : Fin (n + 1)) :
      (FieldSeparableCech.testPoint k Ω m g ≫ (e m).inv ≫
        ((FieldSeparableCech.closureArrow k Ω).cechNerve.map α.op).left) ≫
          (WidePullback.π
            (fun _ : Fin (n + 1) ↦ (FieldSeparableCech.closureArrow k Ω).hom) j).left =
      (Spec.map (CommRingCat.ofHom
        (FieldSeparableCech.cumulative k Ω g (α.toOrderHom 0).val).toRingHom) ≫
        FieldSeparableCech.testPoint k Ω n (FieldSeparableCech.reindex k Ω α g) ≫
          (e n).inv) ≫ (WidePullback.π
            (fun _ : Fin (n + 1) ↦ (FieldSeparableCech.closureArrow k Ω).hom) j).left := by
    have hp := WidePullback.lift_π
      (fun _ : Fin (n + 1) ↦ (FieldSeparableCech.closureArrow k Ω).hom)
      (WidePullback.base (fun _ : Fin (m + 1) ↦
        (FieldSeparableCech.closureArrow k Ω).hom))
      (fun i : Fin (n + 1) ↦ WidePullback.π
        (fun _ : Fin (m + 1) ↦ (FieldSeparableCech.closureArrow k Ω).hom)
          (α.toOrderHom i)) (by simp) j
    change ((FieldSeparableCech.closureArrow k Ω).cechNerve.map α.op) ≫
      WidePullback.π (fun _ : Fin (n + 1) ↦
        (FieldSeparableCech.closureArrow k Ω).hom) j = _ at hp
    have hp' := congrArg F.map hp
    change ((FieldSeparableCech.closureArrow k Ω).cechNerve.map α.op).left ≫
      (WidePullback.π (fun _ : Fin (n + 1) ↦
        (FieldSeparableCech.closureArrow k Ω).hom) j).left =
      (WidePullback.π (fun _ : Fin (m + 1) ↦
        (FieldSeparableCech.closureArrow k Ω).hom) (α.toOrderHom j)).left at hp'
    simp only [Category.assoc]
    rw [hp', he.2 m g (α.toOrderHom j)]
    rw [he.2 n (FieldSeparableCech.reindex k Ω α g) j]
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    have ht := telescope
      (fun i : Fin (n + 1) ↦ FieldSeparableCech.cumulative k Ω g (α.toOrderHom i).val) j
    exact (congrArg (fun a : Ω ≃ₐ[k] Ω ↦ a x) ht).symm
  apply (isLimitOfPreserves F (limit.isLimit D)).hom_ext
  intro z
  cases z with
  | none =>
    change _ ≫ (WidePullback.base
      (fun _ : Fin (n + 1) ↦ (FieldSeparableCech.closureArrow k Ω).hom)).left =
      _ ≫ (WidePullback.base
        (fun _ : Fin (n + 1) ↦ (FieldSeparableCech.closureArrow k Ω).hom)).left
    have hbase := WidePullback.π_arrow
      (fun _ : Fin (n + 1) ↦ (FieldSeparableCech.closureArrow k Ω).hom) 0
    rw [← hbase]
    change _ ≫ ((WidePullback.π
      (fun _ : Fin (n + 1) ↦ (FieldSeparableCech.closureArrow k Ω).hom) 0).left ≫
        (FieldSeparableCech.closureArrow k Ω).hom.left) =
      _ ≫ ((WidePullback.π
        (fun _ : Fin (n + 1) ↦ (FieldSeparableCech.closureArrow k Ω).hom) 0).left ≫
          (FieldSeparableCech.closureArrow k Ω).hom.left)
    simpa only [Category.assoc] using
      congrArg (fun f ↦ f ≫ (FieldSeparableCech.closureArrow k Ω).hom.left) (hproj 0)
  | some j => exact hproj j

/-- The adjoint-normalized section identifications, with all coefficient and simplex maps.
Source: HRS Example 3.1, p. 6; Bhatt--Scholze Lemma 4.2.12.
(blueprint: lem-sfb-galois-continuous-section-naturality).

Proof: (1) Ultrametric balls are clopen, so A and B are Hausdorff and totally
 disconnected, including for trivial norms. No completeness is used.
(2) Express Ω[S] as the limit of finite disjoint unions, using
 def-sfb-profinite-test-objects, lem-weil-pbc-finite-affine-coproduct-spectrum,
 and lem-weil-pbc-spec-small-colimit-limit. Its ring is LC(S,Ω), also for empty S.
(3) By lem-weil-pbc-locally-constant-prime-spectrum, its underlying space is S;
 evaluation primes agree with the integer-label projection profiniteTestProjection.
(4) Apply lem-sfb-continuous-ring-universe-realization to the very canonical
 comparison of def-sfb-continuous-ring-canonical-comparison. Evaluation on W_q
 and Ω[S] gives the ring equivalences below. At a point it gives A.
 The cover in lem-sfb-separable-cover-finite-coordinates and
 lem-weil-pbc-weakly-etale-composition-base-change place the nerve in the site.
(5) The two adjuncts of coefficient change are both f ↦ φ ∘ f ∘ π_S, by
 def-sfb-continuous-map-condensed-ring-map. The adjunction Hom bijection
 therefore gives postcomposition on both section rings and φ at the point.
(6) Restriction is precomposition. Deleting the first cumulative vertex drops
 the first increment; an interior deletion multiplies adjacent increments;
 the last drops the last increment. A repetition inserts 1. The first face
 changes only the geometric base, whose underlying point is unchanged, hence
 has trivial coefficient action. Associativity of function composition gives
 commutation with coefficient change, including both degree-one faces.
(7) Apply the monoidal comparison sk-def-sfb-pullback-from-point-comp to the
 ring object of sk-def-sfb-pulled-back-coefficients. Its component is the
 canonical condensedPullbackHom, an isomorphism preserving multiplication and unit. -/
theorem section_naturality (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω]
    (e : ∀ q : ℕ, (FieldSeparableCech.object k Ω q).left ≅
      ((profiniteToProEtOf (Spec (.of Ω))).obj (FieldSeparableCech.power k Ω q)).left)
    (he : FieldSeparableCech.AreCoordinates k Ω e) :
    ∃ c : ∀ (A : Type u) [NormedField A], IsNonarchimedean (norm : A → ℝ) →
        ∀ q : ℕ, FieldSeparableCech.sections k Ω A q ≃+*
          C(FieldSeparableCech.power k Ω q, A),
    ∃ t : ∀ (A : Type u) [NormedField A], IsNonarchimedean (norm : A → ℝ) →
        ∀ S : Profinite.{u}, profiniteSections Ω A S ≃+* C(S, A),
    ∃ a : ∀ (A : Type u) [NormedField A], IsNonarchimedean (norm : A → ℝ) →
        pointSections Ω A ≃+* A,
      (∀ (A : Type u) [NormedField A] (hA : IsNonarchimedean (norm : A → ℝ))
        (q : ℕ) (f : FieldSeparableCech.sections k Ω A q)
        (g : FieldSeparableCech.power k Ω q),
        c A hA q f g =
          ((ContinuousRingUniverse.comparison (Spec (.of k)) A).hom.app
            (op (FieldSeparableCech.object k Ω q)) f).down
              ((FieldSeparableCech.testPoint k Ω q g ≫ (e q).inv).base
                (IsLocalRing.closedPoint Ω))) ∧
      (∀ (A : Type u) [NormedField A] (hA : IsNonarchimedean (norm : A → ℝ))
        (S : Profinite.{u}) (f : profiniteSections Ω A S)
        (x : ((profiniteToProEtOf (Spec (.of Ω))).obj S).left),
        t A hA S f (profiniteTestProjection (Spec (.of Ω)) S x) =
          ((ContinuousRingUniverse.comparison (Spec (.of Ω)) A).hom.app
            (op ((profiniteToProEtOf (Spec (.of Ω))).obj S)) f).down x) ∧
      (∀ (A : Type u) [NormedField A] (hA : IsNonarchimedean (norm : A → ℝ))
        (f : pointSections Ω A),
        a A hA f = ((ContinuousRingUniverse.comparison (Spec (.of Ω)) A).hom.app
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of Ω))))) f).down (IsLocalRing.closedPoint Ω)) ∧
      (∀ (A : Type u) [NormedField A] (hA : IsNonarchimedean (norm : A → ℝ))
        (n m : ℕ) (α : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
        (f : FieldSeparableCech.sections k Ω A n) (g : FieldSeparableCech.power k Ω m),
        c A hA m
          ((condensedRingObj (Profinite.continuousCoefficientRingObj A) (Spec (.of k))).obj.map
            ((FieldSeparableCech.closureArrow k Ω).cechNerve.map α.op).op f) g =
          c A hA n f (FieldSeparableCech.reindex k Ω α g)) ∧
      (∀ (A B : Type u) [NormedField A] [NormedField B]
        (hA : IsNonarchimedean (norm : A → ℝ)) (hB : IsNonarchimedean (norm : B → ℝ))
        (φ : A →+* B) (hφ : Continuous φ) (q : ℕ)
        (f : FieldSeparableCech.sections k Ω A q) (g : FieldSeparableCech.power k Ω q),
        c B hB q ((FieldSeparableCech.coefficientMap (Spec (.of k)) φ hφ).hom.app
          (op (FieldSeparableCech.object k Ω q)) f) g = φ (c A hA q f g)) ∧
      (∀ (A B : Type u) [NormedField A] [NormedField B]
        (hA : IsNonarchimedean (norm : A → ℝ)) (hB : IsNonarchimedean (norm : B → ℝ))
        (φ : A →+* B) (hφ : Continuous φ) (S : Profinite.{u})
        (f : profiniteSections Ω A S) (s : S),
        t B hB S ((FieldSeparableCech.coefficientMap (Spec (.of Ω)) φ hφ).hom.app
          (op ((profiniteToProEtOf (Spec (.of Ω))).obj S)) f) s = φ (t A hA S f s)) ∧
      (∀ (A B : Type u) [NormedField A] [NormedField B]
        (hA : IsNonarchimedean (norm : A → ℝ)) (hB : IsNonarchimedean (norm : B → ℝ))
        (φ : A →+* B) (hφ : Continuous φ) (f : pointSections Ω A),
        a B hB ((FieldSeparableCech.coefficientMap (Spec (.of Ω)) φ hφ).hom.app
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of Ω))))) f) = φ (a A hA f)) ∧
      (∀ (A : Type u) [NormedField A] (_hA : IsNonarchimedean (norm : A → ℝ)),
        IsIso (condensedPullbackHom (Profinite.continuousCoefficientRingObj A)
          (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) ∧
        IsMonHom (condensedPullbackHom (Profinite.continuousCoefficientRingObj A)
          (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))) := by
  refine ⟨fun A _ hA q ↦ cechEquiv k Ω e A hA q,
    fun A _ hA S ↦ profiniteEquiv Ω A hA S,
    fun A _ hA ↦ pointEquiv Ω A hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun A _ hA q f g ↦ cechEquiv_apply k Ω e A hA q f g
  · exact fun A _ hA S f x ↦ profiniteEquiv_apply Ω A hA S f x
  · intro A _ hA f
    exact congrArg (fun z : C(Spec (.of Ω), A) ↦ z (IsLocalRing.closedPoint Ω))
      (sectionEquiv_apply (Spec (.of Ω)) A hA _ f)
  · intro A _ hA n m α f g
    rw [cechEquiv_apply, cechEquiv_apply]
    have hn := NatTrans.naturality_apply
      (ContinuousRingUniverse.comparison (Spec (.of k)) A).hom
      ((FieldSeparableCech.closureArrow k Ω).cechNerve.map α.op).op f
    erw [hn]
    change (((ContinuousRingUniverse.comparison (Spec (.of k)) A).hom.app
      (op (FieldSeparableCech.object k Ω n)) f).down)
      (((FieldSeparableCech.testPoint k Ω m g ≫ (e m).inv) ≫
      ((FieldSeparableCech.closureArrow k Ω).cechNerve.map α.op).left)
        (IsLocalRing.closedPoint Ω)) = _
    rw [Category.assoc]
    erw [face_coordinates k Ω e he]
    change (((ContinuousRingUniverse.comparison (Spec (.of k)) A).hom.app
      (op (FieldSeparableCech.object k Ω n)) f).down)
      ((FieldSeparableCech.testPoint k Ω n (FieldSeparableCech.reindex k Ω α g) ≫
        (e n).inv) (Spec.map (CommRingCat.ofHom
      (FieldSeparableCech.cumulative k Ω g (α.toOrderHom 0).val).toRingHom)
        (IsLocalRing.closedPoint Ω))) = _
    exact congrArg
      (fun x : PrimeSpectrum Ω ↦
        (((ContinuousRingUniverse.comparison (Spec (.of k)) A).hom.app
          (op (FieldSeparableCech.object k Ω n)) f).down)
          ((FieldSeparableCech.testPoint k Ω n (FieldSeparableCech.reindex k Ω α g) ≫
            (e n).inv) x)) (Subsingleton.elim _ _)
  · intro A B _ _ hA hB φ hφ q f g
    rw [cechEquiv_apply, cechEquiv_apply]
    exact comparison_coefficient_apply _ φ hφ _ f _
  · intro A B _ _ hA hB φ hφ S f s
    obtain ⟨x, rfl⟩ := (testHomeo Ω S).surjective s
    rw [testHomeo_apply, profiniteEquiv_apply, profiniteEquiv_apply]
    exact comparison_coefficient_apply _ φ hφ _ f x
  · intro A B _ _ hA hB φ hφ f
    change (sectionEquiv (Spec (.of Ω)) B hB (Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))) _)
      (IsLocalRing.closedPoint Ω) =
      φ ((sectionEquiv (Spec (.of Ω)) A hA (Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))) f)
        (IsLocalRing.closedPoint Ω))
    rw [sectionEquiv_apply, sectionEquiv_apply]
    exact comparison_coefficient_apply _ φ hφ _ f (IsLocalRing.closedPoint Ω)
  · intros
    exact ⟨inferInstance, inferInstance⟩

end GaloisContinuousSection
end AlgebraicGeometry.ProEtale
