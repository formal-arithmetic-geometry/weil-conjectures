/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import WeilConjectures.AlgebraicGeometry.FinitePresentationStalkLocalizationModel
import WeilConjectures.AlgebraicGeometry.FinitePresentationSourceStalk
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk

/-! # Finite-presentation stalk and compatible fibre quotient data

Source: Stacks Project, Tag 080Q, local algebra setup; Tags 0HA1, 0098 and 01CP
(blueprint: lem-trf-finite-presentation-stalk-fibre-data).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Hom

open scoped TensorProduct ChangeOfRings

private theorem quotient_extendScalars {B C : Type u} [CommRing B] [CommRing C]
    (q : B →+* C) (I : Ideal B) (theta : (B ⧸ I) ≃+* C)
    (htheta : ∀ b, theta (Ideal.Quotient.mk I b) = q b) (M : ModuleCat.{u} B) :
    ∃ e : (M ⧸ (I • (⊤ : Submodule B M))) ≃+ (ModuleCat.extendScalars q).obj M,
      (∀ m : M, e (Submodule.Quotient.mk m) = (1 : C) ⊗ₜ[B, q] m) ∧
      ∀ (b : B) (m : M), e (Submodule.Quotient.mk (b • m)) =
        theta (Ideal.Quotient.mk I b) • e (Submodule.Quotient.mk m) := by
  let : Algebra B C := q.toAlgebra
  let t : (B ⧸ I) ≃ₐ[B] C := AlgEquiv.ofRingEquiv htheta
  let e := (TensorProduct.quotTensorEquivQuotSMul M I).symm.trans
    (TensorProduct.congr t.toLinearEquiv (LinearEquiv.refl B M))
  have he (m : M) : e (Submodule.Quotient.mk m) = (1 : C) ⊗ₜ[B, q] m := by
    simp [e]
  refine ⟨e.toAddEquiv, he, ?_⟩
  intro b m
  change e (Submodule.Quotient.mk (b • m)) =
    theta (Ideal.Quotient.mk I b) • e (Submodule.Quotient.mk m)
  rw [he, he, htheta, ModuleCat.ExtendScalars.smul_tmul, mul_one]
  change (1 : C) ⊗ₜ[B] (b • m) = q b ⊗ₜ[B] m
  rw [TensorProduct.tmul_smul]
  change (q b * 1) ⊗ₜ[B] m = q b ⊗ₜ[B] m
  rw [mul_one]

private theorem stalk_localization_model {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (x : X) :
    ∃ (P : CommRingCat.{u}) (r : S.presheaf.stalk (f x) →+* P)
        (q : P →+* X.presheaf.stalk x),
      r.FinitePresentation ∧ q.comp r = (f.stalkMap x).hom ∧
        ∃ T : Submonoid P, @IsLocalization P _ T (X.presheaf.stalk x) _ q.toAlgebra := by
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : S.Opens) by simp)
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ V from hxV)
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  let g := f.resLE V U hUV
  let y : U := ⟨x, hxU⟩
  obtain ⟨P, a, b, ht, hfp, T, hT⟩ :=
    exists_finitePresentation_stalk_localization_model g y
  let := a
  let := b
  let := ht
  let := hfp
  let := hT
  let e := f.resLEStalkMap (e := hUV) y
  let er : V.toScheme.presheaf.stalk (g y) ≃+* S.presheaf.stalk (f x) :=
    (asIso e.hom.left).commRingCatIsoToRingEquiv
  let es : U.toScheme.presheaf.stalk y ≃+* X.presheaf.stalk x :=
    (asIso e.hom.right).commRingCatIsoToRingEquiv
  let r := (algebraMap (V.toScheme.presheaf.stalk (g y)) P).comp er.symm.toRingHom
  let q := es.toRingHom.comp (algebraMap P (U.toScheme.presheaf.stalk y))
  refine ⟨P, r, q, ?_, ?_, T, ?_⟩
  · exact RingHom.finitePresentation_respectsIso.2 _ er.symm
      (show (algebraMap (V.toScheme.presheaf.stalk (g y)) P).FinitePresentation from
        (RingHom.finitePresentation_algebraMap).mpr hfp)
  · have hc := e.hom.w
    ext z
    have hz := congrArg (fun k ↦ k (er.symm z)) hc
    change es (algebraMap P (U.toScheme.presheaf.stalk y)
      (algebraMap (V.toScheme.presheaf.stalk (g y)) P (er.symm z))) = _
    have hcomp := @IsScalarTower.algebraMap_apply
      (V.toScheme.presheaf.stalk (g y)) P (U.toScheme.presheaf.stalk y)
      _ _ _ a b (g.stalkMap y).hom.toAlgebra ht (er.symm z)
    rw [← hcomp]
    change (f.stalkMap x).hom (er (er.symm z)) =
      es ((g.stalkMap y).hom (er.symm z)) at hz
    rw [er.apply_symm_apply] at hz
    exact hz.symm
  · exact (IsLocalization.isLocalization_iff_of_ringEquiv T es).mp hT

private theorem pullback_quotient {X Y : Scheme.{u}} (p : Y ⟶ X)
    (y : Y) (x : X) (h : p y = x) (F : X.Modules)
    (I : Ideal (X.presheaf.stalk x))
    (theta : (X.presheaf.stalk x ⧸ I) ≃+* Y.presheaf.stalk y)
    (htheta : ∀ b : X.presheaf.stalk x, theta (Ideal.Quotient.mk I b) =
      ((X.presheaf.stalkCongr (.of_eq h)).inv ≫ p.stalkMap y).hom b) :
    ∃ eta : ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F ⧸
        (I • (⊤ : Submodule (X.presheaf.stalk x)
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)))) ≃+
        (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
          ((Scheme.Modules.tensorPullback p).obj F),
      (∀ (b : X.presheaf.stalk x)
          (m : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F),
        eta (Submodule.Quotient.mk (b • m)) =
          theta (Ideal.Quotient.mk I b) • eta (Submodule.Quotient.mk m)) ∧
      (∀ (U : X.Opens) (hx : x ∈ U) (t : F.val.obj (op U)),
        eta (Submodule.Quotient.mk (TopCat.Presheaf.germ F.val.presheaf U x hx t)) =
          TopCat.Presheaf.germ ((Scheme.Modules.tensorPullback p).obj F).val.presheaf
            (p ⁻¹ᵁ U) y (Eq.mpr (congrArg (fun z : X ↦ z ∈ U) h) hx)
            (Scheme.Modules.tensorPullbackSection p F U t)) := by
  subst x
  have ht : ∀ b, theta (Ideal.Quotient.mk I b) = (p.stalkMap y).hom b := by
    simpa [TopCat.Presheaf.stalkCongr] using htheta
  obtain ⟨e, he, hsem⟩ := quotient_extendScalars (p.stalkMap y).hom I theta ht
    ((RingedSpace.moduleStalkFunctor X.toRingedSpace (p y)).obj F)
  obtain ⟨beta, hbeta⟩ := Scheme.Modules.exists_tensorPullback_stalk_iso p y
  let d := (beta.app F).toLinearEquiv
  let eta := e.trans d.symm.toAddEquiv
  refine ⟨eta, ?_, ?_⟩
  · intro b m
    change d.symm (e _) = theta (Ideal.Quotient.mk I b) • d.symm (e _)
    rw [hsem, map_smul]
  · intro U hx t
    apply d.injective
    change d (d.symm (e _)) = d _
    rw [d.apply_symm_apply, he]
    have hb := hbeta F U hx t
    have hs := Classical.choose_spec (Scheme.Modules.exists_tensorPullbackAdjunction p)
      F (op U) t
    change _ = Scheme.Modules.tensorPullbackSection p F U t at hs
    rw [hs] at hb
    exact hb.symm

/-- Local algebra and module presentations, with the actual fibre quotient maps.
Source: Stacks Project, Tag 080Q, local algebra setup; Tags 0HA1, 0098 and 01CP
(blueprint: lem-trf-finite-presentation-stalk-fibre-data).

Proof:
1. The stalk map is local because f is a morphism of locally ringed spaces.
   Choose affine neighbourhoods of x and f(x) witnessing local finite presentation.
   Restriction preserves stalks and their maps, since intersecting with these opens
   preserves germs and equality of germs. Apply
   lem-sbc-finite-presentation-stalk-localization-model to the restricted morphism.
   The scalar tower gives the displayed equality of ring maps. IsLocalization is
   precisely the universal property giving the required R-algebra isomorphism T^-1 P = B.
2. Apply lem-weil-pbc-finite-presentation-source-stalk to F and x; retain its two
   finite free maps, surjectivity and exactness. Both ranks may be zero.
3. By lem-sbc-scheme-fibre-stalk-quotient the actual projection stalk map has kernel
   I = m_R B and induces theta, with theta([b]) = p-sharp(b). Here p-sharp at x' is
   the fibre projection's stalk map, precomposed with the identification of the
   stalks at x and p(x') given by p(x') = x.
4. Apply lem-weil-pbc-module-stalk-pullback to the fibre projection. Its stalk
   comparison sends each pulled-back section germ to 1 tensor t_x. Identify this
   tensor product with M/IM by b tensor m mapping to [b m], using theta to lift b.
   Changing a lift by I changes its image by IM, so this is well defined and balanced.
   The inverse sends [m] to 1 tensor m; it kills IM since I maps to zero. The two
   composites are identities on classes and pure tensors. Composing with the inverse
   stalk comparison gives eta. Its additivity, theta-semilinearity and section-germ
   formula follow from these explicit maps. -/
theorem exists_finitePresentation_stalk_fibre_data
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [SheafOfModules.IsFinitePresentation.{u} F] (x : X) :
    IsLocalHom (f.stalkMap x).hom ∧
    (∃ (P : CommRingCat.{u}) (r : S.presheaf.stalk (f x) →+* P)
        (q : P →+* X.presheaf.stalk x),
      r.FinitePresentation ∧ q.comp r = (f.stalkMap x).hom ∧
        ∃ T : Submonoid P, @IsLocalization P _ T (X.presheaf.stalk x) _ q.toAlgebra) ∧
    (∃ (a b : ℕ)
        (v : (Fin a → X.presheaf.stalk x) →ₗ[X.presheaf.stalk x]
          (Fin b → X.presheaf.stalk x))
        (w : (Fin b → X.presheaf.stalk x) →ₗ[X.presheaf.stalk x]
          (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F),
      Function.Exact v w ∧ Function.Surjective w) ∧
    ∃ (theta : (X.presheaf.stalk x ⧸
          (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))).map (f.stalkMap x).hom) ≃+*
          (f.fiber (f x)).presheaf.stalk (f.asFiber x))
      (eta : ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F ⧸
          ((IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))).map (f.stalkMap x).hom •
            (⊤ : Submodule (X.presheaf.stalk x)
              ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)))) ≃+
          (RingedSpace.moduleStalkFunctor (f.fiber (f x)).toRingedSpace (f.asFiber x)).obj
            ((Scheme.Modules.tensorPullback (f.fiberι (f x))).obj F)),
      (∀ b : X.presheaf.stalk x,
        theta (Ideal.Quotient.mk _ b) =
          ((X.presheaf.stalkCongr (.of_eq (f.fiberι_asFiber x))).inv ≫
            (f.fiberι (f x)).stalkMap (f.asFiber x)).hom b) ∧
      (∀ (b : X.presheaf.stalk x)
          (m : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F),
        eta (Submodule.Quotient.mk (b • m)) =
          theta (Ideal.Quotient.mk _ b) • eta (Submodule.Quotient.mk m)) ∧
      (∀ (U : X.Opens) (hx : x ∈ U) (t : F.val.obj (op U)),
        eta (Submodule.Quotient.mk (TopCat.Presheaf.germ F.val.presheaf U x hx t)) =
          TopCat.Presheaf.germ
            ((Scheme.Modules.tensorPullback (f.fiberι (f x))).obj F).val.presheaf
            ((f.fiberι (f x)) ⁻¹ᵁ U) (f.asFiber x)
            (Eq.mpr (congrArg (fun z : X ↦ z ∈ U) (f.fiberι_asFiber x)) hx)
            (Scheme.Modules.tensorPullbackSection (f.fiberι (f x)) F U t)) := by
  refine ⟨inferInstance, stalk_localization_model f x, ?_, ?_⟩
  · obtain ⟨U, hxU, a, b, s, v, w, hw, hv, _⟩ :=
      RingedSpace.exists_finitePresentation_source_stalk X.toRingedSpace F x
    exact ⟨a, b, v, w, hv, hw⟩
  · obtain ⟨_, _, theta, htheta⟩ := f.fiberStalkMap_surjective_ker_quotientEquiv x
    obtain ⟨eta, hsem, hgerm⟩ := pullback_quotient (f.fiberι (f x)) (f.asFiber x)
      x (f.fiberι_asFiber x) F _ theta htheta
    exact ⟨theta, eta, htheta, hsem, hgerm⟩

end AlgebraicGeometry.Scheme.Hom
