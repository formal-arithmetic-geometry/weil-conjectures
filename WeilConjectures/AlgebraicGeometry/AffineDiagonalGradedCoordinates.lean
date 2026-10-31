/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineTraceTower
public import WeilConjectures.AlgebraicGeometry.ReesConeNormalization
import WeilConjectures.RingTheory.RegularSequenceGradedPolynomial
import WeilConjectures.AlgebraicGeometry.AffineDiagonalRegularDifferences

/-! # Polynomial coordinates on the intrinsic diagonal cone

Source: current blueprint, projection-purity-agreement proof, Agreement on the model,
normal-coordinate calculation (blueprint: lem-pur-affine-diagonal-graded-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.PurityNormalBundle

private theorem affine_homOfVector_isIso {C Z : Scheme.{u}} [IsAffine C] [IsAffine Z]
    (n : Type u) (p : C ⟶ Z) (v : n → Γ(C, ⊤))
    (hv : Function.Bijective (MvPolynomial.eval₂Hom p.appTop.hom v)) :
    IsIso (AffineSpace.homOfVector p v) := by
  let h := AffineSpace.homOfVector p v
  have he : (AffineSpace.isoOfIsAffine n Z).hom.appTop ≫ h.appTop =
      (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom
        (MvPolynomial.eval₂Hom p.appTop.hom v) := by
    rw [AffineSpace.isoOfIsAffine_hom_appTop, Category.assoc]
    congr 1
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
        MvPolynomial.eval₂Hom_C]
      change h.appTop ((AffineSpace n Z ↘ Z).appTop r) = p.appTop r
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
      exact congrArg (fun f ↦ f.appTop r) (AffineSpace.homOfVector_over p v)
    · intro j
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
        MvPolynomial.eval₂Hom_X'] using AffineSpace.homOfVector_appTop_coord p v j
  have : IsIso (CommRingCat.ofHom (MvPolynomial.eval₂Hom p.appTop.hom v)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hv
  have : IsIso ((AffineSpace.isoOfIsAffine n Z).hom.appTop ≫ h.appTop) := by
    rw [he]
    infer_instance
  have : IsIso h.appTop := IsIso.of_isIso_comp_left
    (AffineSpace.isoOfIsAffine n Z).hom.appTop h.appTop
  have hh : h = C.isoSpec.hom ≫ Spec.map h.appTop ≫
      (AffineSpace n Z).isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [show AffineSpace.homOfVector p v = h from rfl, hh]
  infer_instance

private theorem affineChart_eval_bijective {X Z : Scheme.{u}} (s : Z ⟶ X)
    [IsClosedImmersion s] (d : ℕ) (U : X.affineOpens)
    (b : Fin d → (ConormalGradedAlgebra.power s 1).val.obj (op U.1))
    (hr : RingTheory.Sequence.IsRegular Γ(X, U.1) (List.ofFn fun j ↦
      (@id Γ(X, U.1) ((ConormalGradedAlgebra.powerInclusion s 1).val.app
        (op U.1) (b j)))))
    (hs : Ideal.span (Set.range fun j ↦
      (@id Γ(X, U.1) ((ConormalGradedAlgebra.powerInclusion s 1).val.app
        (op U.1) (b j)))) =
        s.ker.ideal U) :
    Function.Bijective (MvPolynomial.eval₂Hom
      ((ConormalGradedAlgebra.presentation s).algebra.hom.hom.app (op (s ⁻¹ᵁ U.1))).hom
      (fun j : ULift.{u} (Fin d) ↦ ConormalGradedAlgebra.homogeneousClass s
        (ConormalGradedAlgebra.presentation s).algebra
        (ConormalGradedAlgebra.presentation s).inclusion 1 U.1 (b j.down))) := by
  let f : Fin d → Γ(X, U.1) := fun j ↦
    (ConormalGradedAlgebra.powerInclusion s 1).val.app (op U.1) (b j)
  let J := Ideal.span (Set.range f)
  have hJ : J = s.ker.ideal U := hs
  have hex := (ConormalGradedAlgebra.presentation s).affineChart U
  rw [← hJ] at hex
  obtain ⟨e, he⟩ := hex
  have hk : J = RingHom.ker (s.app U.1).hom := by rw [hJ, Scheme.Hom.ker_apply]
  let q : Γ(X, U.1) ⧸ J ≃+* Γ(Z, s ⁻¹ᵁ U.1) :=
    (Ideal.quotientEquiv _ _ (RingEquiv.refl _) (by simpa using hk.symm)).trans
      (RingHom.quotientKerEquivOfSurjective (s.app_surjective U.1 U.2))
  have hq (a : Γ(X, U.1)) : q (Ideal.Quotient.mk J a) = s.app U.1 a := by
    simp only [q, RingEquiv.trans_apply, Ideal.quotientEquiv_mk,
      RingEquiv.refl_apply, RingHom.quotientKerEquivOfSurjective_apply_mk]
  let θ := Ideal.regularSequenceGradedPolynomialMap f
  let k := MvPolynomial.eval₂Hom
    ((ConormalGradedAlgebra.presentation s).algebra.hom.hom.app (op (s ⁻¹ᵁ U.1))).hom
    (fun j : ULift.{u} (Fin d) ↦ ConormalGradedAlgebra.homogeneousClass s
      (ConormalGradedAlgebra.presentation s).algebra
      (ConormalGradedAlgebra.presentation s).inclusion 1 U.1 (b j.down))
  let t := (MvPolynomial.renameEquiv (Γ(X, U.1) ⧸ J)
    (Equiv.ulift : ULift.{u} (Fin d) ≃ Fin d)).toRingEquiv
  let m := MvPolynomial.mapEquiv (ULift.{u} (Fin d)) q.symm
  have hc : e.hom.hom.comp k = θ.toRingHom.comp (t.toRingHom.comp m.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      obtain ⟨a, rfl⟩ := s.app_surjective U.1 U.2 r
      have hqa : q.symm (s.app U.1 a) = Ideal.Quotient.mk J a := by
        rw [← hq, q.symm_apply_apply]
      change e.hom (k (MvPolynomial.C (s.app U.1 a))) =
        θ (t (m (MvPolynomial.C (s.app U.1 a))))
      rw [show k (MvPolynomial.C (s.app U.1 a)) = _ from
        MvPolynomial.eval₂Hom_C _ _ _]
      have hmC (a) : m (MvPolynomial.C a) = MvPolynomial.C (q.symm a) :=
        MvPolynomial.map_C _ _
      have htC (a) : t (MvPolynomial.C a) = MvPolynomial.C a :=
        MvPolynomial.rename_C _ _
      rw [hmC, htC]
      change e.hom ((ConormalGradedAlgebra.presentation s).algebra.hom.hom.app
        (op (s ⁻¹ᵁ U.1)) (s.app U.1 a)) = θ (MvPolynomial.C (q.symm (s.app U.1 a)))
      rw [← (ConormalGradedAlgebra.presentation s).constants U.1 a, hqa]
      obtain ⟨ha, h⟩ := he 0 a
      rw [show θ (MvPolynomial.C (Ideal.Quotient.mk J a)) =
          algebraMap (Γ(X, U.1) ⧸ J) (Ideal.associatedGraded J)
            (Ideal.Quotient.mk J a) from MvPolynomial.aeval_C _ _]
      change e.hom (ConormalGradedAlgebra.homogeneousClass s
        (ConormalGradedAlgebra.presentation s).algebra
        (ConormalGradedAlgebra.presentation s).inclusion 0 U.1 a) =
          DirectSum.of (Ideal.associatedGradedPiece J) 0
            (Submodule.Quotient.mk (⟨a, by simp⟩ : (J ^ 0 : Ideal Γ(X, U.1))))
      exact h.trans (congrArg (DirectSum.of (Ideal.associatedGradedPiece J) 0)
        (congrArg Submodule.Quotient.mk (Subtype.ext (by rfl))))
    · intro j
      change e.hom (k (MvPolynomial.X j)) = θ (t (m (MvPolynomial.X j)))
      rw [show k (MvPolynomial.X j) = _ from MvPolynomial.eval₂Hom_X' _ _ _]
      have hmX : m (MvPolynomial.X j) = MvPolynomial.X j := MvPolynomial.map_X _ _
      have htX : t (MvPolynomial.X j) = MvPolynomial.X j.down :=
        MvPolynomial.rename_X _ _
      rw [hmX, htX]
      change e.hom (ConormalGradedAlgebra.homogeneousClass s
        (ConormalGradedAlgebra.presentation s).algebra
        (ConormalGradedAlgebra.presentation s).inclusion 1 U.1 (b j.down)) =
          θ (MvPolynomial.X j.down)
      obtain ⟨ha, h⟩ := he 1 (b j.down)
      rw [show θ (MvPolynomial.X j.down) = _ from
        MvPolynomial.aeval_X _ _]
      exact h
  have hθ : Function.Bijective θ := (Ideal.regularSequence_gradedPolynomial f hr).1
  have hc' : Function.Bijective (e.hom.hom.comp k) := by
    rw [hc]
    exact hθ.comp (t.bijective.comp m.bijective)
  exact ⟨fun a b h ↦ hc'.1 (congrArg e.hom h), fun y ↦ by
    obtain ⟨x, hx⟩ := hc'.2 (e.hom y)
    exact ⟨x, (ConcreteCategory.bijective_of_isIso e.hom).1 hx⟩⟩

private theorem homogeneousClass_restrict {X Z : Scheme.{u}} (s : Z ⟶ X)
    [IsClosedImmersion s] (n : ℕ) {U W : X.Opens} (h : U ≤ W)
    (b : (ConormalGradedAlgebra.power s n).val.obj (op W)) :
    (ConormalGradedAlgebra.presentation s).algebra.right.obj.map
      (homOfLE (s.preimage_mono h)).op
      (ConormalGradedAlgebra.homogeneousClass s
        (ConormalGradedAlgebra.presentation s).algebra
        (ConormalGradedAlgebra.presentation s).inclusion n W b) =
    ConormalGradedAlgebra.homogeneousClass s
      (ConormalGradedAlgebra.presentation s).algebra
      (ConormalGradedAlgebra.presentation s).inclusion n U
        ((ConormalGradedAlgebra.power s n).val.map (homOfLE h).op b) := by
  dsimp only [ConormalGradedAlgebra.homogeneousClass, ConormalGradedAlgebra.representative]
  have hi := PresheafOfModules.naturality_apply
    ((ConormalGradedAlgebra.presentation s).inclusion n).val
    (homOfLE (s.preimage_mono h)).op
      (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction s)).unit.app
        (ConormalGradedAlgebra.power s n)).val.app (op W) b)
  refine hi.symm.trans ?_
  congr 1
  exact (PresheafOfModules.naturality_apply
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction s)).unit.app
      (ConormalGradedAlgebra.power s n)).val (homOfLE h).op b).symm

private def coneFunction {X Z : Scheme.{u}} (s : Z ⟶ X) [IsClosedImmersion s]
    (b : (ConormalGradedAlgebra.power s 1).val.obj (op ⊤)) : Γ(normalCone s, ⊤) :=
  let A := (ConormalGradedAlgebra.presentation s).algebra
  let c := ConormalGradedAlgebra.homogeneousClass s A
    (ConormalGradedAlgebra.presentation s).inclusion 1 ⊤ b
  let c' := A.right.obj.map (homOfLE (by simp)).op c
  (normalCone s).presheaf.map (homOfLE (by simp)).op
    ((Etale.FiniteSmoothPurity.coneAlgebraIso s).hom.right.hom.app (op ⊤) c')

private theorem coneFunction_restrict {X Z : Scheme.{u}} (s : Z ⟶ X)
    [IsClosedImmersion s] (U : X.Opens)
    (b : (ConormalGradedAlgebra.power s 1).val.obj (op ⊤)) :
    (normalCone s).presheaf.map
      (homOfLE (show projection s ⁻¹ᵁ (s ⁻¹ᵁ U) ≤ ⊤ from le_top)).op (coneFunction s b) =
    (Etale.FiniteSmoothPurity.coneAlgebraIso s).hom.right.hom.app (op (s ⁻¹ᵁ U))
      (ConormalGradedAlgebra.homogeneousClass s
        (ConormalGradedAlgebra.presentation s).algebra
        (ConormalGradedAlgebra.presentation s).inclusion 1 U
          ((ConormalGradedAlgebra.power s 1).val.map (homOfLE le_top).op b)) := by
  let A := (ConormalGradedAlgebra.presentation s).algebra
  let e := Etale.FiniteSmoothPurity.coneAlgebraIso s
  let V := s ⁻¹ᵁ U
  have hn := e.hom.right.hom.naturality
    (homOfLE (show V ≤ ⊤ from le_top)).op
  change A.right.obj.map (homOfLE (show V ≤ ⊤ from le_top)).op ≫
    e.hom.right.hom.app (op V) = e.hom.right.hom.app (op ⊤) ≫
      (normalCone s).presheaf.map
        (homOfLE ((projection s).preimage_mono (show V ≤ ⊤ from le_top))).op at hn
  have hm : (normalCone s).presheaf.map (homOfLE (by simp)).op ≫
      (normalCone s).presheaf.map
        (homOfLE (show projection s ⁻¹ᵁ V ≤ ⊤ from le_top)).op =
      (normalCone s).presheaf.map
        (homOfLE ((projection s).preimage_mono (show V ≤ ⊤ from le_top))).op := by
    rw [← Functor.map_comp]
    congr 1
  have hmaps : e.hom.right.hom.app (op ⊤) ≫
      (normalCone s).presheaf.map (homOfLE (by simp)).op ≫
      (normalCone s).presheaf.map
        (homOfLE (show projection s ⁻¹ᵁ V ≤ ⊤ from le_top)).op =
      A.right.obj.map (homOfLE (show V ≤ ⊤ from le_top)).op ≫
        e.hom.right.hom.app (op V) := by
    rw [hm]
    exact hn.symm
  let c := ConormalGradedAlgebra.homogeneousClass s A
    (ConormalGradedAlgebra.presentation s).inclusion 1 ⊤ b
  change (e.hom.right.hom.app (op ⊤) ≫
    (normalCone s).presheaf.map (homOfLE (by simp)).op ≫
    (normalCone s).presheaf.map
      (homOfLE (show projection s ⁻¹ᵁ V ≤ ⊤ from le_top)).op)
        (A.right.obj.map (homOfLE (by simp)).op c) = _
  rw [hmaps, CommRingCat.comp_apply]
  congr 1
  have hA : A.right.obj.map (homOfLE (by simp)).op ≫
      A.right.obj.map (homOfLE (show V ≤ ⊤ from le_top)).op =
      A.right.obj.map (homOfLE (s.preimage_mono (show U ≤ ⊤ from le_top))).op := by
    rw [← Functor.map_comp]
    congr 1
  have hAc := congrArg (fun f ↦ f c) hA
  change A.right.obj.map (homOfLE (show V ≤ ⊤ from le_top)).op
    (A.right.obj.map (homOfLE (by simp)).op c) = _ at hAc
  exact hAc.trans (homogeneousClass_restrict s 1 (show U ≤ ⊤ from le_top) b)

private theorem restricted_eval_bijective {X Z : Scheme.{u}} (s : Z ⟶ X)
    [IsClosedImmersion s] (n : Type u) (V : Z.Opens)
    (c : n → (ConormalGradedAlgebra.presentation s).algebra.right.obj.obj (op V))
    (v : n → Γ(normalCone s, ⊤))
    (hc : ∀ j, (normalCone s).presheaf.map
      (homOfLE (show projection s ⁻¹ᵁ V ≤ ⊤ from le_top)).op (v j) =
        (Etale.FiniteSmoothPurity.coneAlgebraIso s).hom.right.hom.app (op V) (c j))
    (hb : Function.Bijective (MvPolynomial.eval₂Hom
      ((ConormalGradedAlgebra.presentation s).algebra.hom.hom.app (op V)).hom c)) :
    Function.Bijective (MvPolynomial.eval₂Hom ((projection s) ∣_ V).appTop.hom
      (fun j ↦ (projection s ⁻¹ᵁ V).ι.appTop (v j))) := by
  let A := (ConormalGradedAlgebra.presentation s).algebra
  let e := Etale.FiniteSmoothPurity.coneAlgebraIso s
  let W := projection s ⁻¹ᵁ V
  let a := V.topIso.commRingCatIsoToRingEquiv
  let b := W.topIso.symm.commRingCatIsoToRingEquiv
  let eV := ((CategoryTheory.sheafToPresheaf _ _).mapIso
    ((Under.forget Z.sheaf).mapIso e)).app (op V)
  let r := eV.commRingCatIsoToRingEquiv
  let k := MvPolynomial.eval₂Hom (A.hom.hom.app (op V)).hom c
  let m := MvPolynomial.mapEquiv n a
  have he : MvPolynomial.eval₂Hom ((projection s) ∣_ V).appTop.hom
      (fun j ↦ W.ι.appTop (v j)) =
      b.toRingHom.comp (r.toRingHom.comp (k.comp m.toRingHom)) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      rw [MvPolynomial.eval₂Hom_C]
      change ((projection s) ∣_ V).appTop x = b (r (k (m (MvPolynomial.C x))))
      have hmC : m (MvPolynomial.C x) = MvPolynomial.C (a x) :=
        MvPolynomial.map_C _ _
      have hkC : k (m (MvPolynomial.C x)) = A.hom.hom.app (op V) (a x) :=
        (congrArg k hmC).trans (MvPolynomial.eval₂Hom_C _ _ _)
      refine (show ((projection s) ∣_ V).appTop x =
        b (r (A.hom.hom.app (op V) (a x))) from ?_).trans
          (congrArg (fun y ↦ b (r y)) hkC).symm
      have hw := congrArg (fun f ↦ f.hom.app (op V)) (Under.w e.hom)
      change A.hom.hom.app (op V) ≫ e.hom.right.hom.app (op V) =
        (projection s).app V at hw
      have hp : ((projection s) ∣_ V).appTop =
          V.topIso.hom ≫ (projection s).app V ≫ W.topIso.inv := by
        have h := Scheme.Hom.resLE_app_top (projection s)
          (U := V) (V := projection s ⁻¹ᵁ V) le_rfl
        rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at h
        exact h
      have hwu := congrArg (fun f ↦ W.topIso.inv (f (V.topIso.hom x))) hw
      exact (congrArg (fun f ↦ f x) hp).trans hwu.symm
    · intro j
      rw [MvPolynomial.eval₂Hom_X']
      change W.ι.appTop (v j) = b (r (k (m (MvPolynomial.X j))))
      have hmX : m (MvPolynomial.X j) = MvPolynomial.X j := MvPolynomial.map_X _ _
      rw [hmX, MvPolynomial.eval₂Hom_X']
      change W.ι.appTop (v j) = W.topIso.inv
        (e.hom.right.hom.app (op V) (c j))
      have hi : W.ι.appTop = (normalCone s).presheaf.map
          (homOfLE (show W ≤ ⊤ from le_top)).op ≫ W.topIso.inv := by
        rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv, ← Functor.map_comp]
        congr 1
      rw [hi, CommRingCat.comp_apply, hc]
  rw [he]
  exact b.bijective.comp (r.bijective.comp (hb.comp m.bijective))

private theorem affineSpaceMap_range {Z : Scheme.{u}} (n : Type u) (V : Z.Opens) :
    (AffineSpace.map n V.ι).opensRange = (AffineSpace n Z ↘ Z) ⁻¹ᵁ V := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (AffineSpace.isPullback_map (n := n) V.ι).flip (⊤ : V.toScheme.Opens)
  simpa only [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange,
    Scheme.Opens.opensRange_ι, Scheme.Opens.ι_image_top] using h

private theorem homOfVector_isIso_of_local {C Z : Scheme.{u}}
    (p : C ⟶ Z) [IsAffineHom p] (n : Type u) (v : n → Γ(C, ⊤))
    (hloc : ∀ z : Z, ∃ V : Z.Opens, IsAffineOpen V ∧ z ∈ V ∧
      Function.Bijective (MvPolynomial.eval₂Hom (p ∣_ V).appTop.hom
        (fun j ↦ (p ⁻¹ᵁ V).ι.appTop (v j)))) :
    IsIso (AffineSpace.homOfVector p v) := by
  classical
  choose V hV hz hb using hloc
  let h := AffineSpace.homOfVector p v
  let 𝒰 : (AffineSpace n Z).OpenCover := Scheme.Cover.mkOfCovers Z
    (fun z ↦ AffineSpace n (V z).toScheme)
    (fun z ↦ AffineSpace.map n (V z).ι) (by
      intro y
      refine ⟨(AffineSpace n Z ↘ Z) y, ?_⟩
      change y ∈ (AffineSpace.map n (V ((AffineSpace n Z ↘ Z) y)).ι).opensRange
      rw [affineSpaceMap_range]
      exact hz _)
  apply IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme) 𝒰
  intro z
  let t := AffineSpace.homOfVector (p ∣_ V z)
    (fun j ↦ (p ⁻¹ᵁ V z).ι.appTop (v j))
  have : IsAffine (V z).toScheme := hV z
  have : IsAffine (p ⁻¹ᵁ V z).toScheme := (hV z).preimage p
  have : IsIso t := affine_homOfVector_isIso n (p ∣_ V z) _ (hb z)
  have he : (p ⁻¹ᵁ V z).ι ≫ h = t ≫ AffineSpace.map n (V z).ι := by
    dsimp only [h, t]
    rw [AffineSpace.comp_homOfVector, AffineSpace.homOfVector_comp_map,
      morphismRestrict_ι]
    rfl
  have hp : IsPullback t (p ⁻¹ᵁ V z).ι (AffineSpace.map n (V z).ι) h := by
    apply IsOpenImmersion.isPullback _ _ _ _ he
    rw [affineSpaceMap_range, ← Scheme.Hom.comp_preimage,
      AffineSpace.homOfVector_over, Scheme.Opens.opensRange_ι]
  change IsIso (pullback.snd h (AffineSpace.map n (V z).ι))
  rw [← hp.flip.isoPullback_inv_snd]
  infer_instance

/-- The intrinsic relative-Spec cone of an affine diagonal is affine space in the
ordered degree-one difference classes. This concerns only the associated-graded
algebra, before any comparison with an extended-Rees fibre or any integration map.

Source: current blueprint, lem-pur-projection-purity-agreement.proof.md,
Agreement on the model, normal-coordinate calculation; Stacks 0636.
(blueprint: lem-pur-affine-diagonal-graded-coordinates).

Proof: cover Y by affine opens Spec R. The self-product has ring R[x,y], with
its diagonal ideal generated by u_i=y_i-x_i. The substitution y_i=x_i+u_i
identifies this ring with R[x,u] and the ideal with (u). Each power (u)^m is
spanned freely over R[x] by monomials in u of degree at least m. Consequently
(u)^m/(u)^(m+1) has exactly its degree-m monomial basis. Multiplication of these
bases identifies the associated-graded algebra with R[x,v], sending v_i to the
class of u_i. The supplied representatives b_i have these very classes because
their inclusions are u_i. The relative-Spec evaluation used below is therefore
the spectrum of this polynomial-algebra isomorphism. Polynomial substitutions,
ideal powers and their homogeneous quotients commute with localization in R;
thus the affine inverses agree on overlaps and glue. For d=0 the ideal is zero,
its graded algebra is R in degree zero, and the coordinate map is the identity.
The empty affine cover and the zero ring impose no extra assumption. -/
theorem affineDiagonalGradedCoordinates_isIso (Y : Scheme.{u}) (d : ℕ)
    (b : (i : Fin d) → (ConormalGradedAlgebra.power
      (pullback.diagonal (affineTraceProjection Y d)) 1).val.obj (op ⊤))
    (_hb : ∀ i, (ConormalGradedAlgebra.powerInclusion
        (pullback.diagonal (affineTraceProjection Y d)) 1).val.app (op ⊤) (b i) =
      (pullback.snd (affineTraceProjection Y d) (affineTraceProjection Y d)).appTop
          (affineTraceCoordinate Y d i) -
        (pullback.fst (affineTraceProjection Y d) (affineTraceProjection Y d)).appTop
          (affineTraceCoordinate Y d i)) :
    let s := pullback.diagonal (affineTraceProjection Y d)
    let A := (ConormalGradedAlgebra.presentation s).algebra
    IsIso (AffineSpace.homOfVector (projection s)
      (fun i : ULift.{u} (Fin d) ↦
        let c := ConormalGradedAlgebra.homogeneousClass s A
          (ConormalGradedAlgebra.presentation s).inclusion 1 ⊤ (b i.down)
        let c' := A.right.obj.map (homOfLE (by simp)).op c
        (normalCone s).presheaf.map (homOfLE (by simp)).op
          ((Etale.FiniteSmoothPurity.coneAlgebraIso s).hom.right.hom.app (op ⊤) c'))) := by
  let s := pullback.diagonal (affineTraceProjection Y d)
  let A := (ConormalGradedAlgebra.presentation s).algebra
  change IsIso (AffineSpace.homOfVector (projection s)
    (fun j : ULift.{u} (Fin d) ↦ coneFunction s (b j.down)))
  have : IsAffineHom (projection s) := (over s).property
  apply homOfVector_isIso_of_local
  intro z
  obtain ⟨U, hz, hr, hs⟩ := affineDiagonal_regular_differences Y d z
  let bU : Fin d → (ConormalGradedAlgebra.power s 1).val.obj (op U.1) :=
    fun j ↦ (ConormalGradedAlgebra.power s 1).val.map (homOfLE le_top).op (b j)
  have hf : (fun j ↦ @id Γ(pullback (affineTraceProjection Y d)
        (affineTraceProjection Y d), U.1)
      ((ConormalGradedAlgebra.powerInclusion s 1).val.app (op U.1) (bU j))) =
      (fun j ↦ (pullback (affineTraceProjection Y d)
        (affineTraceProjection Y d)).presheaf.map (homOfLE le_top).op
        ((pullback.snd (affineTraceProjection Y d) (affineTraceProjection Y d)).appTop
            (affineTraceCoordinate Y d j) -
          (pullback.fst (affineTraceProjection Y d) (affineTraceProjection Y d)).appTop
            (affineTraceCoordinate Y d j))) := by
    funext j
    exact (PresheafOfModules.naturality_apply
      (ConormalGradedAlgebra.powerInclusion s 1).val (homOfLE le_top).op (b j)).trans
        (congrArg ((pullback (affineTraceProjection Y d)
          (affineTraceProjection Y d)).presheaf.map (homOfLE le_top).op) (_hb j))
  rw [← hf] at hr hs
  refine ⟨s ⁻¹ᵁ U.1, U.2.preimage s, hz, ?_⟩
  apply restricted_eval_bijective s (ULift.{u} (Fin d)) (s ⁻¹ᵁ U.1)
    (fun j ↦ ConormalGradedAlgebra.homogeneousClass s A
      (ConormalGradedAlgebra.presentation s).inclusion 1 U.1 (bU j.down))
  · intro j
    exact coneFunction_restrict s U.1 (b j.down)
  · exact affineChart_eval_bijective s d U bU hr hs

end AlgebraicGeometry.PurityNormalBundle
