/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
import Sheaf.Algebra.Homology.BaseDerivedTensorRestrictedRingComparison

/-! # Independence of the localized tensor comparison from the derived universe

Source: Stacks Project, Tag 06Y6, independence of derived tensor resolutions.
(blueprint: new-base-derived-tensor-localized-universe-independence). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w w'
open CategoryTheory
open scoped TensorProduct
namespace ModuleCat

private theorem identityHomology (E : Type u) [CommRing E] (S : ShortComplex (ModuleCat.{u} E)) :
    (S.mapHomologyIso (𝟭 _)).hom = 𝟙 _ := by
  let h := S.homologyData.left
  let h1 := h.map (𝟭 _)
  let γ : ShortComplex.LeftHomologyMapData (𝟙 S) h1 h :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := by simp [h1]
      commf' := by simp [h1]
      commπ := by simp [h1] }
  have hh := γ.homologyMap_eq
  simp only [ShortComplex.homologyMap_id] at hh
  change 𝟙 _ = h1.homologyIso.hom ≫ 𝟙 _ ≫ h.homologyIso.inv at hh
  have hh' : h1.homologyIso.hom = h.homologyIso.hom := by
    apply (cancel_mono h.homologyIso.inv).1
    simpa only [Category.comp_id, Category.id_comp, Iso.hom_inv_id] using hh.symm
  rw [h.mapHomologyIso_eq]
  change h1.homologyIso.hom ≫ h.homologyIso.inv = 𝟙 _
  rw [hh']
  exact h.homologyIso.hom_inv_id

private theorem identityRestrictionHomology (E : Type u) [CommRing E]
    (K : CochainComplex (ModuleCat.{u} E) ℤ) (i : ℤ) :
    let U := ModuleCat.restrictScalars (RingHom.id E)
    let t := (NatIso.mapHomologicalComplex (ModuleCat.restrictScalarsId E).symm
      (.up ℤ)).app K
    ∀ x : K.homology i, HomologicalComplex.homologyMap t.hom i x =
      ((K.sc i).mapHomologyIso U).inv x := by
  intro U t x
  have h := ((ModuleCat.restrictScalarsId E).inv).app_homology (K.sc i)
  have hid := ((K.sc i).mapHomologyIso (𝟭 _)).hom_inv_id
  rw [identityHomology, Category.id_comp] at hid
  rw [hid] at h
  change (ModuleCat.restrictScalarsId E).inv.app (K.homology i) =
    (𝟙 (K.homology i) ≫ HomologicalComplex.homologyMap t.hom i) ≫
      ((K.sc i).mapHomologyIso U).hom at h
  simp only [Category.id_comp] at h
  have ht : HomologicalComplex.homologyMap t.hom i =
      (ModuleCat.restrictScalarsId E).inv.app (K.homology i) ≫
        ((K.sc i).mapHomologyIso U).inv := by
    apply (cancel_mono ((K.sc i).mapHomologyIso U).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact h.symm
  exact ConcreteCategory.congr_hom ht x

/-- The localized comparison does not depend on the derived-category universe.
Source: Stacks Project, Tag 06Y6, Lemma 15.61.1, independence of choices.
(blueprint: new-base-derived-tensor-localized-universe-independence).

Proof: apply the restricted ring comparison with identity equivalences of R, A
and B and the identity restriction isomorphisms on the input and ordinary tensor
complex. Its second-ring-linear isomorphism commutes with the A-action by its
scalar-action clause. Tensor induction therefore promotes it to an
A tensor_R B-linear isomorphism. The ordinary comparison clause, with identity
restriction removed by its exact homology isomorphism, says that this
isomorphism intertwines comparison. The two ordinaryToLocalized maps agree on
pure tensors, hence agree by scalar-extension hom_ext. Extend the cohomology
isomorphism to D, transpose its desired square through the extension/restriction
adjunction, and substitute the two localized_eq fields. Adjunction naturality
reduces the square to the ordinary comparison identity. All underlying modules
remain in the same universe u; only the auxiliary derived-category morphism
universes vary. Identity maps, zero complexes and zero rings obey the same
adjunction and tensor equations. No localization or flatness is required. -/
theorem baseDerivedTensorCohomologyModel_localized_universe_independence
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [dR : HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [dB : HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : @BaseDerivedTensorCohomologyModel.{u, u, u, u, u, w}
      R A B _ _ _ _ _ dR dB Q D _ _)
    [dR' : HasDerivedCategory.{w'} (ModuleCat.{u} R)]
    [dB' : HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (n : @BaseDerivedTensorCohomologyModel.{u, u, u, u, u, w'}
      R A B _ _ _ _ _ dR' dB' Q D _ _) (i : ℤ) :
    ∃ s : (extendScalars (algebraMap (A ⊗[R] B) D)).obj
        (@BaseDerivedTensorCohomologyModel.cohomology R A B _ _ _ _ _
          dR dB Q D _ _ m i) ≅
        (extendScalars (algebraMap (A ⊗[R] B) D)).obj
          (@BaseDerivedTensorCohomologyModel.cohomology R A B _ _ _ _ _
            dR' dB' Q D _ _ n i),
      s.hom ≫ (@BaseDerivedTensorCohomologyModel.localizedComparison R A B _ _ _ _ _
        dR' dB' Q D _ _ n i) =
          @BaseDerivedTensorCohomologyModel.localizedComparison R A B _ _ _ _ _
            dR dB Q D _ _ m i := by
  classical
  let K := ((extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)).obj Q
  let q := (NatIso.mapHomologicalComplex (restrictScalarsId A).symm (.up ℤ)).app Q
  let t := (NatIso.mapHomologicalComplex (restrictScalarsId (A ⊗[R] B)).symm
    (.up ℤ)).app K
  obtain ⟨kB, hA, hcomp⟩ :=
    @exists_baseDerivedTensor_restricted_ring_comparison.{u, w, w'}
      R A B D R A B D _ _ _ _ _ _ _ _ _ _ _ _ _ _ dR dB dR' dB'
      Q Q m n (RingEquiv.refl R) (RingEquiv.refl A) (RingEquiv.refl B)
      rfl rfl q (RingEquiv.refl (A ⊗[R] B)) (fun _ _ ↦ rfl) t
      (fun _ _ _ ↦ rfl) i
  let mH := @BaseDerivedTensorCohomologyModel.cohomology R A B _ _ _ _ _
    dR dB Q D _ _ m i
  let nH := @BaseDerivedTensorCohomologyModel.cohomology R A B _ _ _ _ _
    dR' dB' Q D _ _ n i
  let mc := @BaseDerivedTensorCohomologyModel.comparison R A B _ _ _ _ _
    dR dB Q D _ _ m i
  let nc := @BaseDerivedTensorCohomologyModel.comparison R A B _ _ _ _ _
    dR' dB' Q D _ _ n i
  let v : mH ≃+ nH := kB.toLinearEquiv.toAddEquiv
  have hB (b : B) (x : mH) :
      v ((Algebra.TensorProduct.includeRight b : A ⊗[R] B) • x) =
        (Algebra.TensorProduct.includeRight b : A ⊗[R] B) • v x :=
    kB.hom.hom.map_smul b x
  have hlinear (r : A ⊗[R] B) (x : mH) : v (r • x) = r • v x := by
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have ht : (a ⊗ₜ[R] b : A ⊗[R] B) =
          (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) *
            Algebra.TensorProduct.includeRight b := by
        change a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [ht, mul_smul, mul_smul]
      exact (hA a _).trans (congrArg
        (fun y ↦ (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • y)
        (hB b x))
    | add r t hr ht => simp only [add_smul, map_add, hr, ht]
  let e : mH ≅ nH :=
    (LinearEquiv.ofBijective
      (show mH →ₗ[A ⊗[R] B] nH from
        { toFun := v, map_add' := v.map_add, map_smul' := hlinear })
      v.bijective).toModuleIso
  have hc : e.hom ≫ nc = mc := by
    ext x
    have hi : Function.Injective (HomologicalComplex.homologyMap t.hom i) :=
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} (A ⊗[R] B))
        (.up ℤ) i).mapIso t).toLinearEquiv.injective
    apply hi
    exact (identityRestrictionHomology (A ⊗[R] B) K i (nc (e.hom x))).trans
      (hcomp x)
  let mt := @BaseDerivedTensorCohomologyModel.ordinaryToLocalized R A B _ _ _ _ _
    dR dB Q D _ _ m
  let nt := @BaseDerivedTensorCohomologyModel.ordinaryToLocalized R A B _ _ _ _ _
    dR' dB' Q D _ _ n
  have hlocal : mt = nt := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply ExtendScalars.hom_ext
    intro x
    exact (@BaseDerivedTensorCohomologyModel.ordinaryToLocalized_tmul
      R A B _ _ _ _ _ dR dB Q D _ _ m j 1 x).trans
        (@BaseDerivedTensorCohomologyModel.ordinaryToLocalized_tmul
          R A B _ _ _ _ _ dR' dB' Q D _ _ n j 1 x).symm
  have hmeq := @BaseDerivedTensorCohomologyModel.localized_eq
    R A B _ _ _ _ _ dR dB Q D _ _ m i
  have hneq := @BaseDerivedTensorCohomologyModel.localized_eq
    R A B _ _ _ _ _ dR' dB' Q D _ _ n i
  let J := extendScalars (algebraMap (A ⊗[R] B) D)
  let adj := extendRestrictScalarsAdj (algebraMap (A ⊗[R] B) D)
  refine ⟨J.mapIso e, ?_⟩
  apply (adj.homEquiv _ _).injective
  dsimp only [Functor.mapIso_hom]
  rw [adj.homEquiv_naturality_left]
  simp only [Adjunction.homEquiv_unit]
  rw [hneq, hmeq]
  change e.hom ≫ (nc ≫ HomologicalComplex.homologyMap nt i ≫ _) =
    mc ≫ HomologicalComplex.homologyMap mt i ≫ _
  rw [← Category.assoc, ← Category.assoc, hc, hlocal]
  simp only [Category.assoc]

end ModuleCat
