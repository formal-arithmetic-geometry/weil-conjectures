/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientRingSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyConstantPullback
public import WeilConjectures.Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Profinite test objects over an object of the pro-étale site

Let `X` be a scheme with `k : X ⟶ Spec ℤ`, `U` an object of `X_proét` and `S` a profinite set.
The profinite test object over `U` is `U[S] = Spec LC(S, ℤ) ×_{Spec ℤ} U`
(`AlgebraicGeometry.ProEtale.testObject`), regarded as an object of `X_proét` through `U ⟶ X`.
This file computes its connected components and the sections of the coefficient sheaf
`Λ_X = k^* p^* Λ` over it, towards an `ℓ`-adic Haar trace for the trivial pro-étale torsor
`X[G] ⟶ X` under a profinite group `G`.

## Main results

* `LocallyConstant.tensorAlgEquiv`: `LC(S, ℤ) ⊗_ℤ A ≅ LC(S, A)` for a ring `A` and `S` compact;
  hence `LC(S, A)` is the coproduct of `LC(S, ℤ)` and `A` in commutative rings
  (`AlgebraicGeometry.ProEtale.isColimitBinaryCofanLocallyConstant`).
* `AlgebraicGeometry.ProEtale.isLimitTestObject`: `U[S]` is the fibre product `U ×_X X[S]` in
  `X_proét`, with projections `testObjectFst` and `testObjectSnd`.
* `AlgebraicGeometry.ProEtale.isHomeomorph_testObjectSchemeToProd`: for `U ≅ Spec R`, the map
  `U[S] → S × U` given by the two projections is a homeomorphism, as
  `U[S] ≅ Spec LC(S, R)` (`AlgebraicGeometry.ProEtale.isPullback_specLocallyConstant`) and
  `Spec LC(S, R) ≅ S × Spec R` (`LocallyConstant.homeomorphPrimeSpectrum`).
* `AlgebraicGeometry.ProEtale.bijective_connectedComponentsTestObjectToProd` and
  `AlgebraicGeometry.ProEtale.connectedComponentsAlongTestObjectIso`: for `U` affine,
  `π₀(U[S]) ≅ π₀(U) × S`.
* `AlgebraicGeometry.ProEtale.bijective_sections_testObject`: if `V ↦ Λ(π₀ V)` agrees with its
  sheafification on sections over `U[S]`, then `Λ(π₀(U) × S) ≅ Λ_X(U[S])`.
-/

@[expose] public section

universe u v

open CategoryTheory Limits Opposite TensorProduct

namespace LocallyConstant

/-! ### `LC(T, ℤ) ⊗_ℤ A = LC(T, A)` -/

section Tensor

variable (T : Type u) [TopologicalSpace T] (A : Type v) [CommRing A]

/-- The comparison `LC(T, ℤ) ⊗_ℤ A ⟶ LC(T, A)`, `a ⊗ r ↦ (t ↦ a(t) r)`. -/
noncomputable def tensorToLocallyConstant : LocallyConstant T ℤ ⊗[ℤ] A →ₐ[ℤ] LocallyConstant T A :=
  Algebra.TensorProduct.lift (mapRingHom (Int.castRingHom A)).toIntAlgHom
    (algebraMap A (LocallyConstant T A)).toIntAlgHom fun _ _ ↦ Commute.all _ _

variable {T A}

lemma tensorToLocallyConstant_tmul (a : LocallyConstant T ℤ) (r : A) :
    tensorToLocallyConstant T A (a ⊗ₜ r) = a.map (Int.cast : ℤ → A) * algebraMap A _ r :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

lemma tensorToLocallyConstant_tmul_apply (a : LocallyConstant T ℤ) (r : A) (t : T) :
    tensorToLocallyConstant T A (a ⊗ₜ r) t = (a t : A) * r := by
  rw [tensorToLocallyConstant_tmul]
  rfl

variable [CompactSpace T]

/-- Every element of `LC(T, ℤ) ⊗_ℤ A` is a sum `∑ χ_v ⊗ w(v)` over the fibres of a locally constant
function `c`, with `χ_v` the characteristic function of the fibre over `v`. -/
lemma exists_eq_sum_fiberCharFn_tmul (z : LocallyConstant T ℤ ⊗[ℤ] A) :
    ∃ (V : Type (max u v)) (c : LocallyConstant T V) (w : V → A),
      z = ∑ v ∈ c.range_finite.toFinset, fiberCharFn ℤ c v ⊗ₜ w v := by
  classical
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset z
  let c : LocallyConstant T (s → ℤ) := unflip fun i ↦ i.1.1
  refine ⟨s → ℤ, c, fun v ↦ ∑ i : s, v i • i.1.2, ?_⟩
  have hmul (i : s) (v : s → ℤ) :
      fiberCharFn ℤ c v * i.1.1 = v i • fiberCharFn ℤ c v := by
    ext t
    rw [coe_mul, Pi.mul_apply, coe_smul, Pi.smul_apply, fiberCharFn_apply, smul_eq_mul]
    split_ifs with h
    · rw [← h, mul_one, one_mul]
      rfl
    · simp
  calc ∑ i ∈ s, i.1 ⊗ₜ i.2 = ∑ i : s, i.1.1 ⊗ₜ i.1.2 := (Finset.sum_coe_sort s _).symm
    _ = ∑ i : s, ∑ v ∈ c.range_finite.toFinset, fiberCharFn ℤ c v ⊗ₜ[ℤ] (v i • i.1.2) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        conv_lhs => rw [← one_mul i.1.1, ← sum_fiberCharFn (R := ℤ) c]
        rw [Finset.sum_mul, TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        rw [hmul, TensorProduct.smul_tmul]
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        rw [TensorProduct.tmul_sum]

lemma tensorToLocallyConstant_injective : Function.Injective (tensorToLocallyConstant T A) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨V, c, w, rfl⟩ := exists_eq_sum_fiberCharFn_tmul z
  have hw (t : T) : w (c t) = 0 := by
    have h := congrArg (fun f : LocallyConstant T A ↦ f t) hz
    simp only [map_sum, sum_apply, tensorToLocallyConstant_tmul_apply, fiberCharFn_apply] at h
    simpa [Finset.sum_ite_eq', c.range_finite.mem_toFinset] using h
  refine Finset.sum_eq_zero fun v hv ↦ ?_
  obtain ⟨t, rfl⟩ := c.range_finite.mem_toFinset.1 hv
  rw [hw, TensorProduct.tmul_zero]

lemma tensorToLocallyConstant_surjective :
    Function.Surjective (tensorToLocallyConstant T A) := by
  classical
  intro f
  refine ⟨∑ v ∈ f.range_finite.toFinset, fiberCharFn ℤ f v ⊗ₜ v, ?_⟩
  ext t
  simp only [map_sum, sum_apply, tensorToLocallyConstant_tmul_apply, fiberCharFn_apply]
  simp [f.range_finite.mem_toFinset]

variable (T A) in
/-- `LC(T, ℤ) ⊗_ℤ A ≅ LC(T, A)` for `T` compact. -/
noncomputable def tensorAlgEquiv : LocallyConstant T ℤ ⊗[ℤ] A ≃ₐ[ℤ] LocallyConstant T A :=
  AlgEquiv.ofBijective (tensorToLocallyConstant T A)
    ⟨tensorToLocallyConstant_injective, tensorToLocallyConstant_surjective⟩

end Tensor

end LocallyConstant

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### `LC(S, A)` as a coproduct of rings -/

/-- `LC(S, A)` is the coproduct of `LC(S, ℤ)` and `A` in commutative rings, with the maps
`a ↦ (t ↦ a(t))` and the constant functions. -/
noncomputable def isColimitBinaryCofanLocallyConstant (S : Type u) [TopologicalSpace S]
    [CompactSpace S] (A : CommRingCat.{u}) :
    IsColimit (BinaryCofan.mk
      (CommRingCat.ofHom (LocallyConstant.mapRingHom (Int.castRingHom A)) :
        CommRingCat.of (LocallyConstant S ℤ) ⟶ CommRingCat.of (LocallyConstant S A))
      (CommRingCat.ofHom (algebraMap A (LocallyConstant S A)))) :=
  (CommRingCat.coproductCoconeIsColimit _ _).ofIsoColimit
    (BinaryCofan.ext (LocallyConstant.tensorAlgEquiv S A).toRingEquiv.toCommRingCatIso
      (by
        ext a : 2
        refine (LocallyConstant.tensorToLocallyConstant_tmul a 1).trans ?_
        rw [map_one, mul_one]
        rfl)
      (by
        ext r : 2
        refine LocallyConstant.ext fun t ↦
          (LocallyConstant.tensorToLocallyConstant_tmul_apply 1 r t).trans ?_
        simp only [LocallyConstant.coe_one, Pi.one_apply, Int.cast_one, one_mul]
        rfl))

/-! ### The profinite test objects over an object of `X_proét` -/

section TestObject

variable {X : Scheme.{u}} (k : X ⟶ specZ.{u}) (U : X.ProEt) (S : Profinite.{u})

/-- The underlying scheme `U[S] = Spec LC(S, ℤ) ×_{Spec ℤ} U` of the profinite test object over
`U`. -/
noncomputable abbrev testObjectScheme : Scheme.{u} :=
  pullback (profiniteToProEt.obj S).hom (U.hom ≫ k)

/-- The profinite test object `U[S] = Spec LC(S, ℤ) ×_{Spec ℤ} U` over an object `U` of
`X_proét`, as an object of `X_proét`. -/
noncomputable def testObject : X.ProEt :=
  ProEt.mk (pullback.snd (profiniteToProEt.obj S).hom (U.hom ≫ k) ≫ U.hom)

/-- The projection `U[S] ⟶ U`. -/
noncomputable def testObjectFst : testObject k U S ⟶ U :=
  MorphismProperty.Over.homMk (pullback.snd _ _) rfl

lemma testObjectFst_left :
    (testObjectFst k U S).left = pullback.snd (profiniteToProEt.obj S).hom (U.hom ≫ k) :=
  rfl

/-- The projection `U[S] ⟶ X[S]`. -/
noncomputable def testObjectSnd : testObject k U S ⟶ (profiniteToProEtAlong k).obj S :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ U.hom)
      (specULiftZIsTerminal.hom_ext _ _))
    (pullback.lift_snd _ _ _)

lemma testObjectSnd_left :
    (testObjectSnd k U S).left = pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ U.hom)
      (specULiftZIsTerminal.hom_ext _ _) :=
  rfl

variable {k U S} in
/-- The morphism `W ⟶ U[S]` induced by morphisms `W ⟶ U` and `W ⟶ X[S]`. -/
noncomputable def testObjectLift {W : X.ProEt} (f : W ⟶ U)
    (g : W ⟶ (profiniteToProEtAlong k).obj S) :
    W ⟶ testObject k U S :=
  MorphismProperty.Over.homMk
    (pullback.lift (g.left ≫ pullback.fst _ _) f.left (specULiftZIsTerminal.hom_ext _ _))
    ((pullback.lift_snd_assoc _ _ _ _).trans (MorphismProperty.Over.w f))

variable {k U S} in
lemma testObjectLift_left {W : X.ProEt} (f : W ⟶ U)
    (g : W ⟶ (profiniteToProEtAlong k).obj S) :
    (testObjectLift f g).left =
      pullback.lift (g.left ≫ pullback.fst _ _) f.left (specULiftZIsTerminal.hom_ext _ _) :=
  rfl

/-- **Pullback of test objects.** `U[S]` is the fibre product `U ×_X X[S]`: the projections
`U[S] ⟶ U` and `U[S] ⟶ X[S]` form a product cone in `X_proét`. -/
noncomputable def isLimitTestObject :
    IsLimit (BinaryFan.mk (testObjectFst k U S) (testObjectSnd k U S)) :=
  BinaryFan.IsLimit.mk _ testObjectLift
    (fun f g ↦ MorphismProperty.Over.Hom.ext (by
      rw [MorphismProperty.Comma.comp_left, testObjectLift_left, BinaryFan.mk_fst,
        testObjectFst_left, pullback.lift_snd]))
    (fun f g ↦ MorphismProperty.Over.Hom.ext (by
      rw [MorphismProperty.Comma.comp_left, testObjectLift_left, BinaryFan.mk_snd,
        testObjectSnd_left]
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
        exact (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm))
    (fun f g m hf hg ↦ MorphismProperty.Over.Hom.ext (by
      rw [testObjectLift_left]
      refine pullback.hom_ext ?_ ?_
      · have h : m.left ≫ pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ U.hom)
            (specULiftZIsTerminal.hom_ext _ _) ≫ pullback.fst _ k =
            g.left ≫ pullback.fst _ k :=
          congrArg (fun φ ↦ φ.left ≫ pullback.fst (profiniteToProEt.obj S).hom k) hg
        rw [pullback.lift_fst, ← h, pullback.lift_fst]
      · have h : m.left ≫ pullback.snd _ _ = f.left := congrArg (fun φ ↦ φ.left) hf
        rw [pullback.lift_snd, h]))

end TestObject

/-! ### The underlying space of `U[S]` for `U` affine -/

section Space

variable {X : Scheme.{u}} (k : X ⟶ specZ.{u}) (U : X.ProEt) (S : Profinite.{u})

/-- The continuous map `U[S] → S × U`, `x ↦ (pr_S x, pr_U x)`. -/
noncomputable def testObjectSchemeToProd : C(testObjectScheme k U S, S × U.left) :=
  ⟨fun x ↦ (specLocallyConstantToProfinite S
      (pullback.fst (profiniteToProEt.obj S).hom (U.hom ≫ k) x),
      pullback.snd (profiniteToProEt.obj S).hom (U.hom ≫ k) x),
    ((specLocallyConstantToProfinite S).continuous.comp
      (Scheme.Hom.continuous (pullback.fst (profiniteToProEt.obj S).hom (U.hom ≫ k)))).prodMk
      (Scheme.Hom.continuous (pullback.snd (profiniteToProEt.obj S).hom (U.hom ≫ k)))⟩

/-- The projection `Spec LC(S, R) → S` along `LC(S, ℤ) → LC(S, R)` sends the point `(s, p)`
to `s`. -/
lemma specMap_mapRingHom_toPrimeSpectrum {R : Type u} [CommRing R] (s : S)
    (p : PrimeSpectrum R) :
    LocallyConstant.specMap (LocallyConstant.mapRingHom (Int.castRingHom R))
      (LocallyConstant.toPrimeSpectrum (s, p)) = s := by
  have h := LocallyConstant.comap_eq_toPrimeSpectrum_specMap
    (LocallyConstant.mapRingHom (Int.castRingHom R) : LocallyConstant S ℤ →+* LocallyConstant S R)
    (LocallyConstant.toPrimeSpectrum (s, p))
  have h' : PrimeSpectrum.comap
      (LocallyConstant.mapRingHom (Int.castRingHom R) : LocallyConstant S ℤ →+* LocallyConstant S R)
      (LocallyConstant.toPrimeSpectrum (s, p)) =
      LocallyConstant.toPrimeSpectrum (s, PrimeSpectrum.comap (Int.castRingHom R) p) := by
    ext f
    exact Iff.rfl
  rw [h'] at h
  exact (congrArg Prod.fst (LocallyConstant.toPrimeSpectrum_injective h)).symm

variable {R : CommRingCat.{u}}

/-- For `U ≅ Spec R`, the square exhibiting `Spec LC(S, R)` as `Spec LC(S, ℤ) ×_{Spec ℤ} U`. -/
lemma isPullback_specLocallyConstant (e : U.left ≅ Spec R) :
    IsPullback (Spec.map (CommRingCat.ofHom (LocallyConstant.mapRingHom (Int.castRingHom R)) :
        CommRingCat.of (LocallyConstant S ℤ) ⟶ CommRingCat.of (LocallyConstant S R)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (LocallyConstant S R))) ≫ e.inv)
      (profiniteToProEt.obj S).hom (U.hom ≫ k) := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _ (IsPushout.of_is_coproduct'
    (isColimitBinaryCofanLocallyConstant S R) CommRingCat.isInitial)
  exact h.of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) (by simp) (by simp)
    (specULiftZIsTerminal.hom_ext _ _) (specULiftZIsTerminal.hom_ext _ _)

/-- **The underlying space of `U[S]`.** For `U ≅ Spec R`, the map `U[S] → S × U` is a
homeomorphism: `U[S] ≅ Spec LC(S, R)` and `Spec LC(S, R) ≅ S × Spec R`. -/
theorem isHomeomorph_testObjectSchemeToProd (e : U.left ≅ Spec R) :
    IsHomeomorph (testObjectSchemeToProd k U S) := by
  let hP := isPullback_specLocallyConstant k U S e
  let g : S × PrimeSpectrum R ≃ₜ testObjectScheme k U S :=
    LocallyConstant.homeomorphPrimeSpectrum.trans (Scheme.homeoOfIso hP.isoPullback)
  let h : S × PrimeSpectrum R ≃ₜ S × U.left :=
    (Homeomorph.refl S).prodCongr (Scheme.homeoOfIso e.symm)
  have h1 (P : PrimeSpectrum (LocallyConstant S R)) :
      pullback.fst (profiniteToProEt.obj S).hom (U.hom ≫ k) (hP.isoPullback.hom P) =
        Spec.map (CommRingCat.ofHom (LocallyConstant.mapRingHom (Int.castRingHom R)) :
          CommRingCat.of (LocallyConstant S ℤ) ⟶ CommRingCat.of (LocallyConstant S R)) P := by
    rw [← Scheme.Hom.comp_apply, hP.isoPullback_hom_fst]
    rfl
  have h2 (P : PrimeSpectrum (LocallyConstant S R)) :
      pullback.snd (profiniteToProEt.obj S).hom (U.hom ≫ k) (hP.isoPullback.hom P) =
        e.inv (Spec.map (CommRingCat.ofHom (algebraMap R (LocallyConstant S R))) P) := by
    rw [← Scheme.Hom.comp_apply, hP.isoPullback_hom_snd, Scheme.Hom.comp_apply]
    rfl
  have key : ⇑(testObjectSchemeToProd k U S) = ⇑(g.symm.trans h) := by
    funext x
    rw [← g.apply_symm_apply x]
    generalize g.symm x = y
    refine Eq.trans ?_ (congrArg h (g.symm_apply_apply y)).symm
    obtain ⟨s, p⟩ := y
    refine Prod.ext ?_ ?_
    · exact (congrArg (specLocallyConstantToProfinite S) (h1 _)).trans
        (specMap_mapRingHom_toPrimeSpectrum S s p)
    · exact (h2 _).trans
        (congrArg e.inv (LocallyConstant.comap_algebraMap_toPrimeSpectrum (s, p)))
  rw [key]
  exact (g.symm.trans h).isHomeomorph

end Space

/-! ### Connected components of `U[S]` -/

section ConnectedComponents

/-- A homeomorphism induces a homeomorphism of the spaces of connected components. -/
noncomputable def _root_.Homeomorph.connectedComponentsCongr {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) : ConnectedComponents A ≃ₜ ConnectedComponents B :=
  e.isQuotientMap.isCoinducing.connectedComponentsHomeomorph fun b ↦ by
    rw [← e.image_symm, Set.image_singleton]
    exact isConnected_singleton

lemma _root_.Homeomorph.connectedComponentsCongr_mk {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (a : A) :
    e.connectedComponentsCongr (ConnectedComponents.mk a) = ConnectedComponents.mk (e a) :=
  rfl

/-- For a totally disconnected space `S`, the map `π₀(S × W) → π₀(W) × S` is bijective. -/
lemma bijective_connectedComponentsLift_prod_swap (S W : Type*) [TopologicalSpace S]
    [TopologicalSpace W] [TotallyDisconnectedSpace S] :
    Function.Bijective (Continuous.connectedComponentsLift
      (f := fun x : S × W ↦ (ConnectedComponents.mk x.2, x.1))
      ((ConnectedComponents.continuous_coe.comp continuous_snd).prodMk continuous_fst)) := by
  let h : ConnectedComponents S × ConnectedComponents W ≃ ConnectedComponents W × S :=
    (Equiv.prodComm _ _).trans
      (Equiv.prodCongr (Equiv.refl _) (ConnectedComponents.mkHomeomorph (S := S)).symm.toEquiv)
  have key : Continuous.connectedComponentsLift
      (f := fun x : S × W ↦ (ConnectedComponents.mk x.2, x.1))
      ((ConnectedComponents.continuous_coe.comp continuous_snd).prodMk continuous_fst) =
      h ∘ Continuous.connectedComponentsLift
        (f := fun x : S × W ↦ (ConnectedComponents.mk x.1, ConnectedComponents.mk x.2))
        (by continuity) := by
    funext x
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    rfl
  rw [key]
  exact h.bijective.comp (ConnectedComponents.bijective_connectedComponentsLift_prod S W)

variable {X : Scheme.{u}} (k : X ⟶ specZ.{u}) (U : X.ProEt) (S : Profinite.{u}) [IsAffine U.left]

/-- `U[S]` is affine for `U` affine. -/
instance isAffine_testObjectScheme : IsAffine (testObjectScheme k U S) :=
  Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine (X := Spec _) (Y := U.left)
    (Z := Spec _) _ _

/-- The homeomorphism `Spec Γ(U[S]) ≅ U[S] ≅ S × U ≅ S × Spec Γ(U)` for `U` affine. -/
noncomputable def specΓTestObjectHomeomorph :
    PrimeSpectrum Γ(testObjectScheme k U S, ⊤) ≃ₜ S × PrimeSpectrum Γ(U.left, ⊤) :=
  (Scheme.homeoOfIso (testObjectScheme k U S).isoSpec.symm).trans
    (((isHomeomorph_testObjectSchemeToProd k U S U.left.isoSpec).homeomorph _).trans
      ((Homeomorph.refl S).prodCongr (Scheme.homeoOfIso U.left.isoSpec)))

/-- The continuous map `π₀(Spec Γ(U[S])) → π₀(Spec Γ(U)) × S` for `U` affine, induced by the
projections `U[S] → U` and `U[S] → S`. -/
noncomputable def connectedComponentsTestObjectToProd :
    C(ConnectedComponents (PrimeSpectrum Γ(testObjectScheme k U S, ⊤)),
      ConnectedComponents (PrimeSpectrum Γ(U.left, ⊤)) × S) :=
  let F : C(PrimeSpectrum Γ(testObjectScheme k U S, ⊤),
      ConnectedComponents (PrimeSpectrum Γ(U.left, ⊤)) × S) :=
    ⟨fun x ↦ (ConnectedComponents.mk (specΓTestObjectHomeomorph k U S x).2,
      (specΓTestObjectHomeomorph k U S x).1),
      ((ConnectedComponents.continuous_coe.comp
        (continuous_snd.comp (specΓTestObjectHomeomorph k U S).continuous)).prodMk
        (continuous_fst.comp (specΓTestObjectHomeomorph k U S).continuous))⟩
  ⟨F.continuous.connectedComponentsLift, F.continuous.connectedComponentsLift_continuous⟩

/-- **Connected components of `U[S]`.** For `U` affine, the map
`π₀(Spec Γ(U[S])) → π₀(Spec Γ(U)) × S` is bijective. -/
theorem bijective_connectedComponentsTestObjectToProd :
    Function.Bijective (connectedComponentsTestObjectToProd k U S) := by
  have key : ⇑(connectedComponentsTestObjectToProd k U S) =
      Continuous.connectedComponentsLift
        (f := fun x : S × PrimeSpectrum Γ(U.left, ⊤) ↦ (ConnectedComponents.mk x.2, x.1))
        ((ConnectedComponents.continuous_coe.comp continuous_snd).prodMk continuous_fst) ∘
          (specΓTestObjectHomeomorph k U S).connectedComponentsCongr := by
    funext x
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    rfl
  rw [key]
  exact (bijective_connectedComponentsLift_prod_swap _ _).comp
    (specΓTestObjectHomeomorph k U S).connectedComponentsCongr.bijective

end ConnectedComponents

/-! ### Sections of the coefficient sheaf over `U[S]` -/

section Sections

variable {X : Scheme.{u}} (k : X ⟶ specZ.{u}) (U : X.ProEt) (S : Profinite.{u}) [IsAffine U.left]

/-- The isomorphism `π₀(U[S]) ≅ π₀(U) × S` of profinite sets, for `U` affine
(`AlgebraicGeometry.ProEtale.bijective_connectedComponentsTestObjectToProd`). -/
noncomputable def connectedComponentsAlongTestObjectIso :
    (connectedComponentsAlong k).obj (testObject k U S) ≅
      Profinite.of ((connectedComponentsAlong k).obj U × S) :=
  have := CompHausLike.isIso_of_bijective
    (ConcreteCategory.ofHom (connectedComponentsTestObjectToProd k U S) :
      (connectedComponentsAlong k).obj (testObject k U S) ⟶
        Profinite.of ((connectedComponentsAlong k).obj U × S))
    (bijective_connectedComponentsTestObjectToProd k U S)
  asIso (ConcreteCategory.ofHom (connectedComponentsTestObjectToProd k U S))

/-- **Sections of the coefficient sheaf over `U[S]`.** Let `U` be an affine object of `X_proét`
and `S` a profinite set, such that the presheaf `V ↦ Λ(π₀ V)` agrees with its sheafification on
sections over `U[S]`. Then the restriction of the map `Λ(π₀(U[S])) ⟶ Λ_X(U[S])` of
`AlgebraicGeometry.ProEtale.bijective_unit_app_comp_map_unit` along `π₀(U[S]) ≅ π₀(U) × S` is a
bijection `Λ(π₀(U) × S) ≅ Λ_X(U[S])`. -/
theorem bijective_sections_testObject (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (hV : Function.Bijective
      ((toSheafify (ProEt.topology X) ((connectedComponentsAlong k).op ⋙ Λ.obj)).app
        (op (testObject k U S)))) :
    Function.Bijective (Λ.obj.map (connectedComponentsAlongTestObjectIso k U S).hom.op ≫
      ((upperStarFromPointAlongAdjunction k).unit.app Λ).hom.app
        (op ((connectedComponentsAlong k).obj (testObject k U S))) ≫
      ((pointUpperStar ⋙ (k)^*[Ab.{u + 1}]).obj Λ).obj.map
        ((connectedComponentsAlongAdjunction k).unit.app (testObject k U S)).op) := by
  rw [ConcreteCategory.coe_comp]
  exact (bijective_unit_app_comp_map_unit k Λ _ hV).comp (ConcreteCategory.bijective_of_isIso _)

end Sections

end AlgebraicGeometry.ProEtale
