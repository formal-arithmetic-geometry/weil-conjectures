/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
import all WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
import all WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection

/-! # The addition presentation of a vector-bundle self-product

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/
sk-prop-sp-orientation/sk-prop-sp-orientation-vector-bundle.proof.md, Step 1.
(blueprint: lem-pur-vector-diagonal-addition-presentation).
The maps are constructed from symmetric-algebra maps on generators.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.VectorTraceGeometry

attribute [local implicit_reducible] Scheme.Modules baseChange first second sumIso bundleLinear

/-- The invertible linear substitution used in the addition coordinates.
Source: vector-bundle orientation, Step 1.
(blueprint: lem-pur-vector-diagonal-addition-presentation). -/
def diagonalShearLinear (S : Scheme.{u}) (M : S.Modules) : sum S M M ≅ sum S M M where
  hom := biprod.desc biprod.inr (biprod.inl + biprod.inr)
  inv := biprod.desc (-biprod.inl + biprod.inr) biprod.inl
  hom_inv_id := by
    apply biprod.hom_ext' <;> simp [Preadditive.add_comp]
  inv_hom_id := by
    apply biprod.hom_ext' <;> simp [Preadditive.add_comp]

private theorem additionSymmetricMap_spec (S : Scheme.{u}) (F G : S.Modules) (j : G ⟶ F)
    (U : S.Opens) (x : G.val.obj (op U)) :
    (WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap S F G j).right.hom.app
        (op U) ((SymmetricAlgebraSheaf.inclusion G).val.app (op U) x) =
      (SymmetricAlgebraSheaf.inclusion F).val.app (op U) (j.val.app (op U) x) :=
  (exists_quasiCoherentSymmetricAlgebra_core S G (SymmetricAlgebraSheaf.algebra F)
    (j ≫ SymmetricAlgebraSheaf.inclusion F)).exists.choose_spec U x

/-- Symmetric algebra takes inverse linear substitutions to inverse algebra maps.
Source: vector-bundle orientation, Step 1; uniqueness on degree-one generators.
(blueprint: lem-pur-vector-diagonal-addition-presentation). -/
theorem additionSymmetricMap_inverse (S : Scheme.{u}) (F G : S.Modules)
    (j : G ≅ F) :
    WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap S F G j.hom ≫
      WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap S G F j.inv = 𝟙 _ := by
  apply (exists_quasiCoherentSymmetricAlgebra_core S G
    (SymmetricAlgebraSheaf.algebra G) (SymmetricAlgebraSheaf.inclusion G)).unique
  · intro U x
    change (WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap
      S G F j.inv).right.hom.app (op U)
      ((WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap
        S F G j.hom).right.hom.app (op U) _) = _
    rw [additionSymmetricMap_spec, additionSymmetricMap_spec]
    have h := congrArg (fun k : G ⟶ G ↦ k.val.app (op U) x) j.hom_inv_id
    exact congrArg ((SymmetricAlgebraSheaf.inclusion G).val.app (op U)) h
  · intros
    rfl

/-- The symmetric-algebra shear (u,v) |-> (v,u+v), with its polynomial inverse.
Source: diagonal orientation for a vector bundle, proof Step 1.
(blueprint: lem-pur-vector-diagonal-addition-presentation). -/
def additionShear (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    VectorBundleZeroSection.scheme S (d + d) (sum S M M) ≅
      VectorBundleZeroSection.scheme S (d + d) (sum S M M) := by
  classical
  let j := diagonalShearLinear S M
  let a : SymmetricAlgebraSheaf.algebra (sum S M M) ≅
      SymmetricAlgebraSheaf.algebra (sum S M M) := {
    hom := WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap
      S (sum S M M) (sum S M M) j.hom
    inv := WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap
      S (sum S M M) (sum S M M) j.inv
    hom_inv_id := additionSymmetricMap_inverse S _ _ j
    inv_hom_id := additionSymmetricMap_inverse S _ _ j.symm }
  let b : VectorBundleZeroSection.algebraObject S (d + d) (sum S M M) ≅
      VectorBundleZeroSection.algebraObject S (d + d) (sum S M M) := ObjectProperty.isoMk _ a
  exact (ObjectProperty.ι _ ⋙ Over.forget S).mapIso
    ((VectorBundleZeroSection.antiEquivalence S).inverse.mapIso b).unop

private theorem purityBundleMap_comp
    (S : Scheme.{u}) [IsNoetherian S] (r s t : ℕ) (F G H : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    [H.IsFiniteLocallyFreeOfRank t] (j : G ⟶ F) (k : H ⟶ G) :
    WeilConjectures.PurityFiniteSetting.purityBundleMap S r s F G j ≫
        WeilConjectures.PurityFiniteSetting.purityBundleMap S s t G H k =
      WeilConjectures.PurityFiniteSetting.purityBundleMap S r t F H (k ≫ j) := by
  let ρ := VectorBundleZeroSection.π S r F
  apply bundle_hom_ext t H ρ _ _
    (by rw [Category.assoc, purityBundleMap_comm, purityBundleMap_comm])
    (purityBundleMap_comm S r t F H (k ≫ j))
  rw [bundleLinear_purityBundleMap s t G H k ρ
    (WeilConjectures.PurityFiniteSetting.purityBundleMap S r s F G j)
    (purityBundleMap_comm S r s F G j)]
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (WeilConjectures.PurityFiniteSetting.purityBundleMap S r s F G j).appLE
    _ _ _ (generator S s G U (k.val.app (op U) x)) =
    (WeilConjectures.PurityFiniteSetting.purityBundleMap S r t F H (k ≫ j)).appLE
      _ _ _ (generator S t H U x)
  rw [purityBundleMap_generators, purityBundleMap_generators]
  rfl

/-- Addition's first coordinate is the original base coordinate.
Source: vector-bundle diagonal orientation, Step 1.
(blueprint: lem-pur-vector-diagonal-addition-presentation).
Proof: the shear sends the first generator to the second. Functoriality of relative
Spec and the symmetric-algebra generator equations identify the two maps. -/
theorem additionShear_first (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    (additionShear S d M).hom ≫ first S d d M M = second S d d M M := by
  change WeilConjectures.PurityFiniteSetting.purityBundleMap S (d + d) (d + d)
      (sum S M M) (sum S M M) (diagonalShearLinear S M).hom ≫
    WeilConjectures.PurityFiniteSetting.purityBundleMap S (d + d) d (sum S M M) M
      biprod.inl = _
  rw [purityBundleMap_comp]
  simp only [diagonalShearLinear, biprod.inl_desc]
  rfl

private theorem zero_generator (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (U : S.Opens) (x : M.val.obj (op U)) :
    (VectorBundleZeroSection.zero S d M).appLE
      ((VectorBundleZeroSection.π S d M) ⁻¹ᵁ U) U
      (by rw [← Scheme.Hom.comp_preimage, (VectorBundleZeroSection.zero_spec S d M).1];
          simp) (generator S d M U x) = 0 := by
  have h := congrArg (fun a ↦ a ((SymmetricAlgebraSheaf.inclusion M).val.app (op U) x))
    (VectorBundleZeroSection.zero_pullback S d M U)
  exact h.trans ((VectorBundleZeroSection.augmentation_spec S M).1 U x)

private theorem bundleLinear_zero {S X : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] (ρ : X ⟶ S) :
    bundleLinear d M ρ (ρ ≫ VectorBundleZeroSection.zero S d M)
      (by rw [Category.assoc, (VectorBundleZeroSection.zero_spec S d M).1,
        Category.comp_id]) = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (ρ ≫ VectorBundleZeroSection.zero S d M).appLE _ _ _
    (generator S d M U x) = 0
  rw [← Scheme.Hom.appLE_comp_appLE ρ (VectorBundleZeroSection.zero S d M)
    ((VectorBundleZeroSection.π S d M) ⁻¹ᵁ U) U (ρ ⁻¹ᵁ U)
    (by rw [← Scheme.Hom.comp_preimage, (VectorBundleZeroSection.zero_spec S d M).1]
        simp) le_rfl, CommRingCat.comp_apply, zero_generator, map_zero]

/-- Relative symmetric-algebra base change preserves the zero section.
Source: vector-bundle orientation, Step 1. On degree-one generators both maps are
zero, and both are over the same base map; the universal property identifies them.
(blueprint: lem-pur-vector-diagonal-addition-presentation). -/
theorem baseChange_zero {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (d : ℕ) (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    VectorBundleZeroSection.zero T d ((Scheme.Modules.tensorPullback f).obj M) ≫
      baseChange f d M = f ≫ VectorBundleZeroSection.zero S d M := by
  let F := (Scheme.Modules.tensorPullback f).obj M
  let z := VectorBundleZeroSection.zero T d F
  have hz := (VectorBundleZeroSection.zero_spec T d F).1
  have hm := map_spec f d d M F
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app M)
  apply bundle_hom_ext d M f _ _
    (by
      change z ≫ map f d d M F _ ≫ VectorBundleZeroSection.π S d M = f
      rw [hm.comm, ← Category.assoc, hz, Category.id_comp])
    (by rw [Category.assoc, (VectorBundleZeroSection.zero_spec S d M).1,
      Category.comp_id])
  have hc := bundleLinear_comp f d d M F _ _ hm (𝟙 T) z hz
  erw [hc]
  have hzero : bundleLinear d F (𝟙 T) z hz = 0 := by
    simpa only [Category.id_comp] using bundleLinear_zero d F (𝟙 T)
  erw [hzero, Functor.map_zero, zero_comp, comp_zero]
  exact (bundleLinear_zero d M f).symm

private theorem shear_second_on_zero (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] {X : Scheme.{u}} (ρ : X ⟶ S)
    (ℓ : X ⟶ VectorBundleZeroSection.scheme S (d + d) (sum S M M))
    (v : X ⟶ VectorBundleZeroSection.scheme S d M)
    (hℓ : ℓ ≫ VectorBundleZeroSection.π S (d + d) (sum S M M) = ρ)
    (hv : v ≫ VectorBundleZeroSection.π S d M = ρ)
    (hl : ℓ ≫ first S d d M M = ρ ≫ VectorBundleZeroSection.zero S d M)
    (hr : ℓ ≫ second S d d M M = v) :
    ℓ ≫ (additionShear S d M).hom ≫ second S d d M M = v := by
  have hc : (additionShear S d M).hom ≫ second S d d M M =
      WeilConjectures.PurityFiniteSetting.purityBundleMap S (d + d) d (sum S M M) M
        (biprod.inl + biprod.inr) := by
    change WeilConjectures.PurityFiniteSetting.purityBundleMap S (d + d) (d + d)
        (sum S M M) (sum S M M) (diagonalShearLinear S M).hom ≫
      WeilConjectures.PurityFiniteSetting.purityBundleMap S (d + d) d (sum S M M) M
        biprod.inr = _
    rw [purityBundleMap_comp]
    simp only [diagonalShearLinear, biprod.inr_desc]
  rw [hc]
  apply bundle_hom_ext d M ρ _ _
    (by rw [Category.assoc, purityBundleMap_comm, hℓ]) hv
  rw [bundleLinear_purityBundleMap (d + d) d (sum S M M) M
    (biprod.inl + biprod.inr) ρ ℓ hℓ, Preadditive.add_comp]
  have hl' := bundleLinear_congr d M ρ _ _
    (by rw [Category.assoc, first, purityBundleMap_comm, hℓ])
    (by rw [Category.assoc, (VectorBundleZeroSection.zero_spec S d M).1,
      Category.comp_id]) hl
  have hr' := bundleLinear_congr d M ρ _ _
    (by rw [Category.assoc, second, purityBundleMap_comm, hℓ]) hv hr
  dsimp only [first] at hl'
  dsimp only [second] at hr'
  rw [bundleLinear_purityBundleMap (d + d) d (sum S M M) M biprod.inl ρ ℓ hℓ,
    bundleLinear_zero] at hl'
  rw [bundleLinear_purityBundleMap (d + d) d (sum S M M) M biprod.inr ρ ℓ hℓ] at hr'
  rw [hl', hr', zero_add]

/-- The sum bundle is the fibre product of its two summands.
Source: vector-bundle orientation, Step 1; the base-change universal property.
(blueprint: lem-pur-vector-diagonal-addition-presentation). -/
def sumProductPresentation (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    VectorBundleZeroSection.scheme S (d + d) (sum S M M) ≅
      pullback (VectorBundleZeroSection.π S d M) (VectorBundleZeroSection.π S d M) := by
  let sq := baseChange_isPullback (VectorBundleZeroSection.π S d M) d M
  let a := sumIso S d d M M
  have hs := (existsUnique_sumIso S d d M M).exists.choose_spec
  let sq' : IsPullback (first S d d M M) (second S d d M M)
      (VectorBundleZeroSection.π S d M) (VectorBundleZeroSection.π S d M) := by
    apply sq.of_iso a (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simpa only [Iso.refl_hom, Category.comp_id, a, sumIso] using hs.1.symm
    · simpa only [Iso.refl_hom, Category.comp_id, a, sumIso] using hs.2.symm
    · simp
    · simp
  exact sq'.isoPullback

/-- The product presentation preserves the first coordinate.
Source: vector-bundle orientation, Step 1; the pullback projection equation.
(blueprint: lem-pur-vector-diagonal-addition-presentation). -/
theorem sumProductPresentation_first (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    (sumProductPresentation S d M).hom ≫
      pullback.fst (VectorBundleZeroSection.π S d M) (VectorBundleZeroSection.π S d M) =
      first S d d M M := by
  exact IsPullback.isoPullback_hom_fst _

/-- Addition identifies the pulled-back bundle with the self-product.
The definition uses only proved symmetric-algebra and pullback universal properties.
Source: vector-bundle orientation, proof Step 1.
(blueprint: lem-pur-vector-diagonal-addition-presentation). -/
def diagonalAdditionPresentation (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    VectorBundleZeroSection.scheme (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) ≅
      pullback (VectorBundleZeroSection.π S d M) (VectorBundleZeroSection.π S d M) :=
  sumIso S d d M M ≪≫ additionShear S d M ≪≫ sumProductPresentation S d M

/-- The addition presentation is over the first vector-bundle factor.
Source: vector-bundle orientation, Step 1. The symmetric generator equation for the
shear followed by the two product projection equations proves the assertion.
(blueprint: lem-pur-vector-diagonal-addition-presentation). -/
theorem diagonalAdditionPresentation_first (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    (diagonalAdditionPresentation S d M).hom ≫
      pullback.fst (VectorBundleZeroSection.π S d M) (VectorBundleZeroSection.π S d M) =
      VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) := by
  simp only [diagonalAdditionPresentation, Iso.trans_hom, Category.assoc,
    sumProductPresentation_first, additionShear_first]
  exact (existsUnique_sumIso S d d M M).exists.choose_spec.2

/-- The addition presentation takes the zero section to the diagonal.
Source: vector-bundle orientation, Step 1. Its first projection is the identity.
The second is zero plus the identity, using the symmetric-algebra generator equations.
(blueprint: lem-pur-vector-diagonal-addition-presentation). -/
theorem diagonalAdditionPresentation_zero (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    VectorBundleZeroSection.zero (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) ≫
      (diagonalAdditionPresentation S d M).hom =
      pullback.diagonal (VectorBundleZeroSection.π S d M) := by
  let V := VectorBundleZeroSection.scheme S d M
  let p := VectorBundleZeroSection.π S d M
  let F := (Scheme.Modules.tensorPullback p).obj M
  let z := VectorBundleZeroSection.zero V d F
  have hs := (existsUnique_sumIso S d d M M).exists.choose_spec
  have hz := (VectorBundleZeroSection.zero_spec V d F).1
  apply pullback.hom_ext
  · simp only [Category.assoc, diagonalAdditionPresentation_first, pullback.diagonal_fst]
    exact hz
  · have hl : (z ≫ (sumIso S d d M M).hom) ≫ first S d d M M =
        p ≫ VectorBundleZeroSection.zero S d M := by
      rw [Category.assoc, show (sumIso S d d M M).hom ≫ first S d d M M =
        baseChange p d M from hs.1, baseChange_zero]
    have hr : (z ≫ (sumIso S d d M M).hom) ≫ second S d d M M = 𝟙 V := by
      rw [Category.assoc, show (sumIso S d d M M).hom ≫ second S d d M M =
        VectorBundleZeroSection.π V d F from hs.2, hz]
    have hb : (z ≫ (sumIso S d d M M).hom) ≫
        VectorBundleZeroSection.π S (d + d) (sum S M M) = p := by
      calc
        _ = ((z ≫ (sumIso S d d M M).hom) ≫ second S d d M M) ≫ p := by
          change _ = ((z ≫ (sumIso S d d M M).hom) ≫
            WeilConjectures.PurityFiniteSetting.purityBundleMap S (d + d) d
              (sum S M M) M biprod.inr) ≫ VectorBundleZeroSection.π S d M
          simp only [Category.assoc, purityBundleMap_comm]
        _ = p := by rw [hr, Category.id_comp]
    have hsecond : (sumProductPresentation S d M).hom ≫ pullback.snd p p =
        second S d d M M := IsPullback.isoPullback_hom_snd _
    simp only [diagonalAdditionPresentation, Iso.trans_hom, Category.assoc,
      pullback.diagonal_snd]
    change z ≫ (sumIso S d d M M).hom ≫ (additionShear S d M).hom ≫
      (sumProductPresentation S d M).hom ≫ pullback.snd p p = 𝟙 V
    rw [hsecond]
    simpa only [Category.assoc] using
      shear_second_on_zero S d M p (z ≫ (sumIso S d d M M).hom) (𝟙 V)
        hb (Category.id_comp p) hl hr

end AlgebraicGeometry.VectorTraceGeometry
