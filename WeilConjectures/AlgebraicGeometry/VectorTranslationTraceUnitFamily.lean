/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
public import WeilConjectures.AlgebraicGeometry.Vector.VectorTraceGeometricDescent
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion
public import WeilConjectures.AlgebraicGeometry.ConstantTraceLineAutomorphismUnit
public import WeilConjectures.AlgebraicGeometry.CompactSupportFixedBaseAction
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection

/-!
# Translation family on the vector-bundle trace line

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1 (blueprint:
lem-pur-vector-translation-trace-unit-family).

The module constructs the canonical self-product translation from the direct-sum
symmetric-algebra map `(v,w) ↦ (v,w-v)`.  Its compact-support action is the
published Cartesian exchange followed by the canonical Tate/shift comparison.
The theorem then records the degree-zero multiplication equation and its
zero-section normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The linear map on `M ⊞ M` sending `(v,w)` to `(v,w-v)`.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, the translation
automorphism `τ(v,w)=(v,w-v)` (blueprint: lem-pur-vector-translation-trace-unit-family). -/
def vectorTranslationLinearMap (S : Scheme.{u}) (M : S.Modules) :
    VectorTraceGeometry.sum S M M ⟶ VectorTraceGeometry.sum S M M :=
  biprod.lift (biprod.fst : VectorTraceGeometry.sum S M M ⟶ M)
    (-(biprod.fst : VectorTraceGeometry.sum S M M ⟶ M) + biprod.snd)

/-- The inverse linear map on `M ⊞ M`, sending `(v,w)` to `(v,w+v)`.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, the inverse of the
translation automorphism (blueprint: lem-pur-vector-translation-trace-unit-family). -/
def vectorTranslationLinearMapInv (S : Scheme.{u}) (M : S.Modules) :
    VectorTraceGeometry.sum S M M ⟶ VectorTraceGeometry.sum S M M :=
  biprod.lift (biprod.fst : VectorTraceGeometry.sum S M M ⟶ M)
    ((biprod.fst : VectorTraceGeometry.sum S M M ⟶ M) + biprod.snd)

/-- The canonical translation map on the pulled-back vector bundle.

It is conjugated from the displayed direct-sum linear map by the canonical
`VectorTraceGeometry.sumIso`; therefore its coordinates are exactly
`(v,w) ↦ (v,w-v)`: the bundle map is contravariant in the generators, and on points
`(w,v)` (fibre `w` from the first summand, base `v` from the second) it sends
`(w,v)` to `(w-v,v)`.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, the translation automorphism
(blueprint: lem-pur-vector-translation-trace-unit-family). -/
def vectorTranslationHom (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    VectorBundleZeroSection.scheme
        (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) ⟶
      VectorBundleZeroSection.scheme
        (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) :=
  let e := VectorTraceGeometry.sumIso S d d M M
  e.hom ≫
    WeilConjectures.PurityFiniteSetting.purityBundleMap S (d + d) (d + d)
      (VectorTraceGeometry.sum S M M) (VectorTraceGeometry.sum S M M)
      (vectorTranslationLinearMap S M) ≫ e.inv

/-- The inverse of `vectorTranslationHom` is obtained from the plus map.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, the translation
automorphism (blueprint: lem-pur-vector-translation-trace-unit-family). -/
def vectorTranslationHomInv (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    VectorBundleZeroSection.scheme
        (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) ⟶
      VectorBundleZeroSection.scheme
        (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) :=
  let e := VectorTraceGeometry.sumIso S d d M M
  e.hom ≫
    WeilConjectures.PurityFiniteSetting.purityBundleMap S (d + d) (d + d)
      (VectorTraceGeometry.sum S M M) (VectorTraceGeometry.sum S M M)
      (vectorTranslationLinearMapInv S M) ≫ e.inv

/-- The translation is invertible.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, "the automorphism τ"
(blueprint: lem-pur-vector-translation-trace-unit-family).
Proof: `vectorTranslationHomInv` is a two-sided inverse, because the plus and minus
linear maps compose to the identity of `M ⊞ M` and `purityBundleMap` is functorial. -/
theorem vectorTranslationHom_isIso (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    IsIso (vectorTranslationHom S d M) := by
  let j : VectorTraceGeometry.sum S M M ≅ VectorTraceGeometry.sum S M M :=
    { hom := vectorTranslationLinearMap S M
      inv := vectorTranslationLinearMapInv S M
      hom_inv_id := by
        apply biprod.hom_ext <;>
          simp [vectorTranslationLinearMap, vectorTranslationLinearMapInv,
            Preadditive.comp_add, Category.assoc]
      inv_hom_id := by
        apply biprod.hom_ext <;>
          simp [vectorTranslationLinearMap, vectorTranslationLinearMapInv,
            Preadditive.comp_add, Category.assoc] }
  let a := WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap
    S (VectorTraceGeometry.sum S M M) (VectorTraceGeometry.sum S M M) j.hom
  have : IsIso a := ⟨⟨WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap
    S (VectorTraceGeometry.sum S M M) (VectorTraceGeometry.sum S M M) j.inv,
    VectorTraceGeometry.symmetricMap_inverse S _ _ j,
    VectorTraceGeometry.symmetricMap_inverse S _ _ j.symm⟩⟩
  let b := ObjectProperty.homMk
    (X := VectorBundleZeroSection.algebraObject S (d + d) (VectorTraceGeometry.sum S M M))
    (Y := VectorBundleZeroSection.algebraObject S (d + d) (VectorTraceGeometry.sum S M M)) a
  have : IsIso b := (ObjectProperty.isIso_hom_iff b).mp ‹IsIso a›
  have : IsIso (WeilConjectures.PurityFiniteSetting.purityBundleMap S (d + d) (d + d)
      (VectorTraceGeometry.sum S M M) (VectorTraceGeometry.sum S M M)
      (vectorTranslationLinearMap S M)) := by
    change IsIso ((ObjectProperty.ι _ ⋙ Over.forget S).map
      ((VectorBundleZeroSection.antiEquivalence S).inverse.map b).unop)
    infer_instance
  dsimp only [vectorTranslationHom]
  infer_instance

/-- The canonical automorphism `τ(v,w)=(v,w-v)` of the self-product bundle.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1
(blueprint: lem-pur-vector-translation-trace-unit-family). -/
def vectorTranslation (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    VectorBundleZeroSection.scheme
        (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) ≅
      VectorBundleZeroSection.scheme
        (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) := by
  letI := vectorTranslationHom_isIso S d M
  exact asIso (vectorTranslationHom S d M)

/-- The translation is over the first projection.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, "τ of V×_S V over the first
factor" (blueprint: lem-pur-vector-translation-trace-unit-family).
Proof: the minus map is the identity on the second (base) summand, so composing with
`sumIso` and the base projection of `existsUnique_sumIso` gives the base projection. -/
theorem vectorTranslation_over (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    (vectorTranslation S d M).hom ≫ VectorBundleZeroSection.π
        (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) =
      VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) := by
  let H := VectorTraceGeometry.sum S M M
  let P := VectorBundleZeroSection.π S (d + d) H
  let j := vectorTranslationLinearMap S M
  let m := WeilConjectures.PurityFiniteSetting.purityBundleMap S (d + d) (d + d) H H j
  let q := VectorTraceGeometry.second S d d M M
  have hm : m ≫ P = P := VectorTraceGeometry.purityBundleMap_comm _ _ _ _ _ _
  have hq : q ≫ VectorBundleZeroSection.π S d M = P :=
    VectorTraceGeometry.purityBundleMap_comm _ _ _ _ _ _
  have hj : (biprod.inr : M ⟶ H) ≫ j = biprod.inr := by
    apply biprod.hom_ext <;> simp [j, vectorTranslationLinearMap, Category.assoc]
  have hmq : m ≫ q = q := by
    apply VectorTraceGeometry.bundle_hom_ext d M P _ _
      (by rw [Category.assoc, hq, hm]) hq
    have hml := VectorTraceGeometry.bundleLinear_purityBundleMap (d + d) (d + d)
      H H j P (𝟙 _) (Category.id_comp P)
    have hql := VectorTraceGeometry.bundleLinear_purityBundleMap (d + d) d
      H M biprod.inr P (𝟙 _) (Category.id_comp P)
    simp only [Category.id_comp] at hml hql
    dsimp only [q, VectorTraceGeometry.second]
    erw [VectorTraceGeometry.bundleLinear_purityBundleMap (d + d) d
      H M biprod.inr P m hm, hml, ← Category.assoc, hj, ← hql]
  let e := VectorTraceGeometry.sumIso S d d M M
  have he : e.hom ≫ q = VectorBundleZeroSection.π
      (VectorBundleZeroSection.scheme S d M) d
      ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) :=
    (VectorTraceGeometry.existsUnique_sumIso S d d M M).exists.choose_spec.2
  change (e.hom ≫ m ≫ e.inv) ≫ _ = _
  rw [← he]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, hmq]

/-- The Cartesian square `(τ,p₁,p₁,1_V)` used for compact-support finite-torsion exchange.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1
(blueprint: lem-pur-vector-translation-trace-unit-family).
Proof: `τ` is an isomorphism over `V` (`vectorTranslation_over`), and a square with two
parallel isomorphisms is Cartesian (`IsPullback.of_horiz_isIso`). -/
theorem vectorTranslationSquare (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    IsPullback (vectorTranslation S d M).hom
      (VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M))
      (VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback
          (VectorBundleZeroSection.π S d M)).obj M)) (𝟙 _) := by
  let _ := vectorTranslationHom_isIso S d M
  exact IsPullback.of_horiz_isIso ⟨by
    simpa only [Category.comp_id] using vectorTranslation_over S d M⟩

private theorem vectorTranslation_zero_square (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    let V := VectorBundleZeroSection.scheme S d M
    let p := VectorBundleZeroSection.π S d M
    let G := (Scheme.Modules.tensorPullback p).obj M
    let q := VectorBundleZeroSection.π V d G
    ∃ v : V ⟶ VectorBundleZeroSection.scheme V d G,
      IsPullback v p q (VectorBundleZeroSection.zero S d M) ∧
        v ≫ (vectorTranslation S d M).hom = v := by
  let V := VectorBundleZeroSection.scheme S d M
  let p := VectorBundleZeroSection.π S d M
  let G := (Scheme.Modules.tensorPullback p).obj M
  let q := VectorBundleZeroSection.π V d G
  let z := VectorBundleZeroSection.zero S d M
  let H := VectorTraceGeometry.sum S M M
  let P := VectorBundleZeroSection.π S (d + d) H
  let bc := VectorTraceGeometry.baseChange p d M
  let sq := VectorTraceGeometry.baseChange_isPullback p d M
  have hz : z ≫ p = 𝟙 S := (VectorBundleZeroSection.zero_spec S d M).1
  let v := sq.lift (𝟙 V) (p ≫ z) (by
    change (𝟙 V) ≫ p = (p ≫ z) ≫ p
    rw [Category.id_comp, Category.assoc, hz, Category.comp_id])
  have hv₁ : v ≫ bc = 𝟙 V := sq.lift_fst _ _ _
  have hv₂ : v ≫ q = p ≫ z := sq.lift_snd _ _ _
  have hs : IsPullback v p q z := by
    apply IsPullback.of_right (h₁₂ := bc) (h₂₂ := p) ?_ hv₂ sq
    simpa only [hv₁, hz] using (IsPullback.id_horiz p)
  refine ⟨v, hs, ?_⟩
  let e := VectorTraceGeometry.sumIso S d d M M
  let l := v ≫ e.hom
  let j := vectorTranslationLinearMap S M
  let m := WeilConjectures.PurityFiniteSetting.purityBundleMap
    S (d + d) (d + d) H H j
  have he₁ : e.hom ≫ VectorTraceGeometry.first S d d M M = bc :=
    (VectorTraceGeometry.existsUnique_sumIso S d d M M).exists.choose_spec.1
  have he₂ : e.hom ≫ VectorTraceGeometry.second S d d M M = q :=
    (VectorTraceGeometry.existsUnique_sumIso S d d M M).exists.choose_spec.2
  have hl₁ : l ≫ VectorTraceGeometry.first S d d M M = 𝟙 V := by
    dsimp only [l]
    rw [Category.assoc, he₁, hv₁]
  have hl₂ : l ≫ VectorTraceGeometry.second S d d M M = p ≫ z := by
    dsimp only [l]
    rw [Category.assoc, he₂, hv₂]
  have hf : VectorTraceGeometry.first S d d M M ≫ p = P :=
    VectorTraceGeometry.purityBundleMap_comm S (d + d) d H M biprod.inl
  have hl : l ≫ P = p := by
    calc
      l ≫ P = l ≫ (VectorTraceGeometry.first S d d M M ≫ p) :=
        congrArg (fun k ↦ l ≫ k) hf.symm
      _ = (l ≫ VectorTraceGeometry.first S d d M M) ≫ p := (Category.assoc _ _ _).symm
      _ = p := by rw [hl₁, Category.id_comp]
  have hzero : (biprod.inr : M ⟶ H) ≫
      VectorTraceGeometry.bundleLinear (d + d) H p l hl = 0 := by
    rw [← VectorTraceGeometry.bundleLinear_purityBundleMap (d + d) d H M
      biprod.inr p l hl]
    have hc := VectorTraceGeometry.bundleLinear_congr d M p
      (l ≫ VectorTraceGeometry.second S d d M M) (p ≫ z)
      (by rw [Category.assoc, VectorTraceGeometry.second,
        VectorTraceGeometry.purityBundleMap_comm, hl])
      (by rw [Category.assoc, hz, Category.comp_id]) hl₂
    exact hc.trans (VectorTraceGeometry.bundleLinear_zero d M p)
  have hm : l ≫ m = l := by
    apply VectorTraceGeometry.bundle_hom_ext (d + d) H p _ _
      (by rw [Category.assoc, VectorTraceGeometry.purityBundleMap_comm, hl]) hl
    rw [VectorTraceGeometry.bundleLinear_purityBundleMap (d + d) (d + d) H H j p l hl]
    apply biprod.hom_ext' <;>
      simp [j, vectorTranslationLinearMap, biprod.lift_eq, Preadditive.add_comp,
        Category.assoc, hzero]
  change v ≫ (e.hom ≫ m ≫ e.inv) = v
  rw [← Category.assoc, ← Category.assoc, hm, Category.assoc, e.hom_inv_id,
    Category.comp_id]

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

/-- The canonical Tate/shift identification `τ^*A_W(d)[2d] ≅ A_W(d)[2d]`: the coefficient
is the pullback of the base line along `p₁`, and `τ ≫ p₁ = p₁` gives the composition
isomorphism of derived inverse images.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1
(blueprint: lem-pur-vector-translation-trace-unit-family). -/
def vectorTranslationCoefficientIso (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (d : ℕ) (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    (ordinaryFinitePullback A (vectorTranslation S d M).hom).obj
        (vectorIntegrationCoefficient A N hA
          (VectorBundleZeroSection.scheme S d M) d
          ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M)) ≅
      vectorIntegrationCoefficient A N hA
        (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) := by
  let V := VectorBundleZeroSection.scheme S d M
  let p := VectorBundleZeroSection.π S d M
  let G := (Scheme.Modules.tensorPullback p).obj M
  dsimp only [vectorIntegrationCoefficient, ordinaryFinitePullback, Functor.comp_obj]
  exact ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (vectorTranslation S d M).hom (VectorBundleZeroSection.π V d G)
      (VectorBundleZeroSection.π V d G) (vectorTranslation_over S d M).symm).symm.app
      (affineLinearBaseCoefficient A N hA V d))

/-- The compact-support exchange for the canonical translation square.

The first comparison is the identity-base pullback comparison, the middle map is the
finite-torsion Cartesian exchange for `(τ,p₁,p₁,1_V)`, and the final map is the
canonical coefficient Tate/shift identification.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, "its effect on the top compactly supported
direct image" (blueprint: lem-pur-vector-translation-trace-unit-family). -/
def vectorTranslationTraceExchange (N : ℕ) (_hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (_hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    vectorIntegrationSource A N hA (VectorBundleZeroSection.scheme S d M) d
      ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) ⟶
    vectorIntegrationSource A N hA (VectorBundleZeroSection.scheme S d M) d
      ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) := by
  let V := VectorBundleZeroSection.scheme S d M
  let p := VectorBundleZeroSection.π S d M
  let G := (Scheme.Modules.tensorPullback p).obj M
  let K := vectorIntegrationCoefficient A N hA V d G
  letI : IsNoetherian V := (vectorIntegration_geometry S d M).2.2
  letI := isIso_rightDerivedLowerShriekBaseChangeMap A (vectorTranslationSquare S d M)
  exact (affineLinearPullbackId A V).inv.app
      (vectorIntegrationSource A N hA V d G) ≫
    (rightDerivedLowerShriekBaseChangeMap A (vectorTranslationSquare S d M)).app K ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (VectorBundleZeroSection.π V d G)).map
      (vectorTranslationCoefficientIso A N hA S d M).hom


/-- The degree-zero action obtained by the canonical integration transport:
`H^0(t)⁻¹ ≫ H^0(ρ_τ) ≫ H^0(t)`, with `ρ_τ = vectorTranslationTraceExchange` and the
canonical identification of `H^0` of a single complex, as an automorphism of the
constant trace line `A_V`.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, "identified with the constant sheaf
by integration"
(blueprint: lem-pur-vector-translation-trace-unit-family). -/
def vectorTranslationDegreeZeroAutomorphism (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    constantTraceLine (VectorBundleZeroSection.scheme S d M) A ≅
      constantTraceLine (VectorBundleZeroSection.scheme S d M) A := by
  let V := VectorBundleZeroSection.scheme S d M
  let p := VectorBundleZeroSection.π S d M
  let G := (Scheme.Modules.tensorPullback p).obj M
  letI : IsNoetherian V := (vectorIntegration_geometry S d M).2.2
  letI : G.IsFiniteLocallyFreeOfRank d :=
    AlgebraicGeometry.VectorTraceGeometry.tensorPullbackRank p d M
  let t := vectorBundleIntegration N hN A hA V
    (by simpa only [map_natCast] using hS.map p.appTop.hom) d G
  letI : IsIso t := (vectorBundleIntegration_concentration_and_isIso N hN A hA V
    (by simpa only [map_natCast] using hS.map p.appTop.hom) d G).2
  let e := asIso ((_root_.DerivedCategory.homologyFunctor _ 0).map t) ≪≫
    (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app
      (ordinaryFiniteConstant A V)
  let K := vectorIntegrationCoefficient A N hA V d G
  letI : IsIso ((affineLinearPullbackId A V).inv.app
      (vectorIntegrationSource A N hA V d G)) := by infer_instance
  letI := isIso_rightDerivedLowerShriekBaseChangeMap A (vectorTranslationSquare S d M)
  letI : IsIso ((rightDerivedLowerShriekBaseChangeMap A
      (vectorTranslationSquare S d M)).app K) := by infer_instance
  letI : IsIso ((rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (VectorBundleZeroSection.π V d G)).map
      (vectorTranslationCoefficientIso A N hA S d M).hom) := by infer_instance
  letI : IsIso (vectorTranslationTraceExchange N hN A hA S hS d M) := by
    dsimp [vectorTranslationTraceExchange]
    infer_instance
  letI : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      (vectorTranslationTraceExchange N hN A hA S hS d M)) := by infer_instance
  exact e.symm ≪≫
    asIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      (vectorTranslationTraceExchange N hN A hA S hS d M)) ≪≫ e

private theorem pullback_homology_conjugate_eq_id
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : Y ⟶ X)
    {K : DerivedCategoryModule A X}
    {L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (e : (_root_.DerivedCategory.homologyFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj K ≅ L)
    (r : K ⟶ K) (hr : (ordinaryFinitePullback A g).map r = 𝟙 _) :
    (upperStar (ModuleCat.{u + 1} A) g).map
      (e.inv ≫ (_root_.DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).map r ≫ e.hom) = 𝟙 _ := by
  let H := _root_.DerivedCategory.homologyFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) 0
  let H' := _root_.DerivedCategory.homologyFunctor
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) 0
  let c : (upperStar (ModuleCat.{u + 1} A) g).obj (H.obj K) ≅
      H'.obj ((ordinaryFinitePullback A g).obj K) :=
    (leftDerivedUpperStarHomologyFunctorIso.{u + 2, u}
      (ModuleCat.{u + 1} A) g 0).app K
  have hn : (upperStar (ModuleCat.{u + 1} A) g).map (H.map r) ≫ c.hom =
      c.hom ≫ H'.map ((ordinaryFinitePullback A g).map r) :=
    (leftDerivedUpperStarHomologyFunctorIso.{u + 2, u}
      (ModuleCat.{u + 1} A) g 0).hom.naturality r
  rw [hr, CategoryTheory.Functor.map_id, Category.comp_id] at hn
  have hh : (upperStar (ModuleCat.{u + 1} A) g).map (H.map r) = 𝟙 _ := by
    apply (cancel_mono c.hom).mp
    simpa only [Category.id_comp] using hn
  change (upperStar (ModuleCat.{u + 1} A) g).map (e.inv ≫ H.map r ≫ e.hom) = 𝟙 _
  rw [Functor.map_comp, Functor.map_comp, hh, Category.id_comp,
    ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]

private theorem vectorTranslationTraceExchange_zero
    (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).map
      (vectorTranslationTraceExchange N hN A hA S hS d M) = 𝟙 _ := by
  let V := VectorBundleZeroSection.scheme S d M
  let p := VectorBundleZeroSection.π S d M
  let G := (Scheme.Modules.tensorPullback p).obj M
  let : IsNoetherian V := (vectorIntegration_geometry S d M).2.2
  let : G.IsFiniteLocallyFreeOfRank d := VectorTraceGeometry.tensorPullbackRank p d M
  let W := VectorBundleZeroSection.scheme V d G
  let : IsNoetherian W := (vectorIntegration_geometry V d G).2.2
  obtain ⟨v, sq, hv⟩ := vectorTranslation_zero_square S d M
  simpa only [id_eq, Functor.id_obj, V, vectorTranslationTraceExchange,
    vectorTranslationCoefficientIso,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, vectorIntegrationCoefficient,
    vectorIntegrationSource] using
    compactSupport_fixed_base_action A sq (vectorTranslation S d M).hom
      (vectorTranslationSquare S d M) (vectorTranslation_over S d M) hv
      (affineLinearBaseCoefficient A N hA V d)

end AlgebraicGeometry.Etale
