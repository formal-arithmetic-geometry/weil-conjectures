/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups N3, U4 and S2
-/
module

public import Sheaf.Paper.CechCupResolutionComparisonData
public import Sheaf.Paper.CechCupProduct
import Sheaf.Paper.CupCechTotalCochainPairing

/-! # The augmentation axis of the signed total Cech pairing

Source: Stacks Project, Tags 07MB and 0FKV.
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

open scoped TensorProduct
open HomologicalComplex

private theorem axis_descend_bilinear {k : Type v} [CommRing k]
    (S₁ S₂ : ShortComplex (ModuleCat.{v} k)) (M : ModuleCat.{v} k)
    (c : S₁.cycles →ₗ[k] S₂.cycles →ₗ[k] M)
    (h₁ : ∀ x b, c (S₁.toCycles x) b = 0)
    (h₂ : ∀ a y, c a (S₂.toCycles y) = 0) :
    ∃ d : S₁.homology →ₗ[k] S₂.homology →ₗ[k] M,
      ∀ a b, d (S₁.homologyπ a) (S₂.homologyπ b) = c a b := by
  classical
  let t : S₁.homology →ₗ[k] S₂.cycles →ₗ[k] M :=
    (S₁.descHomology (ModuleCat.ofHom c) (by
      ext x b
      exact h₁ x b)).hom
  have ht (a : S₁.cycles) : t (S₁.homologyπ a) = c a :=
    congrArg (fun f ↦ f a) (S₁.π_descHomology (ModuleCat.ofHom c) _)
  have hπ₁ : Function.Surjective S₁.homologyπ :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hπ₂ : Function.Surjective S₂.homologyπ :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have ht₂ (a : S₁.homology) : S₂.toCycles ≫ ModuleCat.ofHom (t a) = 0 := by
    obtain ⟨a, rfl⟩ := hπ₁ a
    ext y
    change t (S₁.homologyπ a) (S₂.toCycles y) = 0
    rw [ht]
    exact h₂ a y
  let g (a : S₁.homology) : S₂.homology →ₗ[k] M :=
    (S₂.descHomology (ModuleCat.ofHom (t a)) (ht₂ a)).hom
  have hg (a : S₁.homology) (b : S₂.cycles) : g a (S₂.homologyπ b) = t a b :=
    congrArg (fun f ↦ f b) (S₂.π_descHomology (ModuleCat.ofHom (t a)) (ht₂ a))
  let d : S₁.homology →ₗ[k] S₂.homology →ₗ[k] M :=
    { toFun := g
      map_add' := by
        intro a a'
        ext b
        obtain ⟨b, rfl⟩ := hπ₂ b
        simp only [hg, map_add, LinearMap.add_apply]
      map_smul' := by
        intro r a
        ext b
        obtain ⟨b, rfl⟩ := hπ₂ b
        simp only [LinearMap.smul_apply, RingHom.id_apply, hg]
        exact congrArg (fun f ↦ f b) (t.map_smul r a) }
  exact ⟨d, fun a b ↦ by change g _ _ = _; rw [hg, ht]⟩

private theorem axis_tensor_cycles_lift {k : Type v} [CommRing k]
    (A B : CochainComplex (ModuleCat.{v} k) ℕ) (n : ℕ)
    (s : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (a : A.cycles s.1.1) (b : B.cycles s.1.2) :
    ∃ z : (mapBifunctor A B (curriedTensor (ModuleCat.{v} k))
        (ComplexShape.up ℕ)).cycles n,
      (mapBifunctor A B (curriedTensor (ModuleCat.{v} k))
        (ComplexShape.up ℕ)).iCycles n z =
      ιMapBifunctor A B (curriedTensor (ModuleCat.{v} k)) (ComplexShape.up ℕ)
        s.1.1 s.1.2 n s.2 ((A.iCycles s.1.1 a) ⊗ₜ[k] (B.iCycles s.1.2 b)) := by
  let T := mapBifunctor A B (curriedTensor (ModuleCat.{v} k)) (ComplexShape.up ℕ)
  let x := ιMapBifunctor A B (curriedTensor (ModuleCat.{v} k)) (ComplexShape.up ℕ)
    s.1.1 s.1.2 n s.2 ((A.iCycles s.1.1 a) ⊗ₜ[k] (B.iCycles s.1.2 b))
  have ha : A.d s.1.1 (s.1.1 + 1) (A.iCycles s.1.1 a) = 0 :=
    congrArg (fun f ↦ f a) (A.iCycles_d s.1.1 (s.1.1 + 1))
  have hb : B.d s.1.2 (s.1.2 + 1) (B.iCycles s.1.2 b) = 0 :=
    congrArg (fun f ↦ f b) (B.iCycles_d s.1.2 (s.1.2 + 1))
  have hx : T.d n (n + 1) x = 0 := by
    dsimp only [T, x]
    rw [mapBifunctor.d_eq]
    change ((ιMapBifunctor A B (curriedTensor (ModuleCat.{v} k))
      (ComplexShape.up ℕ) s.1.1 s.1.2 n s.2 ≫
      (mapBifunctor.D₁ A B (curriedTensor (ModuleCat.{v} k)) (ComplexShape.up ℕ) n (n + 1) +
       mapBifunctor.D₂ A B (curriedTensor (ModuleCat.{v} k)) (ComplexShape.up ℕ) n (n + 1)))
      ((A.iCycles s.1.1 a) ⊗ₜ[k] (B.iCycles s.1.2 b))) = 0
    rw [Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
    rw [mapBifunctor.d₁_eq' A B _ _
        (show (ComplexShape.up ℕ).Rel s.1.1 (s.1.1 + 1) by rfl),
      mapBifunctor.d₂_eq' A B _ _ s.1.1
        (show (ComplexShape.up ℕ).Rel s.1.2 (s.1.2 + 1) by rfl)]
    simp [curriedTensor, ha, hb]
  have hx' : ((forget₂ (ModuleCat k) Ab).map (T.sc n).g) x = 0 := by
    change T.d n ((ComplexShape.up ℕ).next n) x = 0
    rwa [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) by rfl)]
  refine ⟨(T.sc n).cyclesMk x hx', ?_⟩
  exact (T.sc n).i_cyclesMk x hx'

private theorem axis_tensor_homology_pairing {k : Type v} [CommRing k]
    (A B : CochainComplex (ModuleCat.{v} k) ℕ) (p q n : ℕ) (hpq : p + q = n) :
    ∃ c : A.homology p →ₗ[k] B.homology q →ₗ[k]
        (mapBifunctor A B (curriedTensor (ModuleCat.{v} k))
          (ComplexShape.up ℕ)).homology n,
      ∀ (a : A.cycles p) (b : B.cycles q),
        ∃ z : (mapBifunctor A B (curriedTensor (ModuleCat.{v} k))
          (ComplexShape.up ℕ)).cycles n,
        (mapBifunctor A B (curriedTensor (ModuleCat.{v} k))
          (ComplexShape.up ℕ)).iCycles n z =
          ιMapBifunctor A B (curriedTensor (ModuleCat.{v} k)) (ComplexShape.up ℕ)
            p q n hpq ((A.iCycles p a) ⊗ₜ[k] (B.iCycles q b)) ∧
        c (A.homologyπ p a) (B.homologyπ q b) =
          (mapBifunctor A B (curriedTensor (ModuleCat.{v} k))
            (ComplexShape.up ℕ)).homologyπ n z := by
  classical
  let T := mapBifunctor A B (curriedTensor (ModuleCat.{v} k)) (ComplexShape.up ℕ)
  let I : A.cycles p ⊗ B.cycles q ⟶ T.X n :=
    (A.iCycles p ⊗ₘ B.iCycles q) ≫
      ιMapBifunctor A B (curriedTensor (ModuleCat.{v} k)) (ComplexShape.up ℕ) p q n hpq
  have hI : I ≫ T.d n (n + 1) = 0 := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a b
    obtain ⟨z, hz⟩ := axis_tensor_cycles_lift A B n ⟨(p, q), hpq⟩ a b
    change T.d n (n + 1)
      (ιMapBifunctor A B (curriedTensor (ModuleCat.{v} k)) (ComplexShape.up ℕ)
        p q n hpq ((A.iCycles p a) ⊗ₜ[k] (B.iCycles q b))) = 0
    rw [← hz]
    exact congrArg (fun f ↦ f z) (T.iCycles_d n (n + 1))
  let t : A.cycles p ⊗ B.cycles q ⟶ T.cycles n :=
    T.liftCycles I (n + 1) ((ComplexShape.up ℕ).next_eq' rfl) hI
  have ht : t ≫ T.iCycles n = I := T.liftCycles_i _ _ _ _
  let c₀ : A.cycles p →ₗ[k] B.cycles q →ₗ[k] T.homology n :=
    TensorProduct.curry (t ≫ T.homologyπ n).hom
  have h₁ : ∀ x b, c₀ ((A.sc p).toCycles x) b = 0 := by
    intro x b
    by_cases hp : p = 0
    · subst p
      have hz : (A.sc 0).toCycles = 0 := by
        apply (cancel_mono (A.sc 0).iCycles).mp
        rw [ShortComplex.toCycles_i]
        change A.d ((ComplexShape.up ℕ).prev 0) 0 = 0 ≫ A.iCycles 0
        rw [A.shape _ _ (by intro h; change _ + 1 = 0 at h; omega), zero_comp]
      rw [hz]
      change c₀ 0 b = 0
      rw [map_zero, LinearMap.zero_apply]
    have hp' : 0 < p := Nat.pos_of_ne_zero hp
    let r := (ComplexShape.up ℕ).prev p
    have hr : r + 1 = p := by
      dsimp only [r]
      rw [(ComplexShape.up ℕ).prev_eq' (show
        (ComplexShape.up ℕ).Rel (p - 1) p by change p - 1 + 1 = p; omega)]
      omega
    let w := ιMapBifunctor A B (curriedTensor (ModuleCat.{v} k)) (ComplexShape.up ℕ)
      r q (n - 1) (by change r + q = n - 1; omega)
      (x ⊗ₜ[k] (B.iCycles q b))
    have hw : T.d (n - 1) n w = I (((A.sc p).toCycles x) ⊗ₜ[k] b) := by
      have hb : B.d q (q + 1) (B.iCycles q b) = 0 :=
        congrArg (fun f ↦ f b) (B.iCycles_d q (q + 1))
      dsimp only [w, T]
      rw [mapBifunctor.d_eq]
      change ((ιMapBifunctor A B (curriedTensor (ModuleCat.{v} k))
        (ComplexShape.up ℕ) r q (n - 1) _ ≫
        (mapBifunctor.D₁ A B _ _ (n - 1) n +
         mapBifunctor.D₂ A B _ _ (n - 1) n)) (x ⊗ₜ[k] (B.iCycles q b))) = _
      rw [Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
        mapBifunctor.d₁_eq A B _ _ (show (ComplexShape.up ℕ).Rel r p from hr) q n hpq,
        mapBifunctor.d₂_eq' A B _ _ r
          (show (ComplexShape.up ℕ).Rel q (q + 1) by rfl)]
      have ha : A.iCycles p ((A.sc p).toCycles x) = A.d r p x :=
        congrArg (fun f ↦ f x) (A.sc p).toCycles_i
      simp [curriedTensor, hb, I, ha]
    have heq : t (((A.sc p).toCycles x) ⊗ₜ[k] b) = T.toCycles (n - 1) n w := by
      apply (ModuleCat.mono_iff_injective (T.iCycles n)).mp inferInstance
      have ht' := congrArg (fun f ↦ f (((A.sc p).toCycles x) ⊗ₜ[k] b)) ht
      have hw' := congrArg (fun f ↦ f w) (T.toCycles_i (n - 1) n)
      exact ht'.trans (hw.symm.trans hw'.symm)
    change T.homologyπ n (t (((A.sc p).toCycles x) ⊗ₜ[k] b)) = 0
    rw [heq]
    exact congrArg (fun f ↦ f w) (T.toCycles_comp_homologyπ (n - 1) n)
  have h₂ : ∀ a y, c₀ a ((B.sc q).toCycles y) = 0 := by
    intro a y
    by_cases hq : q = 0
    · subst q
      have hz : (B.sc 0).toCycles = 0 := by
        apply (cancel_mono (B.sc 0).iCycles).mp
        rw [ShortComplex.toCycles_i]
        change B.d ((ComplexShape.up ℕ).prev 0) 0 = 0 ≫ B.iCycles 0
        rw [B.shape _ _ (by intro h; change _ + 1 = 0 at h; omega), zero_comp]
      rw [hz]
      change c₀ a 0 = 0
      exact (c₀ a).map_zero
    have hq' : 0 < q := Nat.pos_of_ne_zero hq
    let r := (ComplexShape.up ℕ).prev q
    have hr : r + 1 = q := by
      dsimp only [r]
      rw [(ComplexShape.up ℕ).prev_eq' (show
        (ComplexShape.up ℕ).Rel (q - 1) q by change q - 1 + 1 = q; omega)]
      omega
    let ε := ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, r)
    let w := ιMapBifunctor A B (curriedTensor (ModuleCat.{v} k)) (ComplexShape.up ℕ)
      p r (n - 1) (by change p + r = n - 1; omega)
      ((A.iCycles p a) ⊗ₜ[k] y)
    have hw : T.d (n - 1) n w = ε • I (a ⊗ₜ[k] ((B.sc q).toCycles y)) := by
      have ha : A.d p (p + 1) (A.iCycles p a) = 0 :=
        congrArg (fun f ↦ f a) (A.iCycles_d p (p + 1))
      dsimp only [w, T]
      rw [mapBifunctor.d_eq]
      change ((ιMapBifunctor A B (curriedTensor (ModuleCat.{v} k))
        (ComplexShape.up ℕ) p r (n - 1) _ ≫
        (mapBifunctor.D₁ A B _ _ (n - 1) n +
         mapBifunctor.D₂ A B _ _ (n - 1) n)) ((A.iCycles p a) ⊗ₜ[k] y)) = _
      rw [Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
        mapBifunctor.d₁_eq' A B _ _
          (show (ComplexShape.up ℕ).Rel p (p + 1) by rfl),
        mapBifunctor.d₂_eq A B _ _ p
          (show (ComplexShape.up ℕ).Rel r q from hr) n hpq]
      have hb : B.iCycles q ((B.sc q).toCycles y) = B.d r q y :=
        congrArg (fun f ↦ f y) (B.sc q).toCycles_i
      simp [curriedTensor, ha, I, hb, ε]
    have heq : ε • t (a ⊗ₜ[k] ((B.sc q).toCycles y)) = T.toCycles (n - 1) n w := by
      apply (ModuleCat.mono_iff_injective (T.iCycles n)).mp inferInstance
      have ht' := congrArg (fun f ↦ f (a ⊗ₜ[k] ((B.sc q).toCycles y))) ht
      have hw' := congrArg (fun f ↦ f w) (T.toCycles_i (n - 1) n)
      change T.iCycles n (t (a ⊗ₜ[k] ((B.sc q).toCycles y))) =
        I (a ⊗ₜ[k] ((B.sc q).toCycles y)) at ht'
      rw [Units.smul_def, map_zsmul]
      rw [ht']
      exact hw.symm.trans hw'.symm
    have hz : ε • T.homologyπ n (t (a ⊗ₜ[k] ((B.sc q).toCycles y))) = 0 := by
      rw [Units.smul_def, ← map_zsmul, ← Units.smul_def, heq]
      exact congrArg (fun f ↦ f w) (T.toCycles_comp_homologyπ (n - 1) n)
    change T.homologyπ n (t (a ⊗ₜ[k] ((B.sc q).toCycles y))) = 0
    exact (smul_eq_zero_iff_eq ε).mp hz
  obtain ⟨c, hc⟩ := axis_descend_bilinear (A.sc p) (B.sc q) (T.homology n) c₀ h₁ h₂
  refine ⟨c, ?_⟩
  intro a b
  refine ⟨t (a ⊗ₜ[k] b), ?_, ?_⟩
  · exact congrArg (fun f ↦ f (a ⊗ₜ[k] b)) ht
  · change c ((A.sc p).homologyπ a) ((B.sc q).homologyπ b) =
      T.homologyπ n (t (a ⊗ₜ[k] b))
    exact hc a b


private theorem axis_pairing_from_map {k : Type v} [CommRing k]
    (A B C : CochainComplex (ModuleCat.{v} k) ℕ)
    (h : mapBifunctor A B (curriedTensor (ModuleCat.{v} k))
      (ComplexShape.up ℕ) ⟶ C) (p q : ℕ) :
    ∃ t : A.homology p →ₗ[k] B.homology q →ₗ[k] C.homology (p + q),
      ∀ (a : A.cycles p) (b : B.cycles q) (c : C.cycles (p + q)),
        C.iCycles (p + q) c = h.f (p + q)
          (ιMapBifunctor A B (curriedTensor (ModuleCat.{v} k))
            (ComplexShape.up ℕ) p q (p + q) rfl
            ((A.iCycles p a) ⊗ₜ[k] (B.iCycles q b))) →
        t (A.homologyπ p a) (B.homologyπ q b) = C.homologyπ (p + q) c := by
  obtain ⟨t, ht⟩ := axis_tensor_homology_pairing A B p q (p + q) rfl
  refine ⟨t.compr₂ (HomologicalComplex.homologyMap h (p + q)).hom, ?_⟩
  intro a b c hc
  obtain ⟨z, hz, ht⟩ := ht a b
  change HomologicalComplex.homologyMap h (p + q)
    (t (A.homologyπ p a) (B.homologyπ q b)) = _
  rw [ht]
  have he : HomologicalComplex.cyclesMap h (p + q) z = c := by
    apply (ModuleCat.mono_iff_injective (C.iCycles (p + q))).mp inferInstance
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
      ConcreteCategory.comp_apply, hz, hc]
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply, he]

private theorem axis_cycle_value {k : Type v} [CommRing k]
    (K : CochainComplex (ModuleCat.{v} k) ℕ) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    K.iCycles n ((K.sc n).moduleCatCyclesIso.inv a) = a.val :=
  congrArg (fun f ↦ f a) (K.sc n).moduleCatCyclesIso_inv_iCycles

private theorem axis_mapped_value {k : Type v} [CommRing k]
    {K L : CochainComplex (ModuleCat.{v} k) ℕ} (f : K ⟶ L) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    L.iCycles n (HomologicalComplex.cyclesMap f n ((K.sc n).moduleCatCyclesIso.inv a)) =
      f.f n a.val := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
    ConcreteCategory.comp_apply, axis_cycle_value]

private theorem axis_mapped_class {k : Type v} [CommRing k]
    {K L : CochainComplex (ModuleCat.{v} k) ℕ} (f : K ⟶ L) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    L.homologyπ n
        (HomologicalComplex.cyclesMap f n ((K.sc n).moduleCatCyclesIso.inv a)) =
      HomologicalComplex.homologyMap f n (cupCycleClass K n a) := by
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyπ_naturality]
  rfl

set_option maxHeartbeats 800000 in
-- The three total complexes involve nested functor and tensor coercions.
/-- The signed Alexander--Whitney pairing descends to total homology and
computes both axis products. Only the chain maps and their component formulas
are required; no comparison isomorphism or sheaf cohomology cup is used.
Source: Stacks Project, Tags 07MB and 0FKV, final comparison diagram.
(blueprint: lem-sc-cech-cup-signed-axis-pairing)

Proof: for summands of bidegrees (r,i) and (s,j), restrict the front and back
Cech sections to the common intersection, apply D.pair r s, and multiply by
(-1)^(i*s). Extend bilinearly over the finite sums in each total degree.
D.restriction identifies restrictions of products with products of restrictions.
The adjacent shared-face terms in the alternating Cech differential cancel;
the remaining faces give the two Cech Leibniz terms. D.leibniz gives the
resolution differential terms, and the sign (-1)^(i*s) matches the total
Leibniz sign (-1)^(r+i). Thus products of cycles are cycles and a product
with a boundary is a boundary, so the pairing descends through both homology
quotients. On alpha images the Cech degrees are zero and the summands are the
global resolution product. On beta images both resolution degrees are zero;
D.augmentation_pair identifies the product with the coefficient Cech product.
The six component equations therefore give the two displayed class formulas.
Empty families, zero complexes and zero inputs cause no exception: the finite
sum and quotient constructions still apply, with the corresponding maps zero. -/
private theorem betaPairing_signed_axis_pairing {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G)
    (lalpha : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K ⟶
      (cupCechDouble U D.left.K).total (ComplexShape.up ℕ))
    (lbeta : (cechComplexFunctor U).obj F.presheafModuleCat ⟶
      (cupCechDouble U D.left.K).total (ComplexShape.up ℕ))
    (hlalpha : ∀ n : ℕ, lalpha.f n = moduleCechZero U (D.left.K.X n) ≫
      (cupCechDouble U D.left.K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp))
    (hlbeta : ∀ n : ℕ, lbeta.f n =
      ((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (D.left.augmentation.f 0).val)).f n ≫
        (cupCechDouble U D.left.K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp))
    (ralpha : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K ⟶
      (cupCechDouble U D.right.K).total (ComplexShape.up ℕ))
    (rbeta : (cechComplexFunctor U).obj G.presheafModuleCat ⟶
      (cupCechDouble U D.right.K).total (ComplexShape.up ℕ))
    (hralpha : ∀ n : ℕ, ralpha.f n = moduleCechZero U (D.right.K.X n) ≫
      (cupCechDouble U D.right.K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp))
    (hrbeta : ∀ n : ℕ, rbeta.f n =
      ((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (D.right.augmentation.f 0).val)).f n ≫
        (cupCechDouble U D.right.K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp))
    (talpha : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K ⟶
      (cupCechDouble U D.target.K).total (ComplexShape.up ℕ))
    (tbeta : (cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat ⟶
      (cupCechDouble U D.target.K).total (ComplexShape.up ℕ))
    (htalpha : ∀ n : ℕ, talpha.f n = moduleCechZero U (D.target.K.X n) ≫
      (cupCechDouble U D.target.K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp))
    (htbeta : ∀ n : ℕ, tbeta.f n =
      ((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (D.target.augmentation.f 0).val)).f n ≫
        (cupCechDouble U D.target.K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp))
    (p q : ℕ) :
    ∃ t : ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ)).homology p →ₗ[Γ(X, ⊤)]
      ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ)).homology q →ₗ[Γ(X, ⊤)]
        ((cupCechDouble U D.target.K).total (ComplexShape.up ℕ)).homology (p + q),
      (∀ (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          t (HomologicalComplex.homologyMap lalpha p (cupCycleClass _ p a))
              (HomologicalComplex.homologyMap ralpha q (cupCycleClass _ q b)) =
            HomologicalComplex.homologyMap talpha (p + q) (cupCycleClass _ (p + q) c)) ∧
      (∀ (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc
          p).moduleCatLeftHomologyData.K)
        (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc
          q).moduleCatLeftHomologyData.K)
        (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
          (p + q)).moduleCatLeftHomologyData.K),
        c.val = cechCupCochain U F G p q a.val b.val →
          t (HomologicalComplex.homologyMap lbeta p (cupCycleClass _ p a))
              (HomologicalComplex.homologyMap rbeta q (cupCycleClass _ q b)) =
            HomologicalComplex.homologyMap tbeta (p + q) (cupCycleClass _ (p + q) c)) := by
  let : CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
    inferInstanceAs (CommRing Γ(X, ⊤))
  have hla : lalpha = cupCechAlpha U D.left := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact hlalpha n
  have hlb : lbeta = cupCechBeta U D.left := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact hlbeta n
  have hra : ralpha = cupCechAlpha U D.right := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact hralpha n
  have hrb : rbeta = cupCechBeta U D.right := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact hrbeta n
  have hta : talpha = cupCechAlpha U D.target := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact htalpha n
  have htb : tbeta = cupCechBeta U D.target := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact htbeta n
  obtain ⟨h, ha, hb⟩ := exists_cupCech_total_cochain_pairing U D
  obtain ⟨t, ht⟩ := axis_pairing_from_map _ _ _ h p q
  refine ⟨t, ?_, ?_⟩
  · intro a b c hc
    rw [← axis_mapped_class lalpha p a, ← axis_mapped_class ralpha q b,
      ← axis_mapped_class talpha (p + q) c]
    apply ht
    erw [axis_mapped_value lalpha p a, axis_mapped_value ralpha q b,
      axis_mapped_value talpha (p + q) c, hla, hra, hta, hc]
    exact (ha p q a.val b.val).symm
  · intro a b c hc
    rw [← axis_mapped_class lbeta p a, ← axis_mapped_class rbeta q b,
      ← axis_mapped_class tbeta (p + q) c]
    apply ht
    erw [axis_mapped_value lbeta p a, axis_mapped_value rbeta q b,
      axis_mapped_value tbeta (p + q) c, hlb, hrb, htb, hc]
    exact (hb p q a.val b.val).symm


private theorem betaPairing_cycleClass_surjective {R : Type v} [Ring R]
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    Function.Surjective (cupCycleClass K n) := by
  exact (ModuleCat.epi_iff_surjective
    ((K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ)).mp inferInstance

private theorem betaPairing_pair_exists_cycle {X : Scheme.{v}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (p q : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K) :
    ∃ c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K,
      c.val = D.pair p q ⊤ a.val b.val := by
  have ha := a.property
  have hb := b.property
  change (D.left.K.d p ((ComplexShape.up ℕ).next p)).val.app (op ⊤) a.val = 0 at ha
  change (D.right.K.d q ((ComplexShape.up ℕ).next q)).val.app (op ⊤) b.val = 0 at hb
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel p (p + 1))] at ha
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel q (q + 1))] at hb
  refine ⟨⟨D.pair p q ⊤ a.val b.val, ?_⟩, rfl⟩
  change (D.target.K.d (p + q) ((ComplexShape.up ℕ).next (p + q))).val.app (op ⊤)
    (D.pair p q ⊤ a.val b.val) = 0
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel (p + q) (p + q + 1))]
  rw [D.leibniz, ha, hb]
  simp

private theorem betaPairing_alpha_surjective {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F : X.Modules} {D : CupAcyclicResolution F}
    (A : CupCechResolutionComparison U D) (n : ℕ) :
    Function.Surjective (fun z ↦
      HomologicalComplex.homologyMap A.alpha n (cupCycleClass _ n z)) := by
  let := A.alpha_quasiIso
  exact ((ModuleCat.epi_iff_surjective
    (HomologicalComplex.homologyMap A.alpha n)).mp inferInstance).comp
      (betaPairing_cycleClass_surjective _ n)

/-- The augmentation axis computes the already characterized sheaf cup product.
Source: Stacks Project, Tag 07MB and Tag 0FKV, final comparison diagram.
(blueprint: lem-sc-cech-cup-resolution-beta-class-pairing)

Proof: form the signed Alexander--Whitney total pairing using D.pair on each
resolution/Cech summand, with sign (-1)^(i*s) for Cech degree i of the first
factor and resolution degree s of the second. Restriction compatibility and
D.leibniz give the cochain identity; the Cech differential cancels adjacent
omitted-vertex terms. Bilinearity and this identity give quotient descent to
homology. The alpha components lie in Cech degree zero, so their signs are one;
the resulting product is the D.pair product of global resolution cycles.
A.alpha_quasiIso and B.alpha_quasiIso let every total homology input be lifted
to a global resolution cycle. The alpha_class equations identify its class
with the inverse of A.iso or B.iso. The characterization hcup therefore
identifies the total pairing with cup transported along A.iso, B.iso, C.iso.
The beta components lie in resolution degree zero. Here the signs are also
one, and D.augmentation_pair identifies their product with the augmentation
of cechCupCochain. The beta_f equations identify these components with the
specified beta maps. Apply homology and then C.iso.inv to this beta equality.
This calculation is sectionwise and does not require a covering hypothesis:
the needed global comparison isomorphisms are explicitly part of A and B.
If an index set or an input is empty or zero, bilinearity gives the same formula.
The statement fixes cup by hcup, rather than asserting the formula for an
arbitrary bilinear map. -/
theorem cupCechResolution_beta_class_pairing {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G)
    (A : CupCechResolutionComparison U D.left)
    (B : CupCechResolutionComparison U D.right)
    (C : CupCechResolutionComparison U D.target) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
          (@id X.Modules (F ⊗ G)))
    (hcup : IsModuleCupProduct F G p q cup)
    (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc
      p).moduleCatLeftHomologyData.K)
    (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc
      q).moduleCatLeftHomologyData.K)
    (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
      (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = cechCupCochain U F G p q a.val b.val) :
    cup ((A.iso p).inv (HomologicalComplex.homologyMap A.beta p (cupCycleClass _ p a)))
      ((B.iso q).inv (HomologicalComplex.homologyMap B.beta q (cupCycleClass _ q b))) =
        (C.iso (p + q)).inv
          (HomologicalComplex.homologyMap C.beta (p + q) (cupCycleClass _ (p + q) c)) := by
  obtain ⟨t, halpha, hbeta⟩ := betaPairing_signed_axis_pairing U D
    A.alpha A.beta A.alpha_f A.beta_f
    B.alpha B.beta B.alpha_f B.beta_f
    C.alpha C.beta C.alpha_f C.beta_f p q
  obtain ⟨a', ha'⟩ := betaPairing_alpha_surjective U A p
    (HomologicalComplex.homologyMap A.beta p (cupCycleClass _ p a))
  obtain ⟨b', hb'⟩ := betaPairing_alpha_surjective U B q
    (HomologicalComplex.homologyMap B.beta q (cupCycleClass _ q b))
  dsimp only at ha' hb'
  obtain ⟨c', hc'⟩ := betaPairing_pair_exists_cycle D p q a' b'
  have ha : (A.iso p).inv
      (HomologicalComplex.homologyMap A.beta p (cupCycleClass _ p a)) =
      D.left.class p a' := by
    rw [← ha', ← A.alpha_class p a']
    simp only [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply]
  have hb : (B.iso q).inv
      (HomologicalComplex.homologyMap B.beta q (cupCycleClass _ q b)) =
      D.right.class q b' := by
    rw [← hb', ← B.alpha_class q b']
    simp only [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply]
  have ht := halpha a' b' c' hc'
  rw [ha', hb', hbeta a b c hc] at ht
  have ht' := congrArg (fun z ↦ (C.iso (p + q)).inv z) ht
  rw [← C.alpha_class (p + q) c'] at ht'
  simp only [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply] at ht'
  rw [ha, hb, hcup D a' b' c' hc']
  exact ht'.symm

end
end AlgebraicGeometry.Scheme.Modules
