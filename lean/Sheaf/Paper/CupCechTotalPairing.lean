/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups S3 and V3
-/
module

public import Sheaf.Paper.CupCechTotalComplex
public import Sheaf.Paper.CechCupProduct
import Sheaf.Paper.CupCechTotalCochainPairing
import all Sheaf.Algebra.Homology.TensorHomologyPairing

/-! # The two axes of the signed Cech total pairing

Source: Stacks Project, Tags 01EQ and 0FKV.
(blueprint: lem-sc-cup-cech-total-pairing)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct
open HomologicalComplex
noncomputable section

private theorem tensor_cycles_nat {k : Type u} [CommRing k]
    (A B : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ)
    (s : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (a : A.cycles s.1.1) (b : B.cycles s.1.2) :
    ∃ z : (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.up ℕ)).cycles n,
      (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.up ℕ)).iCycles n z =
      ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ)
        s.1.1 s.1.2 n s.2 ((A.iCycles s.1.1 a) ⊗ₜ[k] (B.iCycles s.1.2 b)) := by
  let T := mapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ)
  let x := ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ)
    s.1.1 s.1.2 n s.2 ((A.iCycles s.1.1 a) ⊗ₜ[k] (B.iCycles s.1.2 b))
  have ha : A.d s.1.1 (s.1.1 + 1) (A.iCycles s.1.1 a) = 0 :=
    congrArg (fun f ↦ f a) (A.iCycles_d s.1.1 (s.1.1 + 1))
  have hb : B.d s.1.2 (s.1.2 + 1) (B.iCycles s.1.2 b) = 0 :=
    congrArg (fun f ↦ f b) (B.iCycles_d s.1.2 (s.1.2 + 1))
  have hx : T.d n (n + 1) x = 0 := by
    dsimp only [T, x]
    rw [mapBifunctor.d_eq]
    change ((ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k))
      (ComplexShape.up ℕ) s.1.1 s.1.2 n s.2 ≫
      (mapBifunctor.D₁ A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ) n (n + 1) +
       mapBifunctor.D₂ A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ) n (n + 1)))
      ((A.iCycles s.1.1 a) ⊗ₜ[k] (B.iCycles s.1.2 b))) = 0
    rw [Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
    rw [mapBifunctor.d₁_eq' A B _ _ (show (ComplexShape.up ℕ).Rel s.1.1 (s.1.1 + 1) from rfl),
      mapBifunctor.d₂_eq' A B _ _ s.1.1
        (show (ComplexShape.up ℕ).Rel s.1.2 (s.1.2 + 1) from rfl)]
    simp [curriedTensor, ha, hb]
  have hx' : ((forget₂ (ModuleCat k) Ab).map (T.sc n).g) x = 0 := by
    change T.d n ((ComplexShape.up ℕ).next n) x = 0
    rwa [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)]
  refine ⟨(T.sc n).cyclesMk x hx', ?_⟩
  exact (T.sc n).i_cyclesMk x hx'

private theorem tensor_homology_nat {k : Type u} [CommRing k]
    (A B : CochainComplex (ModuleCat.{u} k) ℕ) (p q n : ℕ) (hpq : p + q = n) :
    ∃ c : A.homology p →ₗ[k] B.homology q →ₗ[k]
        (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
          (ComplexShape.up ℕ)).homology n,
      ∀ (a : A.cycles p) (b : B.cycles q),
        ∃ z : (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
          (ComplexShape.up ℕ)).cycles n,
        (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
          (ComplexShape.up ℕ)).iCycles n z =
          ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ)
            p q n hpq ((A.iCycles p a) ⊗ₜ[k] (B.iCycles q b)) ∧
        c (A.homologyπ p a) (B.homologyπ q b) =
          (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
            (ComplexShape.up ℕ)).homologyπ n z := by
  classical
  let T := mapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ)
  let I : A.cycles p ⊗ B.cycles q ⟶ T.X n :=
    (A.iCycles p ⊗ₘ B.iCycles q) ≫
      ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ) p q n hpq
  have hI : I ≫ T.d n (n + 1) = 0 := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a b
    obtain ⟨z, hz⟩ := tensor_cycles_nat A B n ⟨(p, q), hpq⟩ a b
    change T.d n (n + 1)
      (ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ)
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
        apply (cancel_mono (A.sc 0).iCycles).1
        rw [(A.sc 0).toCycles_i, zero_comp]
        exact A.shape _ _ (by simp)
      simp [hz, c₀]
    let r := (ComplexShape.up ℕ).prev p
    have hr : r + 1 = p := by
      dsimp only [r]
      rw [(ComplexShape.up ℕ).prev_eq' (show
        (ComplexShape.up ℕ).Rel (p - 1) p by change p - 1 + 1 = p; omega)]
      omega
    let w := ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ)
      r q (n - 1) (by change r + q = n - 1; omega)
      (x ⊗ₜ[k] (B.iCycles q b))
    have hw : T.d (n - 1) n w = I (((A.sc p).toCycles x) ⊗ₜ[k] b) := by
      have hb : B.d q (q + 1) (B.iCycles q b) = 0 :=
        congrArg (fun f ↦ f b) (B.iCycles_d q (q + 1))
      dsimp only [w, T]
      rw [mapBifunctor.d_eq]
      change ((ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.up ℕ) r q (n - 1) _ ≫
        (mapBifunctor.D₁ A B _ _ (n - 1) n +
         mapBifunctor.D₂ A B _ _ (n - 1) n)) (x ⊗ₜ[k] (B.iCycles q b))) = _
      rw [Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
        mapBifunctor.d₁_eq A B _ _ (show (ComplexShape.up ℕ).Rel r p from hr) q n hpq,
        mapBifunctor.d₂_eq' A B _ _ r
          (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl)]
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
        apply (cancel_mono (B.sc 0).iCycles).1
        rw [(B.sc 0).toCycles_i, zero_comp]
        exact B.shape _ _ (by simp)
      simp [hz, c₀]
    let r := (ComplexShape.up ℕ).prev q
    have hr : r + 1 = q := by
      dsimp only [r]
      rw [(ComplexShape.up ℕ).prev_eq' (show
        (ComplexShape.up ℕ).Rel (q - 1) q by change q - 1 + 1 = q; omega)]
      omega
    let ε := ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, r)
    let w := ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ)
      p r (n - 1) (by change p + r = n - 1; omega)
      ((A.iCycles p a) ⊗ₜ[k] y)
    have hw : T.d (n - 1) n w = ε • I (a ⊗ₜ[k] ((B.sc q).toCycles y)) := by
      have ha : A.d p (p + 1) (A.iCycles p a) = 0 :=
        congrArg (fun f ↦ f a) (A.iCycles_d p (p + 1))
      dsimp only [w, T]
      rw [mapBifunctor.d_eq]
      change ((ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.up ℕ) p r (n - 1) _ ≫
        (mapBifunctor.D₁ A B _ _ (n - 1) n +
         mapBifunctor.D₂ A B _ _ (n - 1) n)) ((A.iCycles p a) ⊗ₜ[k] y)) = _
      rw [Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
        mapBifunctor.d₁_eq' A B _ _
          (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl),
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
  obtain ⟨c, hc⟩ := descend_bilinear (A.sc p) (B.sc q) (T.homology n) c₀ h₁ h₂
  refine ⟨c, ?_⟩
  intro a b
  refine ⟨t (a ⊗ₜ[k] b), ?_, ?_⟩
  · exact congrArg (fun f ↦ f (a ⊗ₜ[k] b)) ht
  · change c ((A.sc p).homologyπ a) ((B.sc q).homologyπ b) =
      T.homologyπ n (t (a ⊗ₜ[k] b))
    exact hc a b

private theorem tensorMap_homology_pairing {R : Type u} [CommRing R]
    (A B C : CochainComplex (ModuleCat.{u} R) ℕ)
    (h : mapBifunctor A B (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℕ) ⟶ C)
    (p q : ℕ) :
    ∃ t : A.homology p →ₗ[R] B.homology q →ₗ[R] C.homology (p + q),
      ∀ (a : A.cycles p) (b : B.cycles q) (c : C.cycles (p + q)),
        C.iCycles (p + q) c = h.f (p + q)
          (ιMapBifunctor A B (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℕ)
            p q (p + q) rfl ((A.iCycles p a) ⊗ₜ[R] (B.iCycles q b))) →
        t (A.homologyπ p a) (B.homologyπ q b) = C.homologyπ (p + q) c := by
  obtain ⟨t, ht⟩ := tensor_homology_nat A B p q (p + q) rfl
  refine ⟨t.compr₂ (HomologicalComplex.homologyMap h (p + q)).hom, ?_⟩
  intro a b c hc
  obtain ⟨z, hz, hclass⟩ := ht a b
  change HomologicalComplex.homologyMap h (p + q)
    (t (A.homologyπ p a) (B.homologyπ q b)) = _
  rw [hclass]
  have hnat := ConcreteCategory.congr_hom (homologyπ_naturality h (p + q)) z
  simp only [ConcreteCategory.comp_apply] at hnat
  rw [hnat]
  congr 1
  apply (ModuleCat.mono_iff_injective (C.iCycles (p + q))).mp inferInstance
  exact (ConcreteCategory.congr_hom (cyclesMap_i h (p + q)) z).trans
    (by rw [ConcreteCategory.comp_apply, hz]; exact hc.symm)

private def cycleMap {R : Type u} [Ring R]
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) : L.cycles n :=
  cyclesMap f n ((K.sc n).moduleCatCyclesIso.inv a)

private theorem cycleMap_i {R : Type u} [Ring R]
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    L.iCycles n (cycleMap f n a) = f.f n a.val := by
  change L.iCycles n (cyclesMap f n ((K.sc n).moduleCatCyclesIso.inv a)) = _
  rw [← ConcreteCategory.comp_apply, cyclesMap_i]
  change f.f n ((K.iCycles n) ((K.sc n).moduleCatCyclesIso.inv a)) = _
  exact congrArg (f.f n)
    (ConcreteCategory.congr_hom (K.sc n).moduleCatCyclesIso_inv_iCycles a)

private theorem cycleMap_class {R : Type u} [Ring R]
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    HomologicalComplex.homologyMap f n (cupCycleClass K n a) =
      L.homologyπ n (cycleMap f n a) :=
  ConcreteCategory.congr_hom (homologyπ_naturality f n) ((K.sc n).moduleCatCyclesIso.inv a)

set_option maxHeartbeats 800000 in
-- Elaborating the three total complexes and their cycle transports needs extra heartbeats.
/-- The signed total pairing on homology preserves both the global-sections alpha
axis and the coefficient-augmentation beta axis. Neither a cover nor acyclicity
of the resolution terms is required for these two algebraic identities.
Source: Stacks Project, Tag 07MB and the flasque diagram of Tag 0FKV.
(blueprint: lem-sc-cup-cech-total-pairing)

Proof: obtain the signed total cochain map and its two axis formulas from
exists_cupCech_total_cochain_pairing. The private tensor_homology_nat proof
constructs the tensor product of cycles and descends its bilinear homology class
through the two boundary quotients. A tensor with a boundary is a boundary by
the tensor differential formula; in degree zero the incoming differential is
zero, so no negative-degree primitive is needed. Postcompose the descended
pairing with the homology map of the supplied cochain map. Naturality of the
homology projections and injectivity of the cycle inclusions give its formula
on any target cycle with the specified underlying cochain. Map the input and
target cycles first through alpha and then through beta. The cochain map's two
axis formulas, cyclesMap_i and homologyπ_naturality yield the required equalities.
No choice of representatives affects the descended map, since both boundary
submodules are annihilated. Empty covers and degree-zero cycles need no exception. -/
theorem exists_cupCech_total_pairing {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G) (p q : ℕ) :
    ∃ t : ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ)).homology p →ₗ[Γ(X, ⊤)]
      ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ)).homology q →ₗ[Γ(X, ⊤)]
      ((cupCechDouble U D.target.K).total (ComplexShape.up ℕ)).homology (p + q),
      (∀ (a : ((cupSections D.left).sc p).moduleCatLeftHomologyData.K)
        (b : ((cupSections D.right).sc q).moduleCatLeftHomologyData.K)
        (c : ((cupSections D.target).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
        t (HomologicalComplex.homologyMap (cupCechAlpha U D.left) p (cupCycleClass _ p a))
          (HomologicalComplex.homologyMap (cupCechAlpha U D.right) q (cupCycleClass _ q b)) =
        HomologicalComplex.homologyMap (cupCechAlpha U D.target) (p + q)
          (cupCycleClass _ (p + q) c)) ∧
      (∀ (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc p).moduleCatLeftHomologyData.K)
        (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc q).moduleCatLeftHomologyData.K)
        (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
          (p + q)).moduleCatLeftHomologyData.K),
        c.val = cechCupCochain U F G p q a.val b.val →
        t (HomologicalComplex.homologyMap (cupCechBeta U D.left) p (cupCycleClass _ p a))
          (HomologicalComplex.homologyMap (cupCechBeta U D.right) q (cupCycleClass _ q b)) =
        HomologicalComplex.homologyMap (cupCechBeta U D.target) (p + q)
          (cupCycleClass _ (p + q) c))  := by
  obtain ⟨h, hα, hβ⟩ := exists_cupCech_total_cochain_pairing U D
  obtain ⟨t, ht⟩ := tensorMap_homology_pairing _ _ _ h p q
  refine ⟨t, ?_, ?_⟩
  · intro a b c hc
    rw [cycleMap_class, cycleMap_class, cycleMap_class]
    apply ht
    rw [cycleMap_i, cycleMap_i, cycleMap_i, hc]
    exact (hα p q a.val b.val).symm
  · intro a b c hc
    rw [cycleMap_class, cycleMap_class, cycleMap_class]
    apply ht
    rw [cycleMap_i, cycleMap_i, cycleMap_i, hc]
    exact (hβ p q a.val b.val).symm

end
end AlgebraicGeometry.Scheme.Modules
