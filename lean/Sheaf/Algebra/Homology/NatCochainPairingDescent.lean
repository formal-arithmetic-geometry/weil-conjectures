/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.Paper.ModuleCupResolutionData
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns

/-! # Descent of a nonnegative tensor cochain morphism

Source: Stacks Project, Tags 068G and 07MB.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace HomologicalComplex

private theorem descend_bilinear {k : Type u} [CommRing k]
    (S₁ S₂ : ShortComplex (ModuleCat.{u} k)) (M : ModuleCat.{u} k)
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
        simp only [hg, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  exact ⟨d, fun a b ↦ by change g _ _ = _; rw [hg, ht]⟩

private theorem tensor_cycles_lift {k : Type u} [CommRing k]
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

private theorem nat_tensor_homology_pairing {k : Type u} [CommRing k]
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
    obtain ⟨z, hz⟩ := tensor_cycles_lift A B n ⟨(p, q), hpq⟩ a b
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
        apply (cancel_mono ((A.sc 0).iCycles)).mp
        rw [(A.sc 0).toCycles_i, zero_comp]
        exact A.shape _ _ (by intro h; change _ + 1 = 0 at h; omega)
      rw [hz]
      simp [c₀]
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
        apply (cancel_mono ((B.sc 0).iCycles)).mp
        rw [(B.sc 0).toCycles_i, zero_comp]
        exact B.shape _ _ (by intro h; change _ + 1 = 0 at h; omega)
      rw [hz]
      simp [c₀]
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


end HomologicalComplex

namespace AlgebraicGeometry.Scheme.Modules

/-- A cochain morphism out of a tensor total complex induces a bilinear homology
pairing, with its value determined by the image of each tensor of cycles.
Source: Stacks Project, Tag 068G, tensor product of cocycles, and Tag 07MB.
(blueprint: lem-sc-nat-cochain-pairing-descent)

Proof: include the tensor of two cycles into the tensor total complex. Its
 differential is zero by the signed tensor Leibniz identity. Applying h preserves
cycles. This gives a bilinear map from the two cycle modules to target homology.
A boundary in the first variable is the differential of the tensor of its primitive
with the second cycle. A boundary in the second variable is, up to the invertible
sign (-1)^p, the differential of the first cycle tensored with its primitive.
Their target homology classes vanish. Descend through both boundary quotients,
identified with the homology modules using moduleCatHomologyIso. The quotient
formula gives the stated value; equality of the underlying target cycle identifies
its class. At degree zero the incoming differential is zero, so the corresponding
boundary argument is vacuous. The same construction works over the zero ring and
for zero complexes. -/
theorem natCochain_pairing_descent {R : Type u} [CommRing R]
    (A B C : CochainComplex (ModuleCat.{u} R) ℕ)
    (h : HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.up ℕ) ⟶ C) (p q : ℕ) :
    ∃ t : A.homology p →ₗ[R] B.homology q →ₗ[R] C.homology (p + q),
      ∀ (a : (A.sc p).moduleCatLeftHomologyData.K)
        (b : (B.sc q).moduleCatLeftHomologyData.K)
        (c : (C.sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = h.f (p + q)
          (HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{u} R))
            (ComplexShape.up ℕ) p q (p + q) rfl (a.val ⊗ₜ[R] b.val)) →
        t (cupCycleClass A p a) (cupCycleClass B q b) = cupCycleClass C (p + q) c := by
  let T := HomologicalComplex.mapBifunctor A B
    (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℕ)
  obtain ⟨t, ht⟩ := HomologicalComplex.nat_tensor_homology_pairing A B p q (p + q) rfl
  refine ⟨t.compr₂ (HomologicalComplex.homologyMap h (p + q)).hom, ?_⟩
  intro a b c hc
  obtain ⟨z, hz, htz⟩ := ht ((A.sc p).moduleCatCyclesIso.inv a)
    ((B.sc q).moduleCatCyclesIso.inv b)
  change HomologicalComplex.homologyMap h (p + q)
    (t (cupCycleClass A p a) (cupCycleClass B q b)) = _
  rw [show cupCycleClass A p a = A.homologyπ p ((A.sc p).moduleCatCyclesIso.inv a)
      from rfl,
    show cupCycleClass B q b = B.homologyπ q ((B.sc q).moduleCatCyclesIso.inv b)
      from rfl, htz]
  have hzc : HomologicalComplex.cyclesMap h (p + q) z =
      (C.sc (p + q)).moduleCatCyclesIso.inv c := by
    apply (ModuleCat.mono_iff_injective (C.iCycles (p + q))).mp inferInstance
    have hh := congrArg (fun f ↦ f z)
      (HomologicalComplex.cyclesMap_i h (p + q))
    change C.iCycles (p + q) (HomologicalComplex.cyclesMap h (p + q) z) =
      h.f (p + q) (T.iCycles (p + q) z) at hh
    rw [hh, hz]
    have hi (K : CochainComplex (ModuleCat.{u} R) ℕ) (i : ℕ)
        (x : (K.sc i).moduleCatLeftHomologyData.K) :
        K.iCycles i ((K.sc i).moduleCatCyclesIso.inv x) = x.val := by
      exact congrArg (fun f ↦ f x) (K.sc i).moduleCatCyclesIso_inv_iCycles
    rw [hi, hi, hi]
    exact hc.symm
  have hn := congrArg (fun f ↦ f z)
    (HomologicalComplex.homologyπ_naturality h (p + q))
  change HomologicalComplex.homologyMap h (p + q) (T.homologyπ (p + q) z) =
    C.homologyπ (p + q) (HomologicalComplex.cyclesMap h (p + q) z) at hn
  rw [hn, hzc]
  rfl

end AlgebraicGeometry.Scheme.Modules
