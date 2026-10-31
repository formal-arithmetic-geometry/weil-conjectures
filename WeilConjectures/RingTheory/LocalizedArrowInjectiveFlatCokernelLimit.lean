/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import WeilConjectures.RingTheory.LocalizedBaseChangeQuotientFlat

/-!
# Injectivity and flat cokernels in localized directed limits

Source: Stacks Project, Algebra, Tag 046Y, final sentence; Tags 00D7, 00DF, and the
first proof paragraph of Tag 00MO.
(blueprint: lem-trf-localized-arrow-injective-flat-cokernel-limit)

Scalar extensions are written with the new scalar ring on the left. Tensor symmetry
identifies these with the right scalar extensions in the source statement, by
`x ⊗ s ↦ s ⊗ x`. The formulas below specify the canonical comparisons completely.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module

private theorem flat_of_flat_zero_quotient_tensor
    {R P : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    (J : Ideal R) (hJ : J = ⊥)
    (h : Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] P)) : Module.Flat R P := by
  have : Module.Flat R (R ⧸ J) :=
    Module.Flat.of_linearEquiv (Submodule.quotEquivOfEqBot J hJ)
  have : Module.Flat R ((R ⧸ J) ⊗[R] P) :=
    Module.Flat.trans R (R ⧸ J) _
  let e := (TensorProduct.quotTensorEquivQuotSMul P J).trans
    (Submodule.quotEquivOfEqBot _ (by simp [hJ]))
  exact Module.Flat.of_linearEquiv e.symm

set_option linter.unusedVariables false in
/-- Eventual injectivity and flat cokernels pass to the limit of localized module-arrow
systems. Source: Stacks Project, Algebra, Tag 046Y, final sentence, expanded by Tags 00D7,
00DF and the first proof paragraph of Tag 00MO.
(blueprint: lem-trf-localized-arrow-injective-flat-cokernel-limit)

Proof:
1. Represent an element of the kernel of `u` at a stage using `hM_represent`. Its image
   vanishes in `N`. By `hN_equal` it vanishes at a later stage; directedness gives a
   still later stage beyond `i₀`. Arrow compatibility and injectivity there show that
   the representative is zero, hence the original element is zero (Tag 00D7).
2. At every index, tensor the right exact sequence defined by the quotient by
   `LinearMap.range (ui i)`. Tensor right exactness
   [lem-weil-pbc-tensor-right-exact] identifies its cokernel after scalar extension
   with the quotient by `LinearMap.range u`, through `alpha`, `beta`, and `h_arrow`.
   The inverse sends the class of `n` to the scalar-extended quotient of
   `(beta i).symm n`. Changing `n` by `u m` changes this representative by the
   image of the scalar-extended arrow, so the inverse is well defined. The two
   composites are identities after the surjective quotient maps. This gives the
   displayed pure-tensor formula, at all indices, including those before `i₀`.
3. Apply [lem-weil-pbc-localized-base-change-quotient-flat] to the rings
   `Ri.obj i₀`, `Si.obj i₀`, `cR.pt`, `cS.pt`, the zero ideal, and the stage
   cokernel. Its input is `h_tail` at `i₀`; its localization is `h_localization`.
   The identifications of quotient by zero and tensor with the ground ring give
   flatness over `cR.pt` of the scalar-extended stage cokernel. Transport this
   flatness through the comparison of step 2, restricted to `cR.pt` scalars.
No locality, Noetherianity, finite generation, or nontriviality is needed. -/
theorem injective_flat_cokernel_of_localized_directed_limit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (Ri Si : I ⥤ CommRingCat.{u})
    (cR : Cocone Ri) (cS : Cocone Si)
    (hcR : IsColimit cR) (hcS : IsColimit cS)
    [Algebra cR.pt cS.pt]
    [∀ i : I, Algebra (Ri.obj i) (Si.obj i)]
    [∀ i : I, Algebra (Ri.obj i) cR.pt]
    [∀ i : I, Algebra (Si.obj i) cS.pt]
    [∀ i : I, Algebra (Ri.obj i) cS.pt]
    [∀ i : I, IsScalarTower (Ri.obj i) (Si.obj i) cS.pt]
    [∀ i : I, IsScalarTower (Ri.obj i) cR.pt cS.pt]
    (hR : ∀ (i : I), algebraMap (Ri.obj i) cR.pt = (cR.ι.app i).hom)
    (hS : ∀ (i : I), algebraMap (Si.obj i) cS.pt = (cS.ι.app i).hom)
    (h_ring_arrow : ∀ (i j : I) (h : i ≤ j) (r : Ri.obj i),
      (Si.map (homOfLE h)).hom (algebraMap (Ri.obj i) (Si.obj i) r) =
        algebraMap (Ri.obj j) (Si.obj j) ((Ri.map (homOfLE h)).hom r))
    (Mi Ni : I → Type u)
    [∀ i : I, AddCommGroup (Mi i)] [∀ i : I, AddCommGroup (Ni i)]
    [∀ i : I, Module (Si.obj i) (Mi i)] [∀ i : I, Module (Si.obj i) (Ni i)]
    [∀ i : I, Module (Ri.obj i) (Ni i)]
    [∀ i : I, IsScalarTower (Ri.obj i) (Si.obj i) (Ni i)]
    (ui : ∀ i : I, Mi i →ₗ[Si.obj i] Ni i)
    (m : ∀ (i j : I), i ≤ j → Mi i →+ Mi j)
    (n : ∀ (i j : I), i ≤ j → Ni i →+ Ni j)
    (hm_smul : ∀ (i j : I) (h : i ≤ j) (s : Si.obj i) (x : Mi i),
      m i j h (s • x) = (Si.map (homOfLE h)).hom s • m i j h x)
    (hn_smul : ∀ (i j : I) (h : i ≤ j) (s : Si.obj i) (y : Ni i),
      n i j h (s • y) = (Si.map (homOfLE h)).hom s • n i j h y)
    (hm_id : ∀ (i : I) (x : Mi i), m i i le_rfl x = x)
    (hn_id : ∀ (i : I) (y : Ni i), n i i le_rfl y = y)
    (hm_comp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (x : Mi i),
      m j k hjk (m i j hij x) = m i k (hij.trans hjk) x)
    (hn_comp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (y : Ni i),
      n j k hjk (n i j hij y) = n i k (hij.trans hjk) y)
    (h_stage_arrow : ∀ (i j : I) (h : i ≤ j) (x : Mi i),
      n i j h (ui i x) = ui j (m i j h x))
    (M N : Type u) [AddCommGroup M] [AddCommGroup N]
    [Module cS.pt M] [Module cS.pt N]
    [Module cR.pt N] [IsScalarTower cR.pt cS.pt N]
    (mu : ∀ i : I, Mi i →+ M) (nu : ∀ i : I, Ni i →+ N)
    (hmu_smul : ∀ (i : I) (s : Si.obj i) (x : Mi i),
      mu i (s • x) = algebraMap (Si.obj i) cS.pt s • mu i x)
    (hnu_smul : ∀ (i : I) (s : Si.obj i) (y : Ni i),
      nu i (s • y) = algebraMap (Si.obj i) cS.pt s • nu i y)
    (hmu_comp : ∀ (i j : I) (h : i ≤ j) (x : Mi i), mu j (m i j h x) = mu i x)
    (hnu_comp : ∀ (i j : I) (h : i ≤ j) (y : Ni i), nu j (n i j h y) = nu i y)
    (u : M →ₗ[cS.pt] N)
    (h_limit_arrow : ∀ (i : I) (x : Mi i), nu i (ui i x) = u (mu i x))
    (hM_represent : ∀ x : M, ∃ (i : I) (xi : Mi i), mu i xi = x)
    (hN_represent : ∀ y : N, ∃ (i : I) (yi : Ni i), nu i yi = y)
    (hM_equal : ∀ (i j : I) (x : Mi i) (y : Mi j),
      mu i x = mu j y → ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
        m i k hik x = m j k hjk y)
    (hN_equal : ∀ (i j : I) (x : Ni i) (y : Ni j),
      nu i x = nu j y → ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
        n i k hik x = n j k hjk y)
    (alpha : ∀ i : I, (cS.pt ⊗[Si.obj i] Mi i) ≃ₗ[cS.pt] M)
    (beta : ∀ i : I, (cS.pt ⊗[Si.obj i] Ni i) ≃ₗ[cS.pt] N)
    (h_alpha : ∀ (i : I) (x : Mi i) (s : cS.pt),
      alpha i (s ⊗ₜ[Si.obj i] x) = s • mu i x)
    (h_beta : ∀ (i : I) (y : Ni i) (s : cS.pt),
      beta i (s ⊗ₜ[Si.obj i] y) = s • nu i y)
    (h_arrow : ∀ (i : I) (t : cS.pt ⊗[Si.obj i] Mi i),
      beta i ((ui i).lTensor cS.pt t) = u (alpha i t))
    (h_localization : ∀ i : I,
      ∃ (q : Si.obj i ⊗[Ri.obj i] cR.pt →+* cS.pt)
        (W : Submonoid (Si.obj i ⊗[Ri.obj i] cR.pt)),
        (∀ (a : Si.obj i) (r : cR.pt), q (a ⊗ₜ[Ri.obj i] r) =
          algebraMap (Si.obj i) cS.pt a * algebraMap cR.pt cS.pt r) ∧
        (∀ w : W, IsUnit (q w)) ∧
        (∀ s : cS.pt, ∃ (a : Si.obj i ⊗[Ri.obj i] cR.pt) (w : W),
          s * q w = q a) ∧
        (∀ a : Si.obj i ⊗[Ri.obj i] cR.pt, q a = 0 →
          ∃ w : W, (w : Si.obj i ⊗[Ri.obj i] cR.pt) * a = 0))
    (i₀ : I)
    (h_tail : ∀ j : I, i₀ ≤ j →
      Function.Injective (ui j) ∧
        Module.Flat (Ri.obj j) (Ni j ⧸ LinearMap.range (ui j))) :
    Function.Injective u ∧ Module.Flat cR.pt (N ⧸ LinearMap.range u) ∧
      ∀ i : I,
        ∃ e : (cS.pt ⊗[Si.obj i] (Ni i ⧸ LinearMap.range (ui i))) ≃ₗ[cS.pt]
            (N ⧸ LinearMap.range u),
          ∀ (y : Ni i) (s : cS.pt),
            e (s ⊗ₜ[Si.obj i] (LinearMap.range (ui i)).mkQ y) =
              s • (LinearMap.range u).mkQ (nu i y) := by
  have hinj : Function.Injective u := by
    apply (injective_iff_map_eq_zero u).mpr
    intro x hx
    obtain ⟨i, xi, rfl⟩ := hM_represent x
    have hz : nu i (ui i xi) = nu i 0 := by
      rw [h_limit_arrow, hx, map_zero]
    obtain ⟨j, hij, _, hj⟩ := hN_equal i i (ui i xi) 0 hz
    obtain ⟨k, hjk, h₀k⟩ := exists_ge_ge j i₀
    have hk : ui k (m i k (hij.trans hjk) xi) = 0 := by
      rw [← h_stage_arrow, ← hn_comp i j k hij hjk, hj, map_zero, map_zero]
    have hm : m i k (hij.trans hjk) xi = 0 :=
      (h_tail k h₀k).1 (hk.trans (map_zero (ui k)).symm)
    rw [← hmu_comp i k (hij.trans hjk) xi, hm, map_zero]
  have hcompare : ∀ i : I,
      ∃ e : (cS.pt ⊗[Si.obj i] (Ni i ⧸ LinearMap.range (ui i))) ≃ₗ[cS.pt]
          (N ⧸ LinearMap.range u),
        ∀ (y : Ni i) (s : cS.pt),
          e (s ⊗ₜ[Si.obj i] (LinearMap.range (ui i)).mkQ y) =
            s • (LinearMap.range u).mkQ (nu i y) := by
    intro i
    let P := LinearMap.range
      (TensorProduct.AlgebraTensorModule.lTensor cS.pt cS.pt (ui i).range.subtype)
    have hmap : P.map (beta i).toLinearMap = LinearMap.range u := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hz' : z ∈ LinearMap.range ((ui i).lTensor cS.pt) := by
          rw [LinearMap.lTensor_range]
          exact hz
        obtain ⟨t, rfl⟩ := hz'
        exact ⟨alpha i t, (h_arrow i t).symm⟩
      · rintro ⟨x, rfl⟩
        obtain ⟨t, rfl⟩ := (alpha i).surjective x
        refine ⟨(ui i).lTensor cS.pt t, ?_, h_arrow i t⟩
        change (ui i).lTensor cS.pt t ∈
          LinearMap.range ((ui i).range.subtype.lTensor cS.pt)
        rw [← LinearMap.lTensor_range]
        exact ⟨t, rfl⟩
    let e := (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv
      cS.pt (Si.obj i) cS.pt (LinearMap.range (ui i))).trans
      (Submodule.Quotient.equiv P (LinearMap.range u) (beta i) hmap)
    refine ⟨e, ?_⟩
    intro y s
    change (LinearMap.range u).mkQ (beta i (s ⊗ₜ[Si.obj i] y)) = _
    rw [h_beta, map_smul]
  refine ⟨hinj, ?_, hcompare⟩
  obtain ⟨e, _⟩ := hcompare i₀
  have hflat : Module.Flat cR.pt
      (cS.pt ⊗[Si.obj i₀] (Ni i₀ ⧸ LinearMap.range (ui i₀))) := by
    let C := Ni i₀ ⧸ LinearMap.range (ui i₀)
    have : Module.Flat (Ri.obj i₀) C := (h_tail i₀ le_rfl).2
    have hloc : ∃ (q : Si.obj i₀ ⊗[Ri.obj i₀] cR.pt →+* cS.pt)
        (W : Submonoid (Si.obj i₀ ⊗[Ri.obj i₀] cR.pt)),
        (∀ (a : Si.obj i₀) (r : cR.pt), q (a ⊗ₜ[Ri.obj i₀] r) =
          algebraMap (Si.obj i₀) cS.pt a * algebraMap cR.pt cS.pt r) ∧
        (let := q.toAlgebra; IsLocalization W cS.pt) := by
      obtain ⟨q, W, hq, hu, hs, hz⟩ := h_localization i₀
      refine ⟨q, W, hq, ?_⟩
      let : Algebra (Si.obj i₀ ⊗[Ri.obj i₀] cR.pt) cS.pt := q.toAlgebra
      apply (isLocalization_iff W cS.pt).mpr
      refine ⟨hu, ?_, ?_⟩
      · intro s
        obtain ⟨a, w, h⟩ := hs s
        exact ⟨⟨a, w⟩, h⟩
      · intro a b hab
        change q a = q b at hab
        obtain ⟨w, hw⟩ := hz (a - b) (by rw [map_sub, hab, sub_self])
        exact ⟨w, sub_eq_zero.mp (by rw [← mul_sub, hw])⟩
    have ht := flat_quotient_localized_baseChange
      (R := Ri.obj i₀) (S := Si.obj i₀) (R' := cR.pt) (S' := cS.pt)
      (⊥ : Ideal (Ri.obj i₀)) C hloc (by infer_instance)
    exact flat_of_flat_zero_quotient_tensor _ Ideal.map_bot ht
  exact (Module.Flat.equiv_iff (e.restrictScalars cR.pt)).mp hflat

end Module
