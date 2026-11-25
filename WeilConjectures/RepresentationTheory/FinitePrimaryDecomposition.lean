/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.GroupTheory.PGroup
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.RingTheory.Int.Basic

/-!
# Primary decomposition of finite discrete representations

A finite discrete continuous representation `M` of a topological group on an abelian group
splits equivariantly as a finite direct sum of finite `p`-primary discrete representations.

## Main statements

- `Rep.exists_finite_primary_decomposition`: the primary decomposition of `M`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace Rep

/-- A finite discrete continuous integral representation splits into finite primary
representations equivariantly: there are primes `p i`, finite `p i`-primary discrete
representations `N i` and morphisms `a i : M ⟶ N i`, `b i : N i ⟶ M` with
`∑ i, a i ≫ b i = 𝟙 M`. -/
theorem exists_finite_primary_decomposition
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteContinuousRep.{0, u, v} ℤ G) [Finite M.obj.V] :
    ∃ (r : ℕ) (p : Fin r → ℕ) (N : Fin r → DiscreteContinuousRep.{0, u, v} ℤ G),
      (∀ i, (p i).Prime) ∧ (∀ i, Finite (N i).obj.V) ∧
      (∀ i, IsPGroup (p i) (Multiplicative (N i).obj.V)) ∧
      ∃ (a : ∀ i, M ⟶ N i) (b : ∀ i, N i ⟶ M),
        ∑ i, a i ≫ b i = 𝟙 M := by
  classical
  -- Normalize the bundled integral module structure to the canonical one.
  rcases M with ⟨@⟨V, hV, hmodule, ρ⟩, hcont⟩
  have hm : hmodule = AddCommGroup.toIntModule V := Subsingleton.elim _ _
  subst hmodule
  let M : DiscreteContinuousRep.{0, u, v} ℤ G := ⟨Rep.of ρ, hcont⟩
  have hM : Module.IsTorsion ℤ M.obj.V :=
    isAddTorsion_iff_isTorsion_int.mp isAddTorsion_of_finite
  -- Mathlib supplies the primary torsion submodules and their internal direct sum.
  obtain ⟨ι, fι, dι, p, hp, e, hS⟩ :=
    Submodule.exists_isInternal_prime_power_torsion_of_pid hM
  let := fι
  let := dι
  let S : ι → Submodule ℤ M.obj.V := fun i ↦ Submodule.torsionBy ℤ M.obj.V (p i ^ e i)
  let : DirectSum.Decomposition S := hS.chooseDecomposition
  have hstable (i : ι) (g : G) : S i ≤ (S i).comap (M.obj.ρ g) := by
    intro x hx
    change p i ^ e i • M.obj.ρ g x = 0
    rw [← map_smul, show p i ^ e i • x = 0 from hx, map_zero]
  let σ (i : ι) : Representation ℤ G (S i) :=
    M.obj.ρ.subrepresentation (S i) (hstable i)
  let N (i : ι) : DiscreteContinuousRep.{0, u, v} ℤ G :=
    ⟨Rep.of (σ i), fun x ↦ by
      have heq : {g : G | σ i g x = x} = {g : G | M.obj.ρ g x.val = x.val} := by
        ext g
        exact Subtype.ext_iff
      rw [heq]
      exact M.property x.val⟩
  let P (i : ι) : M.obj.V →ₗ[ℤ] S i :=
    (DirectSum.component ℤ ι (fun i ↦ S i) i).comp
      (DirectSum.decomposeLinearEquiv S).toLinearMap
  have hP (i j : ι) (x : S j) :
      P i x.val = DirectSum.component ℤ ι (fun i ↦ S i) i (DirectSum.lof ℤ ι _ j x) := by
    simp only [P, LinearMap.comp_apply, LinearEquiv.coe_coe,
      DirectSum.decomposeLinearEquiv_apply_coe]
  -- Check equivariance on each summand, where the projection is identity or zero.
  have hcomm (i : ι) (g : G) : P i ∘ₗ M.obj.ρ g = σ i g ∘ₗ P i := by
    apply DirectSum.decompose_lhom_ext S
    intro j
    apply LinearMap.ext
    intro x
    change P i (M.obj.ρ g x.val) = σ i g (P i x.val)
    change P i (σ j g x).val = σ i g (P i x.val)
    rw [hP, hP]
    by_cases h : j = i
    · subst j
      simp
    · simp [DirectSum.component.of, h]
  let a (i : ι) : M ⟶ N i :=
    ObjectProperty.homMk (Rep.ofHom ⟨P i, fun g ↦ hcomm i g⟩)
  let b (i : ι) : N i ⟶ M :=
    ObjectProperty.homMk (Rep.ofHom ⟨(S i).subtype, fun g ↦ by ext x; rfl⟩)
  have hprime (i : ι) : (p i).natAbs.Prime := by
    rw [← Int.prime_iff_natAbs_prime, ← irreducible_iff_prime]
    exact hp i
  have hprimary (i : ι) : IsPGroup (p i).natAbs (Multiplicative (N i).obj.V) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    refine ⟨e i, ?_⟩
    change (p i).natAbs ^ e i • Multiplicative.toAdd x = 0
    rw [← Int.natAbs_pow, natAbs_nsmul_eq_zero]
    exact Submodule.smul_torsionBy _ _
  have hsum (x : M.obj.V) : ∑ i, (P i x).val = x := by
    have h := DirectSum.sum_support_decompose S x
    change ∑ i, (DirectSum.decompose S x i).val = x
    calc
      _ = ∑ i ∈ (DirectSum.decompose S x).support,
          (DirectSum.decompose S x i).val := ?_
      _ = x := h
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hz : DirectSum.decompose S x i = 0 := by
      simpa only [DFinsupp.mem_support_toFun, not_not] using hi
    simp only [hz, ZeroMemClass.coe_zero]
  let t : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun i ↦ (p (t i)).natAbs, fun i ↦ N (t i),
    fun i ↦ hprime (t i), fun i ↦ inferInstance, fun i ↦ hprimary (t i),
    fun i ↦ a (t i), fun i ↦ b (t i), ?_⟩
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  ext x
  change ((∑ i, a (t i) ≫ b (t i)).hom.hom.toLinearMap) x = x
  let F : DiscreteContinuousRep.{0, u, v} ℤ G ⥤ Rep.{v} ℤ G := ObjectProperty.ι _
  have hf : (∑ i, a (t i) ≫ b (t i)).hom = ∑ i, (a (t i) ≫ b (t i)).hom :=
    F.map_sum _ _
  rw [hf, Rep.sum_hom]
  change (∑ i, ((a (t i) ≫ b (t i)).hom).hom) x = x
  rw [Representation.IntertwiningMap.sum_apply]
  change ∑ i, (P (t i) x).val = x
  calc
    _ = ∑ i, (P i x).val := Fintype.sum_equiv t _ _ (fun _ ↦ rfl)
    _ = x := hsum x

end Rep
