/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Module.PadicTorsionLinear
public import WeilConjectures.AlgebraicGeometry.ProEtale.IntegralAdicCohomology

/-!
# `Hⁿ(S, ℤ_p)` is the limit of the `Hⁿ(S, ℤ/pᵐ)`

The transition maps `Hⁿ(S, ℤ/pᵐ⁺¹) ⟶ Hⁿ(S, ℤ/pᵐ)`
(`AlgebraicGeometry.ProEtale.finiteAdicTransition`) are compatible with the reductions. Every
compatible family of classes of `Hⁿ(S, ℤ/pᵐ)` comes from a class of `Hⁿ(S, ℤ_p)`
(`AlgebraicGeometry.ProEtale.exists_reduction_eq`), unique if the groups `Hⁿ⁻¹(S, ℤ/pᵐ)` are
finite. Consequently a compatible family of biadditive maps on the finite levels lifts uniquely
to a `ℤ_p`-bilinear map on the integral cohomology
(`AlgebraicGeometry.ProEtale.integralAdicBilinear`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry.ProEtale

open PadicInt

variable (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]

/-- The transition map `Hⁿ(S, ℤ/pᵐ⁺¹) ⟶ Hⁿ(S, ℤ/pᵐ)`. -/
noncomputable def finiteAdicTransition (m n : ℕ) :
    FiniteAdicH S p (m + 1) n →+ FiniteAdicH S p m n :=
  Sheaf.H.map (continuousSheafMap S (openAddSubgroupQuotientMap (powOpenAddSubgroup p)
    (powOpenAddSubgroup_succ_le p) m)) n

lemma finiteAdicTransition_reduction (m n : ℕ) (x : IntegralAdicH S p n) :
    finiteAdicTransition S p m n (reduction S p (m + 1) n x) = reduction S p m n x := by
  refine (Ext.comp_assoc_of_third_deg_zero x _ _ (add_zero n)).trans ?_
  rw [Ext.mk₀_comp_mk₀, ← continuousSheafMap_comp]
  rfl

/-- **Compatible families of finite-level classes come from integral classes.** -/
theorem exists_reduction_eq (n : ℕ) (z : ∀ m, FiniteAdicH S p m n)
    (hz : ∀ m, finiteAdicTransition S p m n (z (m + 1)) = z m) :
    ∃ x : IntegralAdicH S p n, ∀ m, reduction S p m n x = z m := by
  have hU := powOpenAddSubgroup_succ_le p
  have hrep := Scheme.ProEt.epiπAppZeroOfEpi_addCommGrpCat (S := S)
  have := Abelian.hasFiniteBiproducts (C := Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
  have := lim_preservesEpimorphisms_of_epi_π_app_zero hrep
  have := hasExactLimitsOfShape_of_preservesEpi
    (Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}) (Discrete ℕ)
  have hepi (k : ℕ) :
      Epi ((continuousSheafTower S (powOpenAddSubgroup p) hU).map (homOfLE k.le_succ).op) := by
    rw [continuousSheafTower_map_succ]
    exact (shortExact_continuousSheafShortComplex S (powOpenAddSubgroup p) hU k).epi_g
  obtain ⟨x, hx⟩ := Ext.exists_comp_eq_of_isLimit_tower _
    (fun P hP t ht ↦ epi_one_sub_of_epiπAppZeroOfEpi hrep hepi hP t ht)
    (isLimitContinuousSheafCone S (powOpenAddSubgroup p) hU
      (eq_zero_of_forall_mem_powOpenAddSubgroup p)) (q := n) z fun m ↦ by
        rw [continuousSheafTower_map_succ]
        exact hz m
  exact ⟨x, hx⟩

variable {S p}

/-- **A compatible family of finite-level biadditive maps lifts to the integral cohomology.**
If `cₘ : Hⁱ(S, ℤ/pᵐ) × Hʲ(S, ℤ/pᵐ) ⟶ Hᵏ(S, ℤ/pᵐ)` are biadditive and compatible with the
transition maps, and the groups `Hᵏ⁻¹(S, ℤ/pᵐ)` are finite, there is a unique `ℤ_p`-bilinear
map `C` on the integral cohomology with `ρₘ (C x y) = cₘ (ρₘ x) (ρₘ y)`. -/
noncomputable def integralAdicBilinear {i j k : ℕ}
    (hfin : ∀ m k', k' + 1 = k → Finite (FiniteAdicH S p m k'))
    (c : ∀ m, FiniteAdicH S p m i →+ FiniteAdicH S p m j →+ FiniteAdicH S p m k)
    (hc : ∀ m a b, finiteAdicTransition S p m k (c (m + 1) a b) =
      c m (finiteAdicTransition S p m i a) (finiteAdicTransition S p m j b)) :
    IntegralAdicH S p i →ₗ[ℤ_[p]] IntegralAdicH S p j →ₗ[ℤ_[p]] IntegralAdicH S p k :=
  have hex (x : IntegralAdicH S p i) (y : IntegralAdicH S p j) :=
    exists_reduction_eq S p k (fun m ↦ c m (reduction S p m i x) (reduction S p m j y))
      fun m ↦ by rw [hc, finiteAdicTransition_reduction, finiteAdicTransition_reduction]
  have huniq (z z' : IntegralAdicH S p k)
      (h : ∀ m, reduction S p m k z = reduction S p m k z') : z = z' :=
    sub_eq_zero.1 (eq_zero_of_forall_reduction_eq_zero S p k hfin _
      fun m ↦ by rw [map_sub, h, sub_self])
  have hspec (x : IntegralAdicH S p i) (y : IntegralAdicH S p j) (m : ℕ) :
      reduction S p m k (hex x y).choose = c m (reduction S p m i x) (reduction S p m j y) :=
    (hex x y).choose_spec m
  LinearMap.mk₂ ℤ_[p] (fun x y ↦ (hex x y).choose)
    (fun x x' y ↦ huniq _ _ fun m ↦ by
      rw [hspec, map_add (reduction S p m k), hspec, hspec, map_add (reduction S p m i),
        map_add (c m), AddMonoidHom.add_apply])
    (fun r x y ↦ huniq _ _ fun m ↦ by
      rw [map_smul, hspec, hspec, map_smul,
        smul_eq_appr_nsmul (pow_smul_finiteAdicH S p m i),
        smul_eq_appr_nsmul (pow_smul_finiteAdicH S p m k), map_nsmul, AddMonoidHom.nsmul_apply])
    (fun x y y' ↦ huniq _ _ fun m ↦ by
      rw [hspec, map_add (reduction S p m k), hspec, hspec, map_add (reduction S p m j),
        map_add (c m _)])
    (fun r x y ↦ huniq _ _ fun m ↦ by
      rw [map_smul, hspec, hspec, map_smul,
        smul_eq_appr_nsmul (pow_smul_finiteAdicH S p m j),
        smul_eq_appr_nsmul (pow_smul_finiteAdicH S p m k), map_nsmul])

lemma reduction_integralAdicBilinear {i j k : ℕ}
    (hfin : ∀ m k', k' + 1 = k → Finite (FiniteAdicH S p m k'))
    (c : ∀ m, FiniteAdicH S p m i →+ FiniteAdicH S p m j →+ FiniteAdicH S p m k)
    (hc : ∀ m a b, finiteAdicTransition S p m k (c (m + 1) a b) =
      c m (finiteAdicTransition S p m i a) (finiteAdicTransition S p m j b))
    (m : ℕ) (x : IntegralAdicH S p i) (y : IntegralAdicH S p j) :
    reduction S p m k (integralAdicBilinear hfin c hc x y) =
      c m (reduction S p m i x) (reduction S p m j y) :=
  (exists_reduction_eq S p k (fun m ↦ c m (reduction S p m i x) (reduction S p m j y))
    fun m ↦ by rw [hc, finiteAdicTransition_reduction, finiteAdicTransition_reduction]).choose_spec
      m

/-- Integral classes are determined by their reductions (for finite `Hᵏ⁻¹(S, ℤ/pᵐ)`). -/
lemma eq_of_forall_reduction_eq {k : ℕ}
    (hfin : ∀ m k', k' + 1 = k → Finite (FiniteAdicH S p m k')) (z z' : IntegralAdicH S p k)
    (h : ∀ m, reduction S p m k z = reduction S p m k z') : z = z' :=
  sub_eq_zero.1 (eq_zero_of_forall_reduction_eq_zero S p k hfin _
    fun m ↦ by rw [map_sub, h, sub_self])

end AlgebraicGeometry.ProEtale
