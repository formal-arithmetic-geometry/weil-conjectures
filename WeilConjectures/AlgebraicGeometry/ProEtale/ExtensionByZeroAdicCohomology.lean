/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.IntegralAdicCohomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono

/-!
# Integral `ℓ`-adic cohomology of an extension by zero

Let `j : U ⟶ T` be an open immersion of schemes and `p` a prime (in practice `ℓ`). This file
develops, for the pro-étale cohomology of the extensions by zero
`Hⁿ(T, j_! ℤ_p) = Hⁿ(T_proét, j_! C(-, ℤ_p))`
(`AlgebraicGeometry.ProEtale.CompactIntegralAdicH`) and
`Hⁿ(T, j_! ℤ/pᵐ) = Hⁿ(T_proét, j_! C(-, ℤ_p / pᵐ))`
(`AlgebraicGeometry.ProEtale.CompactFiniteAdicH`), the lattice theory that
`WeilConjectures.AlgebraicGeometry.ProEtale.IntegralAdicCohomology` develops for the constant
sheaves. When `T` is proper over an algebraically closed field these are the compactly
supported cohomology groups of `U`; the results feed the `ℚ̄_ℓ` stage of the compactly
supported case of blueprint `thm-pod-degreewise-perfectness-over-a-field`.

* the **Bockstein sequence**: the extension by zero `j_!` is exact, so it maps the Bockstein
  sequence `0 ⟶ ℤ_p --pᵐ--> ℤ_p ⟶ ℤ/pᵐ ⟶ 0` to a short exact sequence, whence
  `AlgebraicGeometry.ProEtale.exists_eq_pow_smul_of_compactReduction_eq_zero` and
  `AlgebraicGeometry.ProEtale.pow_smul_mem_range_compactReduction`;
* **separation** and **finite generation**
  (`AlgebraicGeometry.ProEtale.eq_zero_of_forall_compactReduction_eq_zero`,
  `AlgebraicGeometry.ProEtale.module_finite_compactIntegralAdicH`), from the fact that
  `j_! C(-, ℤ_p)` is the limit of the tower `j_! C(-, ℤ/pᵐ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian PadicInt

namespace AlgebraicGeometry.ProEtale

section RingHom

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  {R : Type*} [Ring R]

/-- An additive functor maps an action `R →+* End X` of a ring on an object to an action on its
image. -/
@[simps]
def _root_.CategoryTheory.Functor.mapRingHom (G : C ⥤ D) [G.Additive] {X : C}
    (φ : R →+* End X) : R →+* End (G.obj X) where
  toFun r := G.map (φ r)
  map_one' := by rw [map_one]; exact G.map_id X
  map_mul' r s := by rw [map_mul]; exact G.map_comp _ _
  map_zero' := by rw [map_zero]; exact G.map_zero _ _
  map_add' r s := by rw [map_add]; exact G.map_add

end RingHom

variable {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (p : ℕ) [Fact p.Prime]

/-- The action of `ℤ_p` on `j_! C(-, ℤ_p)`. -/
noncomputable abbrev compactIntegralSmulRingHom :
    ℤ_[p] →+* End ((j)_!open[AddCommGrpCat.{u + 1}].obj (continuousSheaf U ℤ_[p])) :=
  (j)_!open[AddCommGrpCat.{u + 1}].mapRingHom (integralSmulRingHom U p)

/-- The action of `ℤ_p` on `j_! C(-, ℤ_p / pᵐ)`. -/
noncomputable abbrev compactFiniteSmulRingHom (m : ℕ) :
    ℤ_[p] →+* End ((j)_!open[AddCommGrpCat.{u + 1}].obj
      (continuousSheaf U (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p])))) :=
  (j)_!open[AddCommGrpCat.{u + 1}].mapRingHom (finiteSmulRingHom U p m)

/-- The integral `p`-adic pro-étale cohomology `Hⁿ(T, j_! ℤ_p) = Hⁿ(T_proét, j_! C(-, ℤ_p))` of
the extension by zero along an open immersion `j : U ⟶ T`, a `ℤ_p`-module. For `T` proper over
an algebraically closed field this is the compactly supported cohomology `Hⁿ_c(U, ℤ_p)`. -/
def CompactIntegralAdicH (n : ℕ) : Type (u + 1) :=
  Sheaf.H ((j)_!open[AddCommGrpCat.{u + 1}].obj (continuousSheaf U ℤ_[p])) n

noncomputable instance (n : ℕ) : AddCommGroup (CompactIntegralAdicH j p n) :=
  inferInstanceAs (AddCommGroup (Sheaf.H ((j)_!open[AddCommGrpCat.{u + 1}].obj
    (continuousSheaf U ℤ_[p])) n))

noncomputable instance (n : ℕ) : Module ℤ_[p] (CompactIntegralAdicH j p n) :=
  Ext.moduleOfRingHom (compactIntegralSmulRingHom j p) n

/-- The pro-étale cohomology `Hⁿ(T, j_! ℤ/pᵐ) = Hⁿ(T_proét, j_! C(-, ℤ_p / pᵐ))` of the
extension by zero along an open immersion `j : U ⟶ T`, a `ℤ_p`-module. -/
def CompactFiniteAdicH (m n : ℕ) : Type (u + 1) :=
  Sheaf.H ((j)_!open[AddCommGrpCat.{u + 1}].obj
    (continuousSheaf U (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p])))) n

noncomputable instance (m n : ℕ) : AddCommGroup (CompactFiniteAdicH j p m n) :=
  inferInstanceAs (AddCommGroup (Sheaf.H ((j)_!open[AddCommGrpCat.{u + 1}].obj
    (continuousSheaf U (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p])))) n))

noncomputable instance (m n : ℕ) : Module ℤ_[p] (CompactFiniteAdicH j p m n) :=
  Ext.moduleOfRingHom (compactFiniteSmulRingHom j p m) n

/-- The extension by zero `j_! C(-, ℤ_p) ⟶ j_! C(-, ℤ_p / pᵐ)` of the reduction. -/
noncomputable abbrev compactReductionSheafMap (m : ℕ) :
    (j)_!open[AddCommGrpCat.{u + 1}].obj (continuousSheaf U ℤ_[p]) ⟶
      (j)_!open[AddCommGrpCat.{u + 1}].obj
        (continuousSheaf U (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p]))) :=
  (j)_!open[AddCommGrpCat.{u + 1}].map (reductionSheafMap U p m)

lemma compactReductionSheafMap_comm (m : ℕ) (c : ℤ_[p]) :
    compactIntegralSmulRingHom j p c ≫ compactReductionSheafMap j p m =
      compactReductionSheafMap j p m ≫ compactFiniteSmulRingHom j p m c := by
  simp only [Functor.mapRingHom_apply, ← Functor.map_comp, reductionSheafMap_comm]

/-- The reduction `ρₘ : Hⁿ(T, j_! ℤ_p) ⟶ Hⁿ(T, j_! ℤ/pᵐ)`. -/
noncomputable def compactReduction (m n : ℕ) :
    CompactIntegralAdicH j p n →ₗ[ℤ_[p]] CompactFiniteAdicH j p m n :=
  Ext.postcompLinearMap (compactIntegralSmulRingHom j p) (compactFiniteSmulRingHom j p m)
    (compactReductionSheafMap j p m) (compactReductionSheafMap_comm j p m) n

lemma compactReduction_apply (m n : ℕ) (x : CompactIntegralAdicH j p n) :
    compactReduction j p m n x = Ext.comp (C := Sheaf (Scheme.ProEt.topology T)
      AddCommGrpCat.{u + 1}) x (Ext.mk₀ (compactReductionSheafMap j p m)) (add_zero n) :=
  rfl

/-- `pᵐ` kills `Hⁿ(T, j_! ℤ/pᵐ)`. -/
lemma pow_smul_compactFiniteAdicH (m n : ℕ) (y : CompactFiniteAdicH j p m n) :
    (p : ℤ_[p]) ^ m • y = 0 := by
  have h : finiteSmulRingHom U p m ((p : ℤ_[p]) ^ m) = 0 := by
    refine (continuousSheafMap_congr U fun x ↦ ?_).trans (continuousSheafMap_zero U)
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      refine (QuotientAddGroup.eq_zero_iff _).2 ?_
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  change Ext.comp y (Ext.mk₀ ((j)_!open[AddCommGrpCat.{u + 1}].map
    (finiteSmulRingHom U p m ((p : ℤ_[p]) ^ m)))) (add_zero n) = 0
  rw [h, Functor.map_zero, Ext.mk₀_zero, Ext.comp_zero]

/-- The extension by zero of the Bockstein short complex,
`j_! C(-, ℤ_p) --pᵐ--> j_! C(-, ℤ_p) ⟶ j_! C(-, ℤ_p / pᵐ)`. -/
noncomputable abbrev compactBocksteinShortComplex (m : ℕ) :
    ShortComplex (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) :=
  (bocksteinShortComplex U p m).map (j)_!open[AddCommGrpCat.{u + 1}]

lemma shortExact_compactBocksteinShortComplex (m : ℕ) :
    (compactBocksteinShortComplex j p m).ShortExact :=
  (shortExact_bocksteinShortComplex U p m).map_of_exact _

/-- **Bockstein, first part.** The kernel of `ρₘ : Hⁿ(T, j_! ℤ_p) ⟶ Hⁿ(T, j_! ℤ/pᵐ)` is
`pᵐ Hⁿ(T, j_! ℤ_p)`. -/
theorem exists_eq_pow_smul_of_compactReduction_eq_zero (m n : ℕ)
    {x : CompactIntegralAdicH j p n} (hx : compactReduction j p m n x = 0) :
    ∃ x', x = (p : ℤ_[p]) ^ m • x' := by
  obtain ⟨x', hx'⟩ := Ext.covariant_sequence_exact₂ _
    (shortExact_compactBocksteinShortComplex j p m) (n := n) x hx
  exact ⟨x', hx'.symm⟩

/-- The connecting map `δ : Hⁿ(T, j_! ℤ/pᵐ) ⟶ Hⁿ⁺¹(T, j_! ℤ_p)` of the Bockstein sequence. -/
noncomputable def compactBocksteinδ (m n : ℕ) :
    CompactFiniteAdicH j p m n →+ CompactIntegralAdicH j p (n + 1) :=
  AddMonoidHom.mk' (fun y ↦ Ext.comp (C := Sheaf (Scheme.ProEt.topology T)
    AddCommGrpCat.{u + 1}) y (shortExact_compactBocksteinShortComplex j p m).extClass rfl)
    fun _ _ ↦ Ext.add_comp _ _ _ _

private lemma pow_smul_eq_nsmul_compactIntegral (n e : ℕ) (x : CompactIntegralAdicH j p n) :
    (p : ℤ_[p]) ^ e • x = (p ^ e) • x := by
  rw [← Ext.smul_natCast_eq_nsmul (compactIntegralSmulRingHom j p) n (p ^ e) x, Nat.cast_pow]

private lemma pow_smul_eq_nsmul_compactFinite (m n e : ℕ) (y : CompactFiniteAdicH j p m n) :
    (p : ℤ_[p]) ^ e • y = (p ^ e) • y := by
  rw [← Ext.smul_natCast_eq_nsmul (compactFiniteSmulRingHom j p m) n (p ^ e) y, Nat.cast_pow]

/-- **Bockstein, second part.** If `pᵉ` kills the `p`-power torsion of `Hⁿ⁺¹(T, j_! ℤ_p)`,
then the image of `ρₘ : Hⁿ(T, j_! ℤ_p) ⟶ Hⁿ(T, j_! ℤ/pᵐ)` contains `pᵉ Hⁿ(T, j_! ℤ/pᵐ)`. -/
theorem pow_smul_mem_range_compactReduction (m n e : ℕ)
    (he : ∀ x : CompactIntegralAdicH j p (n + 1), (∃ k, (p : ℤ_[p]) ^ k • x = 0) →
      (p : ℤ_[p]) ^ e • x = 0)
    (y : CompactFiniteAdicH j p m n) :
    (p : ℤ_[p]) ^ e • y ∈ LinearMap.range (compactReduction j p m n) := by
  have hδ (k : ℕ) : compactBocksteinδ j p m n ((p : ℤ_[p]) ^ k • y) =
      (p : ℤ_[p]) ^ k • compactBocksteinδ j p m n y := by
    rw [pow_smul_eq_nsmul_compactFinite, pow_smul_eq_nsmul_compactIntegral, map_nsmul]
  have h0 : compactBocksteinδ j p m n ((p : ℤ_[p]) ^ e • y) = 0 := by
    rw [hδ, he _ ⟨m, by rw [← hδ, pow_smul_compactFiniteAdicH, map_zero]⟩]
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ _
    (shortExact_compactBocksteinShortComplex j p m) ((p : ℤ_[p]) ^ e • y) rfl h0
  exact ⟨x, hx⟩


section Separation

variable {j p}

/-- The tower `j_! C(-, ℤ_p / pᵐ)` of extensions by zero. -/
noncomputable abbrev compactContinuousSheafTower :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  continuousSheafTower U (powOpenAddSubgroup p) (powOpenAddSubgroup_succ_le p) ⋙
    (j)_!open[AddCommGrpCat.{u + 1}]

variable (j p) in
/-- The cone `j_! C(-, ℤ_p) ⟶ j_! C(-, ℤ_p / pᵐ)` over the tower `compactContinuousSheafTower`. -/
noncomputable abbrev compactContinuousSheafCone :
    Cone (compactContinuousSheafTower (j := j) (p := p)) :=
  (j)_!open[AddCommGrpCat.{u + 1}].mapCone
    (continuousSheafCone U (powOpenAddSubgroup p) (powOpenAddSubgroup_succ_le p))

/-- **Separation in degree `n + 1`**, given that `j_! C(-, ℤ_p)` is the limit of the tower
`j_! C(-, ℤ/pᵐ)`. -/
theorem eq_zero_of_forall_compactReduction_eq_zero_succ_of_isLimit
    (hlim : IsLimit (compactContinuousSheafCone j p)) (n : ℕ)
    (hfin : ∀ m, Finite (CompactFiniteAdicH j p m n)) (x : CompactIntegralAdicH j p (n + 1))
    (hx : ∀ m, compactReduction j p m (n + 1) x = 0) : x = 0 := by
  have hU := powOpenAddSubgroup_succ_le p
  have hrep := Scheme.ProEt.epiπAppZeroOfEpi_addCommGrpCat (S := T)
  have := Abelian.hasFiniteBiproducts (C := Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
  have := lim_preservesEpimorphisms_of_epi_π_app_zero hrep
  have := hasExactLimitsOfShape_of_preservesEpi
    (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) (Discrete ℕ)
  have hepi (k : ℕ) :
      Epi ((compactContinuousSheafTower (j := j) (p := p)).map (homOfLE k.le_succ).op) := by
    rw [Functor.comp_map, continuousSheafTower_map_succ]
    have : Epi (continuousSheafMap U (openAddSubgroupQuotientMap (powOpenAddSubgroup p) hU k)) :=
      (shortExact_continuousSheafShortComplex U (powOpenAddSubgroup p) hU k).epi_g
    exact (j)_!open[AddCommGrpCat.{u + 1}].map_epi _
  refine Ext.eq_zero_of_isLimit_tower _
    (fun P hP t ht ↦ epi_one_sub_of_epiπAppZeroOfEpi hrep hepi hP t ht) hlim (q := n)
    (fun y ↦ ?_) x hx
  let F := compactContinuousSheafTower (j := j) (p := p)
  have (k : ℕ) : Finite (Sheaf.H (F.obj (op k)) n) := hfin k
  obtain ⟨w, hw⟩ := AddCommGroup.exists_sub_map_succ_eq_of_finite
    (G := fun k ↦ Sheaf.H (F.obj (op k)) n)
    (fun k ↦ (Ext.mk₀ (F.map (homOfLE k.le_succ).op)).postcomp _ (add_zero n)) y
  exact ⟨w, hw⟩

/-- **Separation in degree `0`**, given that `j_! C(-, ℤ_p)` is the limit of the tower
`j_! C(-, ℤ/pᵐ)`. -/
theorem eq_zero_of_forall_compactReduction_eq_zero_zero_of_isLimit
    (hlim : IsLimit (compactContinuousSheafCone j p)) (x : CompactIntegralAdicH j p 0)
    (hx : ∀ m, compactReduction j p m 0 x = 0) : x = 0 := by
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
  have hf : f = 0 := by
    refine hlim.hom_ext fun ⟨m⟩ ↦ ?_
    rw [zero_comp]
    refine (Ext.mk₀_bijective _ _).1 ?_
    rw [Ext.mk₀_zero, ← Ext.mk₀_comp_mk₀]
    exact hx m
  rw [hf, Ext.mk₀_zero]

/-- **Separation**, given that `j_! C(-, ℤ_p)` is the limit of the tower `j_! C(-, ℤ/pᵐ)`: if
the groups `Hⁿ⁻¹(T, j_! ℤ/pᵐ)` are finite, a class of `Hⁿ(T, j_! ℤ_p)` whose reductions modulo
all `pᵐ` vanish is zero. -/
theorem eq_zero_of_forall_compactReduction_eq_zero_of_isLimit
    (hlim : IsLimit (compactContinuousSheafCone j p)) (n : ℕ)
    (hfin : ∀ m k, k + 1 = n → Finite (CompactFiniteAdicH j p m k))
    (x : CompactIntegralAdicH j p n) (hx : ∀ m, compactReduction j p m n x = 0) : x = 0 := by
  cases n with
  | zero => exact eq_zero_of_forall_compactReduction_eq_zero_zero_of_isLimit hlim x hx
  | succ n =>
    exact eq_zero_of_forall_compactReduction_eq_zero_succ_of_isLimit hlim n
      (fun m ↦ hfin m n rfl) x hx

/-- **Finite generation**, given that `j_! C(-, ℤ_p)` is the limit of the tower
`j_! C(-, ℤ/pᵐ)`: if the groups `Hⁿ⁻¹(T, j_! ℤ/pᵐ)` and `Hⁿ(T, j_! ℤ/p)` are finite, then
`Hⁿ(T, j_! ℤ_p)` is a finitely generated `ℤ_p`-module. -/
theorem module_finite_compactIntegralAdicH_of_isLimit
    (hlim : IsLimit (compactContinuousSheafCone j p)) (n : ℕ)
    (hfin : ∀ m k, k + 1 = n → Finite (CompactFiniteAdicH j p m k))
    [Finite (CompactFiniteAdicH j p 1 n)] :
    Module.Finite ℤ_[p] (CompactIntegralAdicH j p n) :=
  PadicInt.module_finite_of_finite_quotient (fun m ↦ compactReduction j p m n)
    (fun m y ↦ pow_smul_compactFiniteAdicH j p m n y)
    (fun m _ ha ↦ exists_eq_pow_smul_of_compactReduction_eq_zero j p m n ha)
    (fun a ha ↦ eq_zero_of_forall_compactReduction_eq_zero_of_isLimit hlim n hfin a ha)

end Separation

end AlgebraicGeometry.ProEtale
