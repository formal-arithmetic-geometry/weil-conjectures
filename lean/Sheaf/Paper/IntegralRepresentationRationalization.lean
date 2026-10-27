/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.Paper.LisseCompletedSystemData
public import Sheaf.Paper.EtaleMonodromyRealizationData
import Sheaf.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Rationalization of continuous integral representations

Source: Bhatt--Scholze, Corollary 6.8.5, p. 60.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory
open scoped TensorProduct Topology
namespace AlgebraicGeometry.Scheme
open ProEtale.CompletedLisse

private theorem integral_coordinate_continuous (l : ℕ) [Fact l.Prime] (P : Base.{u} l)
    {L : Type*} [AddCommGroup L] [Module (Integers l P) L]
    (f : L →ₗ[Integers l P] Integers l P) :
    let := spectralNorm.nontriviallyNormedField ℚ_[l] P.E
    @Continuous L P.E ((Padic.coefficientExtensionMaximalIdeal l P.E).adicModuleTopology L)
      inferInstance (fun x ↦ (f x : P.E)) := by
  let := spectralNorm.nontriviallyNormedField ℚ_[l] P.E
  let R := Integers l P
  let I := Padic.coefficientExtensionMaximalIdeal l P.E
  have h := (Padic.extension_integers_dvr l P.E
    (Padic.coefficientExtensionAbsoluteValue l P.E)
    (spectralNorm_extends (K := ℚ_[l]) (L := P.E))).choose_spec.choose_spec
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l P.E} : Set R) = I :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  let BL : AddGroupFilterBasis L := by
    let : TopologicalSpace R := I.adicTopology
    exact (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis L)).toAddGroupFilterBasis
  let : TopologicalSpace L := BL.topology
  let : IsTopologicalAddGroup L := BL.isTopologicalAddGroup
  have hc : Continuous f := by
    apply continuous_of_tendsto_nhds_zero f
    rw [BL.nhds_zero_hasBasis.tendsto_iff
      (Padic.coefficientExtension_integers_coset_basis l P.E 0)]
    intro n _
    refine ⟨(I ^ (n + 1) • ⊤ : Submodule R L), ⟨n + 1, rfl⟩, ?_⟩
    intro x hx
    change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l P.E (n + 1)) (f x) =
      Ideal.Quotient.mk _ 0
    rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
    change f x ∈ Ideal.span ({Padic.coefficientExtensionUniformizer l P.E} : Set R) ^ _
    rw [hgen]
    have hm := Submodule.smul_top_le_comap_smul_top (I ^ (n + 1)) f hx
    simpa only [Submodule.mem_comap, smul_eq_mul, Ideal.mul_top] using hm
  exact continuous_subtype_val.comp hc

/-- Extending a finite free integral representation to the fraction field preserves
joint continuity, and the tensor unit exhibits the original module as a stable lattice.

Source: Bhatt--Scholze, Corollary 6.8.5, proof, p. 60
(blueprint: lem-a1-integral-representation-rationalization).

Proof: Choose a finite integral basis and extend it to a basis of the tensor product.
In these bases the tensor unit is the coordinatewise inclusion of the valuation ring
into its fraction field, so it is injective and its image spans. Extend every action
map by scalars; functoriality gives the representation laws and stability of the image.
Integral linear coordinates are continuous for the adic topology: their inverse
images carry each power-ideal submodule into the same power ideal. Uniformizer cosets
are a neighbourhood basis in the valuation ring. Thus every matrix coefficient of
the extended action is continuous in the group variable. Expanding a vector in the
finite extended basis writes the joint action as a finite sum of products of these
continuous matrix coefficients and the continuous vector coordinates. This proves
joint continuity for the module topology, including when the basis is empty. -/
theorem integral_representation_rationalization
    (l : ℕ) [Fact l.Prime] (P : Base.{u} l) (p : SfMonodromyPoint P.X)
    (L : ModuleCat.{u + 1} (Integers l P)) [Module.Finite (Integers l P) L]
    [Module.Free (Integers l P) L] (ρ : Representation (Integers l P) p.group L)
    (hc : @Continuous _ _
      (@instTopologicalSpaceProd _ _ inferInstance
        ((Padic.coefficientExtensionMaximalIdeal l P.E).adicModuleTopology L))
      ((Padic.coefficientExtensionMaximalIdeal l P.E).adicModuleTopology L)
      (fun z : p.group × L ↦ ρ z.1 z.2)) :
    ∃ (V : SfContinuousRepresentations l P.E p)
      (e : (ModuleCat.extendScalars (Integers l P).subtype).obj L ≅ ModuleCat.of P.E V.obj.V)
      (B : SfInvariantLattice l P.E V) (i : L ≃ₗ[Integers l P] B.submodule),
      Function.Injective ((ModuleCat.ExtendRestrictScalarsAdj.unit.{u + 1, u + 1, u + 1}
        (Integers l P).subtype).app L) ∧
      (∀ x : L, (i x).val = e.hom
        ((ModuleCat.ExtendRestrictScalarsAdj.unit.{u + 1, u + 1, u + 1}
          (Integers l P).subtype).app L x)) ∧
      (∀ (g : p.group) (x : L),
        e.hom ((ModuleCat.ExtendRestrictScalarsAdj.unit.{u + 1, u + 1, u + 1}
          (Integers l P).subtype).app L
          (ρ g x)) = V.obj.ρ g
          (e.hom ((ModuleCat.ExtendRestrictScalarsAdj.unit.{u + 1, u + 1, u + 1}
          (Integers l P).subtype).app L x))) := by
  classical
  let R := Integers l P
  let E := P.E
  let W := E ⊗[R] L
  let b := Module.finBasis R L
  let c := b.baseChange E
  let σ : Representation E p.group W :=
    (Module.End.baseChangeHom R E L).toMonoidHom.comp ρ
  let j : L →ₗ[R] W :=
    (ModuleCat.ExtendRestrictScalarsAdj.unit.{u + 1, u + 1, u + 1} R.subtype).app L |>.hom
  have hj (x : L) : j x = (1 : E) ⊗ₜ[R] x := rfl
  have hσ (g : p.group) (x : L) : σ g (j x) = j (ρ g x) := by
    change (ρ g).baseChange E ((1 : E) ⊗ₜ[R] x) = (1 : E) ⊗ₜ[R] (ρ g x)
    rfl
  have hji : Function.Injective j := by
    intro x y hxy
    apply b.repr.injective
    ext k
    have he := congrArg (fun z : W ↦ c.repr z k) hxy
    simp only [hj, c, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one] at he
    exact he
  have hfd : FiniteDimensional E W := Module.Finite.of_basis c
  have hcont : let := spectralNorm.nontriviallyNormedField ℚ_[l] E
      let : TopologicalSpace W := moduleTopology E W
      Continuous (fun z : p.group × W ↦ σ z.1 z.2) := by
    let := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let : TopologicalSpace W := moduleTopology E W
    let : IsModuleTopology E W := ⟨rfl⟩
    let : ContinuousAdd W := ModuleTopology.continuousAdd E W
    let : ContinuousSMul E W := ModuleTopology.continuousSMul E W
    have hcoef (k t : Fin (Module.finrank R L)) :
        Continuous (fun g : p.group ↦ ((b.repr (ρ g (b t)) k : R) : E)) := by
      let : TopologicalSpace L :=
        (Padic.coefficientExtensionMaximalIdeal l E).adicModuleTopology L
      exact (integral_coordinate_continuous l P ((Finsupp.lapply k).comp b.repr.toLinearMap)).comp
        (hc.comp (continuous_id.prodMk continuous_const))
    have hbase (t : Fin (Module.finrank R L)) : Continuous (fun g : p.group ↦ σ g (c t)) := by
      have he (g : p.group) : σ g (c t) =
          ∑ k, ((b.repr (ρ g (b t)) k : R) : E) • c k := by
        rw [show c t = (1 : E) ⊗ₜ[R] b t from Module.Basis.baseChange_apply E b t]
        rw [← hj, hσ]
        apply c.repr.injective
        ext k
        simp [hj, c, Module.Basis.baseChange_repr_tmul, Algebra.smul_def,
          Finset.sum_apply, Finsupp.single_apply]
        rfl
      simp_rw [he]
      exact continuous_finsetSum _ (fun k _ ↦ (hcoef k t).smul continuous_const)
    have he (z : p.group × W) : σ z.1 z.2 =
        ∑ t, c.repr z.2 t • σ z.1 (c t) := by
      conv_lhs => rw [← c.sum_repr z.2]
      simp only [map_sum, map_smul]
    simp_rw [he]
    apply continuous_finsetSum
    intro t _
    exact ((IsModuleTopology.continuous_of_linearMap
      ((Finsupp.lapply t).comp c.repr.toLinearMap)).comp continuous_snd).smul
        ((hbase t).comp continuous_fst)
  let V : SfContinuousRepresentations l E p :=
    ⟨Rep.of σ, hfd, hcont⟩
  let B : SfInvariantLattice l E V :=
    { submodule := LinearMap.range j
      finite := Module.Finite.equiv (LinearEquiv.ofInjective j hji)
      free := Module.Free.of_equiv (LinearEquiv.ofInjective j hji)
      spans := by
        apply top_unique
        rw [← c.span_eq]
        apply Submodule.span_mono
        rintro _ ⟨t, rfl⟩
        exact ⟨⟨j (b t), LinearMap.mem_range_self j (b t)⟩,
          (Module.Basis.baseChange_apply E b t).symm⟩
      stable := by
        rintro g ⟨_, x, rfl⟩
        exact ⟨ρ g x, (hσ g x).symm⟩ }
  refine ⟨V, Iso.refl _, B, LinearEquiv.ofInjective j hji, hji, fun x ↦ rfl, ?_⟩
  intro g x
  exact (hσ g x).symm

end AlgebraicGeometry.Scheme
