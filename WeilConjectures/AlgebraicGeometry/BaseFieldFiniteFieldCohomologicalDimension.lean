/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteModule.Basic
public import WeilConjectures.AlgebraicGeometry.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimensionSupplement
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

import WeilConjectures.AlgebraicGeometry.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteTorsionCohomologicalDimension
import WeilConjectures.RepresentationTheory.DiscreteModule.Torsion
import WeilConjectures.RepresentationTheory.ProfiniteIntegerSmoothPrimitives

/-!
# Cohomological dimension of finite and algebraically closed fields

Source: literature/blueprint/slopmaster2-20261029-2300/blueprint/
sec-six-functors-basics/sk-lem-base-field-cd/
sk-lem-base-field-cd-finite-field.md (blueprint: det-base-field-cd-finite-field).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

open CategoryTheory.Limits Action DiscreteModule

private theorem fixed_of_dense_generator
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (τ : G) (hd : DenseRange (zpowersHom G τ))
    (X : DiscreteModule.{w} G) (x : X.obj.V)
    (hx : (X.obj.ρ τ).hom x = x) : ∀ g : G, (X.obj.ρ g).hom x = x := by
  intro g
  let U := X.obj.stabilizer x
  have hU : IsClosed (U : Set G) := U.isClosed_of_isOpen (X.isOpen_stabilizer x)
  exact hd.induction_on g hU (fun z ↦ U.zpow_mem hx z.toAdd)

private theorem H_one_of_generator_surjective
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (τ : G) (hd : DenseRange (zpowersHom G τ))
    (X : DiscreteModule.{w} G)
    (hsurj : ∀ x : X.obj.V, ∃ y : X.obj.V, (X.obj.ρ τ).hom y - y = x) :
    Subsingleton (H G X 1) := by
  change Subsingleton (Abelian.Ext (intTrivial.{w} G) (shortComplex₁.{w} X).X₁ 1)
  rw [subsingleton_ext_one_iff (shortExact₁.{w} X) (subsingleton_H_coind₁.{w} _ 0),
    forall_exists_comp_eq_iff.{w}]
  intro z hz
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective z
  have hτf : (((coind₁.{w} G).obj X.obj.V).obj.ρ τ).hom f - f ∈ toCoind₁Range X := by
    rw [← QuotientAddGroup.eq_iff_sub_mem]
    exact hz τ
  obtain ⟨x, hx⟩ := hτf
  obtain ⟨y, hy⟩ := hsurj x
  let f' : ((coind₁.{w} G).obj X.obj.V).obj.V := f - (toCoind₁ X).hom.hom.hom y
  have hf'τ : (((coind₁.{w} G).obj X.obj.V).obj.ρ τ).hom f' = f' := by
    have h1 : (((coind₁.{w} G).obj X.obj.V).obj.ρ τ).hom f =
        f + (toCoind₁ X).hom.hom.hom x := by
      rw [hx]; abel
    simp only [f', map_sub, h1, ← hom_comm_apply, ← hy, map_sub]
    abel
  refine ⟨f', fixed_of_dense_generator τ hd _ f' hf'τ, ?_⟩
  have h0 : (QuotientAddGroup.mk ((toCoind₁ X).hom.hom.hom y) :
      (coker₁ X).obj.V) = 0 := (QuotientAddGroup.eq_zero_iff _).2 ⟨y, rfl⟩
  simp only [shortComplex₁, coker₁π_apply, f', QuotientAddGroup.mk_sub, h0, sub_zero]

private theorem completion_torsion_vanishing
    (M : DiscreteModule.{w} (ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (Multiplicative ℤ))))
    (hM : ∀ x : M.obj.V, IsOfFinAddOrder x) (s : ℕ) (hs : 2 ≤ s) :
    Subsingleton (H (ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (Multiplicative ℤ))) M s) := by
  classical
  let Z := GrpCat.of (Multiplicative ℤ)
  let G := ProfiniteGrp.ProfiniteCompletion.completion Z
  let τ : G := ProfiniteGrp.ProfiniteCompletion.etaFn Z (Multiplicative.ofAdd (1 : ℤ))
  have heta (z : Multiplicative ℤ) :
      τ ^ z.toAdd = ProfiniteGrp.ProfiniteCompletion.etaFn Z z := by
    change (ProfiniteGrp.ProfiniteCompletion.eta Z).hom (.ofAdd (1 : ℤ)) ^ z.toAdd =
      (ProfiniteGrp.ProfiniteCompletion.eta Z).hom z
    rw [← map_zpow]
    have hz : (Multiplicative.ofAdd (1 : ℤ)) ^ z.toAdd = z := by
      rw [← ofAdd_zsmul, zsmul_eq_mul, mul_one]
      rfl
    exact congrArg (ProfiniteGrp.ProfiniteCompletion.eta Z).hom hz
  have hd : DenseRange (zpowersHom G τ) := by
    convert ProfiniteGrp.ProfiniteCompletion.denseRange Z using 1
    exact funext heta
  let residue (n : ℕ) (hn : 0 < n) : G →ₜ* Multiplicative (ZMod n) := by
    have : NeZero n := ⟨by omega⟩
    exact (ProfiniteGrp.ProfiniteCompletion.lift (P := ProfiniteGrp.of (Multiplicative (ZMod n)))
      (GrpCat.ofHom (Int.castAddHom (ZMod n)).toMultiplicative)).hom
  have hresidue (n : ℕ) (hn : 0 < n) : residue n hn τ = Multiplicative.ofAdd 1 := by
    have : NeZero n := ⟨by omega⟩
    have h := congrArg (fun f : GrpCat.of (Multiplicative ℤ) ⟶
        GrpCat.of (Multiplicative (ZMod n)) ↦
      f.hom (Multiplicative.ofAdd (1 : ℤ)))
      (ProfiniteGrp.ProfiniteCompletion.lift_eta
        (P := ProfiniteGrp.of (Multiplicative (ZMod n)))
        (GrpCat.ofHom (Int.castAddHom (ZMod n)).toMultiplicative))
    change _ = Multiplicative.ofAdd ((1 : ℤ) : ZMod n) at h
    simpa only [GrpCat.hom_comp, GrpCat.hom_ofHom, MonoidHom.comp_apply,
      Int.cast_one] using! h
  have htwo (X : DiscreteModule.{w} G)
      (hX : ∀ x : X.obj.V, IsOfFinAddOrder x) : Subsingleton (H G X 2) := by
    have hsurj (z : (coker₁ X).obj.V) :
        ∃ y : (coker₁ X).obj.V, ((coker₁ X).obj.ρ τ).hom y - y = z := by
      obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective z
      obtain ⟨N, hN, hf⟩ := exists_pos_nsmul_eq_zero_of_finite
        (finite_range_smoothFunctions f) (by rintro _ ⟨x, rfl⟩; exact hX _)
      obtain ⟨h, hho, hh⟩ := exists_smooth_primitive_of_cyclic_residues τ hd residue hresidue
        (2 * N) (by omega) f.1 f.2 (fun x ↦ by
          rw [mul_smul, hf _ ⟨x, rfl⟩, smul_zero])
      let h' : ((coind₁ G).obj X.obj.V).obj.V := ⟨h, hho⟩
      refine ⟨QuotientAddGroup.mk h', ?_⟩
      rw [coker₁_ρ_mk, ← QuotientAddGroup.mk_sub]
      congr 1
      exact Subtype.ext (funext hh)
    exact subsingleton_ext_succ_of_shortExact (shortExact₁ X)
      (subsingleton_H_coind₁ _ 1) (H_one_of_generator_surjective τ hd (coker₁ X) hsurj)
  induction s, hs using Nat.le_induction generalizing M with
  | base => exact htwo M hM
  | succ n hn ih =>
    exact subsingleton_ext_succ_of_shortExact (shortExact₁ M) (subsingleton_H_coind₁ _ n)
      (ih _ (isOfFinAddOrder_coker₁ hM) hresidue)

/-- Fix a prime and state the finite-field cohomological-dimension result.

Source: literature/blueprint/slopmaster2-20261029-2300/blueprint/
sec-six-functors-basics/sk-lem-base-field-cd/
sk-lem-base-field-cd-finite-field.md, node `det-base-field-cd-finite-field`,
and Stacks Project Tag 03QQ (blueprint: det-base-field-cd-finite-field).

The proof has three parts. First, let `τ` be the image of `1` in the profinite
completion `G` of the integers; its integral powers are dense, and the universal
property gives continuous residue maps `G → ℤ/n` sending `τ` to `1`. Second,
for a torsion discrete module `X`, every smooth function `f : G → X` has finite
image, hence a positive annihilator `N`; the smooth primitive theorem
(node `lem-sfb-profinite-integer-smooth-primitives`) with exponent `2N`
makes `τ - 1` surjective on `C^sm(G, X) / X`. If `τ - 1` is surjective on a
discrete module, its `H¹` vanishes, because a `τ`-fixed smooth function is
`G`-fixed (its stabilizer is closed and contains the dense powers of `τ`);
the coinduced short exact sequence and the acyclicity of coinduced modules
therefore give `H²(G, X) = 0`. Since `C^sm(G, X) / X` is again torsion,
dimension shifting gives `Hˢ(G, X) = 0` for all `s ≥ 2`. Third, the field
clauses are the finite-field torsion bound
(node `det-base-field-cd-finite-torsion-bound`) and the two clauses of
`cohomologicalDimension_baseField` (node `sk-lem-base-field-cd`).
-/
theorem finiteField_cohomologicalDimension_statement (ℓ : ℕ) (hℓ : Nat.Prime ℓ) :
    (∀ (M : DiscreteModule.{w}
        (ProfiniteGrp.ProfiniteCompletion.completion
          (GrpCat.of (Multiplicative ℤ)))),
      (∀ x : M.obj.V, IsOfFinAddOrder x) →
        ∀ (s : ℕ), 2 ≤ s →
          Subsingleton
            (DiscreteModule.H
              (ProfiniteGrp.ProfiniteCompletion.completion
                (GrpCat.of (Multiplicative ℤ))) M s)) ∧
      (∀ (K : Type u) [Field K] [Finite K],
        Scheme.HasTorsionEtaleCohomologicalDimensionLE
            (Spec (.of K)) 1 ∧
          cohomologicalDimension ℓ hℓ (Spec (.of K)) ≤ 1) ∧
      (∀ (L : Type v) [Field L], IsAlgClosed L →
        cohomologicalDimension ℓ hℓ (Spec (.of L)) = 0) := by
  refine ⟨completion_torsion_vanishing, ?_, ?_⟩
  · intro K _ _
    exact ⟨
      Scheme.hasTorsionEtaleCohomologicalDimensionLE_one_of_finite_baseField K,
      (cohomologicalDimension_baseField ℓ hℓ K).2 inferInstance⟩
  · intro L _ hL
    exact (cohomologicalDimension_baseField ℓ hℓ L).1 hL

end AlgebraicGeometry.ProEtale

end
