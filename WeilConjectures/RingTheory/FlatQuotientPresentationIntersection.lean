/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

import Mathlib.RingTheory.Flat.Equalizer

/-!
# Intersection of presentation relations with an extended ideal

Let `F → M` be a surjection with kernel `L`, and suppose `M / IM` is flat over `R / I`. After
base change to an `R`-algebra `B`, the relations in `B ⊗[R] L` whose image lies in `IB` times
`B ⊗[R] F` are sums of extended relations from `L ∩ IF` and `IB`-multiples of extended
relations.

## Implementation details

Modulo `I` the presentation gives a short exact sequence `0 → L/H → F/IF → M/IM → 0` with
`H = L ∩ IF`. Flatness of `M/IM` makes the inclusion `L/H → F/IF` stay injective after
tensoring with `B/IB`, and right exactness then decomposes the given relation. No flatness or
freeness of `F` or `B` is required.

## References

* [Stacks, Tag 00MM]
* [Stacks, Tag 00MO]
* [Stacks, Tag 00HL]
-/

@[expose] public section

universe u v w t
open scoped TensorProduct

namespace Module

private theorem quotient_unitTensor_surjective
    {R X : Type*} [CommRing R] [AddCommGroup X] [Module R X] (I : Ideal R) :
    Function.Surjective (TensorProduct.mk R (R ⧸ I) X 1) := by
  intro y
  let e := TensorProduct.quotTensorEquivQuotSMul X I
  obtain ⟨x, hx⟩ := (I • (⊤ : Submodule R X)).mkQ_surjective (e y)
  refine ⟨x, e.injective ?_⟩
  simpa [e] using hx

private theorem quotient_lTensor_injective
    {R Q C X Y : Type*} [CommRing R] [CommRing Q] [Algebra R Q]
    [AddCommGroup C] [Module R C] [Module Q C] [IsScalarTower R Q C]
    [AddCommGroup X] [Module R X] [Module Q X] [IsScalarTower R Q X]
    [AddCommGroup Y] [Module R Y] [Module Q Y] [IsScalarTower R Q Y]
    (hs : Function.Surjective (algebraMap R Q)) (d : X →ₗ[Q] Y)
    (hd : Function.Injective (d.lTensor C)) :
    Function.Injective ((d.restrictScalars R).lTensor C) := by
  let := TensorProduct.CompatibleSMul.of_algebraMap_surjective C X hs
  let := TensorProduct.CompatibleSMul.of_algebraMap_surjective C Y hs
  let eX := TensorProduct.equivOfCompatibleSMul R Q R C X
  let eY := TensorProduct.equivOfCompatibleSMul R Q R C Y
  have he (z : C ⊗[Q] X) :
      (d.restrictScalars R).lTensor C (eX z) = eY (d.lTensor C z) := by
    induction z using TensorProduct.inductionOn with
    | tmul c x => rfl
    | add a b ha hb => simp [ha, hb]
  intro a b hab
  obtain ⟨a, rfl⟩ := eX.surjective a
  obtain ⟨b, rfl⟩ := eX.surjective b
  rw [he, he] at hab
  exact congrArg eX (hd (eY.injective hab))

/-- Relations in an extended presentation which lie in the extended ideal are sums of
extended ideal-valued original relations and ideal multiples of extended relations, provided
`M / IM` is flat over `R / I`. -/
theorem flat_quotient_presentation_intersection
    {R : Type u} {B : Type v} {F : Type w} {M : Type t}
    [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    (I : Ideal R) (q : F →ₗ[R] M) (hq : Function.Surjective q)
    (hflat : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)) :
    q.ker.baseChange B ⊓ I.map (algebraMap R B) • (⊤ : Submodule B (B ⊗[R] F)) ≤
      (q.ker ⊓ I • (⊤ : Submodule R F)).baseChange B ⊔
        I.map (algebraMap R B) • q.ker.baseChange B  := by
  classical
  let Q := R ⧸ I
  let J := I.map (algebraMap R B)
  let C := B ⧸ J
  let φ : Q →+* C := Ideal.Quotient.lift I
    ((Ideal.Quotient.mk J).comp (algebraMap R B)) (by
      intro r hr
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr))
  let : Algebra Q C := φ.toAlgebra
  have htower : IsScalarTower R Q C := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change Ideal.Quotient.mk J (algebraMap R B r) = φ (Ideal.Quotient.mk I r)
    rfl
  let := htower
  let a : B →ₗ[R] C := (Ideal.Quotient.mkₐ R J).toLinearMap
  have ha : Function.Surjective a := Ideal.Quotient.mk_surjective
  let p := q.baseChange Q
  let V := p.ker
  let d : V →ₗ[Q] Q ⊗[R] F := V.subtype
  let e : q.ker →ₗ[R] V :=
    { toFun := fun l ↦ ⟨(1 : Q) ⊗ₜ[R] (l : F), by
        change (1 : Q) ⊗ₜ[R] q l = 0
        rw [LinearMap.mem_ker.mp l.property, TensorProduct.tmul_zero]⟩
      map_add' := fun l k ↦ by ext; simp [TensorProduct.tmul_add]
      map_smul' := fun r l ↦ by ext; simp [TensorProduct.tmul_smul] }
  have he : Function.Surjective e := by
    intro v
    obtain ⟨t, ht⟩ := (_root_.lTensor_exact Q q.exact_subtype_ker_map hq v.val).mp v.property
    obtain ⟨l, hl⟩ := quotient_unitTensor_surjective I t
    refine ⟨l, ?_⟩
    apply Subtype.ext
    change (1 : Q) ⊗ₜ[R] (l : F) = v.val
    rw [← ht, ← hl]
    rfl
  have hd : Function.Injective ((d.restrictScalars R).lTensor C) := by
    let := hflat
    apply quotient_lTensor_injective (Ideal.Quotient.mk_surjective) d
    exact LinearMap.lTensor_injective_of_exact_of_flat p
      (LinearMap.baseChange_surjective Q hq) d V.injective_subtype
      p.exact_subtype_ker_map C
  have heker (l : q.ker) : l ∈ e.ker ↔ (l : F) ∈ I • (⊤ : Submodule R F) := by
    rw [LinearMap.mem_ker]
    change (⟨(1 : Q) ⊗ₜ[R] (l : F), _⟩ : V) = 0 ↔ _
    rw [Subtype.ext_iff]
    change (TensorProduct.mk R Q F 1) (l : F) = 0 ↔ _
    rw [← LinearMap.mem_ker, LinearMap.ker_tensorProductMk]
  intro z hz
  obtain ⟨t, ht⟩ := hz.1
  have hred (b : B) (hb : b ∈ J) (x : B ⊗[R] F) :
      a.rTensor F (b • x) = 0 := by
    have hb0 : a b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    induction x using TensorProduct.inductionOn with
    | tmul c f =>
      simp only [TensorProduct.smul_tmul', smul_eq_mul, LinearMap.rTensor_tmul]
      have hab : a (b * c) = a b * a c := map_mul (Ideal.Quotient.mk J) b c
      rw [hab, hb0, zero_mul, TensorProduct.zero_tmul]
    | add x y hx hy => simp [smul_add, hx, hy]
  have hz0 : a.rTensor F z = 0 := by
    exact Submodule.smul_induction_on hz.2 (fun b hb x _ ↦ hred b hb x)
      (fun x y hx hy ↦ by simp [hx, hy])
  let tc := a.rTensor q.ker t
  have hcomm (t : B ⊗[R] q.ker) :
      (d.restrictScalars R).lTensor C (e.lTensor C (a.rTensor q.ker t)) =
        (TensorProduct.mk R Q F 1).lTensor C
          (a.rTensor F (q.ker.subtype.baseChange B t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul b l => rfl
    | add x y hx hy => simp [hx, hy]
  have htc : e.lTensor C tc = 0 := by
    apply hd
    rw [map_zero]
    change (d.restrictScalars R).lTensor C
      (e.lTensor C (a.rTensor q.ker t)) = 0
    rw [hcomm, ht, hz0, map_zero]
  obtain ⟨s, hs⟩ := (_root_.lTensor_exact C e.exact_subtype_ker_map he tc).mp htc
  obtain ⟨v, hv⟩ := LinearMap.rTensor_surjective e.ker ha s
  let vl := e.ker.subtype.baseChange B v
  have hvc : a.rTensor q.ker vl = tc := by
    have hvcomm (v : B ⊗[R] e.ker) :
        a.rTensor q.ker (e.ker.subtype.baseChange B v) =
          e.ker.subtype.lTensor C (a.rTensor e.ker v) := by
      induction v using TensorProduct.inductionOn with
      | tmul b l => rfl
      | add x y hx hy => simp [hx, hy]
    rw [hvcomm, hv, hs]
  have hdiff : a.rTensor q.ker (t - vl) = 0 := by
    rw [map_sub, hvc]
    exact sub_self tc
  obtain ⟨w, hw⟩ := (_root_.rTensor_exact q.ker a.exact_subtype_ker_map ha (t - vl)).mp
    hdiff
  have hfirst : q.ker.subtype.baseChange B vl ∈
      (q.ker ⊓ I • (⊤ : Submodule R F)).baseChange B := by
    change q.ker.subtype.baseChange B (e.ker.subtype.baseChange B v) ∈ _
    clear hv hvc hdiff hs htc ht hz hw
    induction v using TensorProduct.inductionOn with
    | tmul b l =>
      exact Submodule.tmul_mem_baseChange_of_mem b
        ⟨l.val.property, (heker l.val).mp l.property⟩
    | add x y hx hy => simpa using Submodule.add_mem _ hx hy
  have hsecond : q.ker.subtype.baseChange B (t - vl) ∈ J • q.ker.baseChange B := by
    rw [← hw]
    clear hw
    induction w using TensorProduct.inductionOn with
    | tmul b l =>
      have hb : (b : B) ∈ J := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        exact LinearMap.mem_ker.mp b.property
      change (b : B) ⊗ₜ[R] (l : F) ∈ J • q.ker.baseChange B
      rw [← mul_one (b : B), ← smul_eq_mul, ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem_smul hb (Submodule.tmul_mem_baseChange_of_mem 1 l.property)
    | add x y hx hy => simpa using Submodule.add_mem _ hx hy
  apply Submodule.mem_sup.mpr
  refine ⟨q.ker.subtype.baseChange B vl, hfirst,
    q.ker.subtype.baseChange B (t - vl), hsecond, ?_⟩
  rw [← map_add, add_sub_cancel, ht]

end Module
