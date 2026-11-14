/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.IsCurve

/-- The geometric data underlying the separably closed comparison square.
Source: Stacks Project, Tag 0A5E, compatible algebraic closures. -/
theorem exists_sepClosed_comparison_core
    {k k' : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsProper f]
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
      (K' : Type u) (_ : Field K') (_ : IsAlgClosed K')
      (D D' : Scheme.{u}) (b : D ⟶ Spec (.of K)) (b' : D' ⟶ Spec (.of K'))
      (j : Spec (.of K') ⟶ Spec (.of K)) (a : D' ⟶ D) (p : D ⟶ C) (p' : D' ⟶ C')
      (t : Spec (.of K) ⟶ Spec (.of k)),
      IsPullback p b f t ∧ IsPullback a b' b j ∧ IsUniversalHomeomorphism p ∧
        IsUniversalHomeomorphism p' ∧ p' ≫ ι' = a ≫ p := by
  let φ : k →+* k' := (Spec.preimage ι).hom
  let K' := AlgebraicClosure k'
  let : Algebra k K' := ((algebraMap k' K').comp φ).toAlgebra
  let K := algebraicClosure k K'
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  let t : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let t' : Spec (.of K') ⟶ Spec (.of k') :=
    Spec.map (CommRingCat.ofHom (algebraMap k' K'))
  let j : Spec (.of K') ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraicClosure k K').subtype)
  have hj : j ≫ t = t' ≫ ι := by
    rw [← Spec.map_preimage ι]
    simp only [j, t, t', ← Spec.map_comp]
    congr 1
  let D := Limits.pullback f t
  let D' := Limits.pullback f' t'
  let p : D ⟶ C := Limits.pullback.fst f t
  let b : D ⟶ Spec (.of K) := Limits.pullback.snd f t
  let p' : D' ⟶ C' := Limits.pullback.fst f' t'
  let b' : D' ⟶ Spec (.of K') := Limits.pullback.snd f' t'
  have ht : IsPullback p b f t := .of_hasPullback f t
  have ht' : IsPullback p' b' f' t' := .of_hasPullback f' t'
  have hs : IsPullback (p' ≫ ι') b' f (j ≫ t) := by
    rw [hj]
    exact ht'.paste_horiz h
  let a : D' ⟶ D := ht.lift (p' ≫ ι') (b' ≫ j)
    (by rw [hs.w, Category.assoc])
  have ha : IsPullback a b' b j := hs.of_right' ht
  refine ⟨K, inferInstance, inferInstance, K', inferInstance, inferInstance,
    D, D', b, b', j, a, p, p', t, ht, ha, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · exact (ht.lift_fst _ _ _).symm

end AlgebraicGeometry.IsCurve
