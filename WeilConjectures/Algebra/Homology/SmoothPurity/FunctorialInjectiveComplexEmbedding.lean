/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-!
# Functorial complex embeddings through injective subobjects

Source: Stacks Project, Injectives, Lemma `lemma-functorial-injective`
(blueprint: lem-pur-kinjective-functorial-injective).
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CochainComplex

/-- Source: Stacks Project, Injectives, Lemma `lemma-functorial-injective`
(blueprint: lem-pur-kinjective-functorial-injective).
In a Grothendieck abelian category there is a functorial termwise monomorphic
quasi-isomorphism into a complex, factoring in each degree through an injective subobject.
The subobject is represented by the monomorphism `b` from the injective object `I`.

Proof: let `N` be the functorial K-injective replacement
`CochainComplex.kInjectiveResolutionFunctor` (node lem-weil-pbc-kinjective-functorial-existence;
Stacks, Injectives, Theorem 079P) and `j` its augmentation
`CochainComplex.toKInjectiveResolution`. By `monoQuasiIso_toKInjectiveResolution_app`, each
`j.app M` is a monomorphic quasi-isomorphism, so it is termwise monic and a quasi-isomorphism.
By `injective_kInjectiveResolutionFunctor_obj_X`, every term `(N.obj M).X n` is injective
(maps out of the acyclic two-term complex `X ⟶ X` lift against `N.obj M ⟶ 0`). The factorization
clause takes `I = (N.obj M).X n`, `a = (j.app M).f n` and `b = 𝟙 I`. -/
theorem exists_functorial_injective_complex_embedding
    (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C] :
    ∃ (N : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
      (j : 𝟭 (CochainComplex C ℤ) ⟶ N),
      ∀ (M : CochainComplex C ℤ),
        (∀ (n : ℤ), Mono ((j.app M).f n)) ∧ QuasiIso (j.app M) ∧
          ∀ (n : ℤ), ∃ (I : C) (a : M.X n ⟶ I) (b : I ⟶ (N.obj M).X n),
            Injective I ∧ Mono b ∧ a ≫ b = (j.app M).f n := by
  let N : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
    CochainComplex.kInjectiveResolutionFunctor C
  let j : 𝟭 (CochainComplex C ℤ) ⟶ N :=
    CochainComplex.toKInjectiveResolution C
  refine ⟨N, j, ?_⟩
  intro M
  have hj := CochainComplex.monoQuasiIso_toKInjectiveResolution_app C M
  let : Mono (j.app M) := hj.1
  refine ⟨?_, hj.2, ?_⟩
  · intro n
    exact (inferInstance : Mono ((j.app M).f n))
  · intro n
    let I : C := (N.obj M).X n
    let a : M.X n ⟶ I := (j.app M).f n
    let b : I ⟶ (N.obj M).X n := 𝟙 I
    have hI : Injective I := by
      dsimp [I, N]
      infer_instance
    have hb : Mono b := by
      dsimp [b]
      infer_instance
    refine ⟨I, a, b, hI, hb, ?_⟩
    simp [I, a, b]

end CochainComplex
