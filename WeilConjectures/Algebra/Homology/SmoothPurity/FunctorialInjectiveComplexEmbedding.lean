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

## References

* Stacks Project, Injectives, functorial injective embeddings
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CochainComplex

/-- In a Grothendieck abelian category there is a functorial termwise monomorphic
quasi-isomorphism into a complex, factoring in each degree through an injective subobject.
The subobject is represented by the monomorphism `b` from the injective object `I`. -/
theorem exists_functorial_injective_complex_embedding
    (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C] :
    ∃ (N : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
      (j : 𝟭 (CochainComplex C ℤ) ⟶ N),
      ∀ (M : CochainComplex C ℤ),
        (∀ (n : ℤ), Mono ((j.app M).f n)) ∧ QuasiIso (j.app M) ∧
          ∀ (n : ℤ), ∃ (I : C) (a : M.X n ⟶ I) (b : I ⟶ (N.obj M).X n),
            Injective I ∧ Mono b ∧ a ≫ b = (j.app M).f n :=
  ⟨kInjectiveResolutionFunctor.{v} C, toKInjectiveResolution.{v} C, fun M ↦
    have h := monoQuasiIso_toKInjectiveResolution_app.{v} C M
    have := h.1
    ⟨fun _ ↦ inferInstance, h.2, fun _ ↦
      ⟨_, _, 𝟙 _, inferInstance, inferInstance, Category.comp_id _⟩⟩⟩

end CochainComplex
