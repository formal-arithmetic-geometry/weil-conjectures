/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Functorial objectwise injective resolutions -/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace CochainComplex

/-- A functorial injective resolution of objects, indexed in nonnegative degrees.

Source: Stacks Project, Derived Categories, Tag 0141, construction preceding assertion (1).
(blueprint: lem-weil-pbc-functorial-object-resolution).

The construction first replaces the given embedding by its kernel over the zero object,
so that the resulting functor preserves the zero object and zero morphisms.  It then iterates
cokernels of the successive monomorphic embeddings.  Kernel and cokernel universal
properties make all maps functorial, while the retract argument preserves injectivity.
The augmented nonnegative complexes are exact by the kernel--cokernel identities.
-/
theorem exists_functorial_object_injective_resolution
    {C : Type u} [Category.{v} C] [Abelian C]
    (J : C ⥤ C) (η : 𝟭 C ⟶ J)
    (hη : ∀ A : C, Mono (η.app A)) (hJ : ∀ A : C, Injective (J.obj A)) :
    ∃ (E : C ⥤ CochainComplex C ℕ)
      (ε : (CochainComplex.single₀ C) ⟶ E),
      (∀ A : C, QuasiIso (ε.app A)) ∧
      (∀ (A B : C), E.map (0 : A ⟶ B) = 0) ∧
      IsZero (E.obj (0 : C)) ∧
      (∀ (A : C) (n : ℕ), Injective ((E.obj A).X n)) := by
  sorry

end CochainComplex
