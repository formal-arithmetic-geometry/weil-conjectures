/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Objects of a derived category with homology in a single degree

An object of `D(C)` whose homology objects vanish in every degree but `n` is the single complex
on its `n`-th homology object, placed in degree `n`.

## Main statements

- `DerivedCategory.nonempty_iso_singleFunctor_obj_homologyFunctor_obj`
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Blueprint `lem-pur-concentrated-complex-shift`: Complexes with cohomology in a single degree

*Concentration in one degree.* If the homology objects `H^i(K)` vanish for every `i ≠ n`, then
the truncation triangles identify `K` with `H^n(K)[-n]`, the object `H^n(K)` placed in
degree `n`. -/
theorem nonempty_iso_singleFunctor_obj_homologyFunctor_obj (K : DerivedCategory C) (n : ℤ)
    (hK : ∀ i, i ≠ n → IsZero ((homologyFunctor C i).obj K)) :
    Nonempty (K ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj K)) := by
  have : K.IsGE n := (isGE_iff K n).2 fun i hi ↦ hK i hi.ne
  have : K.IsLE n := (isLE_iff K n).2 fun i hi ↦ hK i hi.ne'
  obtain ⟨Y, ⟨e⟩⟩ := K.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  exact ⟨e ≪≫ (singleFunctor C n).mapIso
    (((singleFunctorCompHomologyFunctorIso C n).app Y).symm ≪≫ (homologyFunctor C n).mapIso e.symm)⟩

end DerivedCategory
