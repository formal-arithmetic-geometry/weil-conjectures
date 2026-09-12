/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# The restriction of scalars is lax braided, and monoidal along an isomorphism

Let `f : R →+* S` be a morphism of commutative rings. Mathlib knows that the functor
`ModuleCat.restrictScalars f : ModuleCat S ⥤ ModuleCat R` is lax monoidal. As the
monoidal categories `ModuleCat R` and `ModuleCat S` are symmetric, we upgrade this to
a lax braided (i.e. lax symmetric monoidal) structure.

When moreover `f` is bijective, the extension and the restriction of scalars along `f` are
quasi-inverse equivalences of categories, and the restriction of scalars is monoidal: the
canonical map `M ⊗[R] N ⟶ M ⊗[S] N` is then an isomorphism.

## Main declarations

* `ModuleCat.restrictScalarsLaxBraided`: `ModuleCat.restrictScalars f` is lax braided.
* `ModuleCat.restrictScalarsMonoidal`: for `f` bijective, `ModuleCat.restrictScalars f` is
  monoidal.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

open ModuleCat.MonoidalCategory in
/-- The restriction of scalars along a morphism of commutative rings is lax braided: the
structure map `μ` sends `m₁ ⊗ₜ m₂` to `m₁ ⊗ₜ m₂`, hence commutes with the symmetry which
exchanges the two factors. -/
noncomputable instance restrictScalarsLaxBraided : (restrictScalars f).LaxBraided where
  braided M N := tensor_ext fun m n ↦ by simp

section Bijective

variable (hf : Function.Bijective f)

include hf

lemma isEquivalence_restrictScalars : (restrictScalars.{u, u, u} f).IsEquivalence :=
  restrictScalars_isEquivalence_of_ringEquiv (RingEquiv.ofBijective f hf)

lemma isEquivalence_extendScalars : (extendScalars.{u, u, u} f).IsEquivalence := by
  have := isEquivalence_restrictScalars f hf
  exact Functor.isEquivalence_of_iso
    ((extendRestrictScalarsAdj.{u, u, u} f).leftAdjointUniq
      (restrictScalars.{u, u, u} f).asEquivalence.symm.toAdjunction).symm

/-- The restriction of scalars along a bijective morphism of commutative rings is monoidal:
the canonical map `M ⊗[R] N ⟶ M ⊗[S] N` is an isomorphism. -/
@[instance_reducible]
noncomputable def restrictScalarsMonoidal : (restrictScalars.{u, u, u} f).Monoidal :=
  have := isEquivalence_restrictScalars f hf
  have := isEquivalence_extendScalars f hf
  letI : ((extendRestrictScalarsAdj.{u, u, u} f).toEquivalence).functor.Monoidal :=
    inferInstanceAs (extendScalars.{u, u, u} f).Monoidal
  ((extendRestrictScalarsAdj.{u, u, u} f).toEquivalence).inverseMonoidal

end Bijective

end ModuleCat
