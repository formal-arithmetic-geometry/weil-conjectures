/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# The restriction of scalars is lax braided, and monoidal along a bijection

Let `f : R →+* S` be a morphism of commutative rings. Mathlib knows that the functor
`ModuleCat.restrictScalars f : ModuleCat S ⥤ ModuleCat R` is lax monoidal. As the
monoidal categories `ModuleCat R` and `ModuleCat S` are symmetric, we upgrade this to
a lax braided (i.e. lax symmetric monoidal) structure.

When moreover `f` is bijective, the lax monoidal structure is strong: its structure maps are
`ε = f`, which is bijective, and the canonical map `M ⊗[R] N ⟶ M ⊗[S] N`, which is bijective
because `S` acts on `M` and on `N` through `f`. The monoidal structure produced below is built
from Mathlib's lax monoidal structure by inverting these two maps, so that `restrictScalars_η`
and `restrictScalars_μ_tmul` describe its structure maps.

## Main declarations

* `ModuleCat.restrictScalarsLaxBraided`: `ModuleCat.restrictScalars f` is lax braided.
* `ModuleCat.restrictScalarsMonoidalOfBijective`: for `f` bijective,
  `ModuleCat.restrictScalars f` is monoidal.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

open ModuleCat.MonoidalCategory in
/-- The restriction of scalars along a morphism of commutative rings is lax braided: the
structure map `μ` sends `m₁ ⊗ₜ m₂` to `m₁ ⊗ₜ m₂`, hence commutes with the symmetry which
exchanges the two factors. -/
noncomputable instance restrictScalarsLaxBraided : (restrictScalars f).LaxBraided where
  braided M N := tensor_ext fun m n ↦ by simp

/-- **The restriction of scalars along a bijective morphism of commutative rings is monoidal.**
Its structure map `ε` is `f` itself, and its structure map `μ` is the canonical map
`M ⊗[R] N ⟶ M ⊗[S] N`, which is bijective because `R` acts on `M` and on `N` through `f`.

This is Mathlib's lax monoidal structure with these two maps inverted, so that
`ModuleCat.restrictScalars_η` and `ModuleCat.restrictScalars_μ_tmul` compute its structure
maps. -/
@[instance_reducible]
noncomputable def restrictScalarsMonoidalOfBijective (hf : Function.Bijective f) :
    (restrictScalars f : ModuleCat.{u} S ⥤ ModuleCat.{u} R).Monoidal :=
  haveI : IsIso (ε (restrictScalars f)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    have : ⇑(ConcreteCategory.hom (ε (restrictScalars f))) = ⇑f := funext (restrictScalars_η f)
    rw [this]
    exact hf
  haveI : ∀ M N : ModuleCat.{u} S, IsIso (μ (restrictScalars f) M N) := fun M N ↦ by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine Function.bijective_iff_has_inverse.2
      ⟨TensorProduct.liftAddHom (R := S) (M := M) (N := N)
        (P := TensorProduct R ((restrictScalars f).obj M) ((restrictScalars f).obj N))
        { toFun := fun m ↦
            (TensorProduct.mk R ((restrictScalars f).obj M)
              ((restrictScalars f).obj N) m).toAddMonoidHom
          map_zero' := by ext n; simp
          map_add' := fun m₁ m₂ ↦ by ext n; simp }
        (fun s m n ↦ by
          obtain ⟨r, rfl⟩ := hf.surjective s
          exact TensorProduct.smul_tmul (R := R) (M := (restrictScalars f).obj M)
            (N := (restrictScalars f).obj N) r m n), ?_, ?_⟩
    · intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul m n => simp only [restrictScalars_μ_tmul]; rfl
      | add x y hx hy => simp [hx, hy]
    · intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul m n => exact restrictScalars_μ_tmul f M N m n
      | add x y hx hy => simp [hx, hy]
  .ofLaxMonoidal _

end ModuleCat
