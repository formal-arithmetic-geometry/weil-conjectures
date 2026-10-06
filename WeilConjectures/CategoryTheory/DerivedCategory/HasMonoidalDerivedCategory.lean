/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Monoidal.Linear
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory

/-!

# The monoidal structure on the derived category of a monoidal Grothendieck abelian category

The K-flat machinery migrated from mathlib PR #25848 equips the derived category
`DerivedCategory A` with a monoidal structure as soon as the localization functor
`Qh : K(A) ⥤ D(A)` satisfies `Functor.HasDerivedMonoidalCategory` with respect to
quasi-isomorphisms; see `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`.

Verifying that hypothesis by hand at every use site is impractical, because it is phrased in
terms of the derived bifunctor, trifunctors and quadrifunctor of the tensor product. This
file packages it once and for all as an instance, deduced from conditions that are
checkable in practice:

* `A` is a monoidal Grothendieck abelian category (`IsGrothendieckAbelian`,
  `MonoidalCategory`, `MonoidalPreadditive`, `BraidedCategory`);
* the tensor product is closed (`MonoidalClosed`), so that `- ⊗ X` and `X ⊗ -` are left
  adjoints and hence preserve all colimits;
* `A` admits functorial flat resolutions (`Abelian.HasFunctorialFlatResolution`).

Together these give the K-flat left derivability structure, which is what
`CategoryTheory.MorphismProperty.kFlat_derivesMonoidal` turns into
`Functor.HasDerivedMonoidalCategory`. The file also records that the resulting derived tensor
product is additive, and `Λ`-linear if the tensor product of `A` is, in each variable.

## Main results

- `DerivedCategory.hasDerivedMonoidalCategory` : the instance
  `Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso A (.up ℤ))`, from which
  `MonoidalCategory (DerivedCategory A)` follows by
  `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`.
- `DerivedCategory.monoidalPreadditive`, `DerivedCategory.monoidalLinear`: the derived tensor
  product is additive, and `Λ`-linear if the tensor product of `A` is, in each variable.

## TODO

The proofs are currently `sorry`.

`hasDerivedMonoidalCategory` should go through the K-flat route already available in
`WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`: the hypotheses above give
`(HomotopyCategory.quasiIso A (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure`
(this part is already proved, in `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat`),
and the instance `CategoryTheory.MorphismProperty.instHasDerivedMonoidalCategory` then applies.
What remains is to discharge the ambient graded-object and colimit side conditions from
`MonoidalClosed A` and `IsGrothendieckAbelian A` rather than assuming them.

`monoidalLinear` should be proved on K-flat representatives. Since `r • f = f ≫ (r • 𝟙 _)`, it
suffices that `(r • 𝟙 K) ▷ L = r • 𝟙 (K ⊗ᴸ L)` and symmetrically. By
`isLeftDerivedFunctor₂CurriedTensor`, on K-flat complexes `K ⊗ᴸ -` is the localization of the
tensor product of complexes, which is `Λ`-linear by `MonoidalLinear Λ A`, and `DerivedCategory.Qh`
is `Λ`-linear. `monoidalPreadditive` is the same argument with `ℤ` in place of `Λ`; once
`monoidalLinear` is proved it follows directly, although Mathlib has no general instance
`MonoidalLinear ℤ C → MonoidalPreadditive C`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

variable (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{w} A] [Abelian.HasFunctorialFlatResolution A]

/-- For a monoidal closed Grothendieck abelian category `A` admitting functorial flat
resolutions, the localization functor `Qh : K(A) ⥤ D(A)` admits a derived monoidal
structure with respect to quasi-isomorphisms. Consequently `DerivedCategory A` is monoidal,
with tensor product the derived tensor product `- ⊗ᴸ -`. -/
instance hasDerivedMonoidalCategory :
    Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  sorry

/-- The derived tensor product is additive in each variable. -/
instance monoidalPreadditive : MonoidalPreadditive (DerivedCategory A) :=
  -- Proof sketch: on K-flat complexes, `K ⊗ᴸ -` is the localization of the tensor product of
  -- complexes, which is additive by `MonoidalPreadditive A`, and `Qh` is additive.
  -- See the TODO in the module docstring.
  sorry

/-- If the tensor product of `A` is `Λ`-linear in each variable, so is the derived tensor
product on `D(A)`. -/
instance monoidalLinear (Λ : Type*) [Ring Λ] [Linear Λ A] [MonoidalLinear Λ A] :
    MonoidalLinear Λ (DerivedCategory A) :=
  -- Proof sketch: it suffices that `(r • 𝟙 K) ▷ L = r • 𝟙 (K ⊗ᴸ L)` and symmetrically, which
  -- holds on K-flat representatives, where `⊗ᴸ` is the localization of the `Λ`-linear tensor
  -- product of complexes. See the TODO in the module docstring.
  sorry

end DerivedCategory
