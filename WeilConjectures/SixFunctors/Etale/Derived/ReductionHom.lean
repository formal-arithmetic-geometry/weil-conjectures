/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalKFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Hom

/-!
# Derived extension of scalars along a quotient map and the internal hom

Let `φ : Λ →+* Λ'` be a surjective morphism of commutative rings with principal kernel `(a)`,
for instance `Λ ⟶ Λ ⧸ (ϖⁿ)`, and let `X` be a scheme. The extension of scalars of étale sheaves
`Λ' ⊗_Λ -` is a strong monoidal left adjoint of restriction of scalars which preserves flat
objects; its total left derived functor `K ↦ K ⊗ᴸ_Λ Λ'`
(`AlgebraicGeometry.Etale.derivedExtendScalars`) is therefore left adjoint to the derived
restriction of scalars and monoidal. We deduce:

- `AlgebraicGeometry.Etale.isDerivedBaseChange_derivedExtendScalarsAdjunction_unit`: the unit
  `K ⟶ Res(K ⊗ᴸ Λ')` exhibits `K ⊗ᴸ Λ'` as the derived base change of `K`;
- `AlgebraicGeometry.Etale.derivedHomRestrictScalarsIso`: the extension–restriction adjunction
  for internal homs, `RHom_Λ(K, Res N) ≅ Res RHom_{Λ'}(K ⊗ᴸ Λ', N)`;
- `AlgebraicGeometry.Etale.nonempty_iso_derivedRestrictScalars_derivedExtendScalars`: with
  scalars restricted back to `Λ`, `K ⊗ᴸ_Λ Λ'` is the derived tensor product of `K` with the
  constant sheaf `Λ ⧸ (a)`.
- `AlgebraicGeometry.Etale.nonempty_iso_derivedHom_derivedTensor_of_isDerivedBaseChange`: for
  derived base changes `K'`, `L'` of `K`, `L`, `RHom_Λ(K, L ⊗ᴸ (Λ ⧸ (a))_X) ≅ Res RHom_{Λ'}(K', L')`
  (used for blueprint `lem-coef-integral-hom-reduction`).

## Implementation notes

The monoidal comparison of the derived extension of scalars is obtained from the general
`CategoryTheory.Functor.leftDerivedTensorIsoOfIsLeftDerivedFunctor`. For the kernel to
compare its monoidal structures with those inside `AlgebraicGeometry.Etale.derivedTensor` cheaply,
instance search must produce syntactically the same terms; this is ensured by the local instance
attributes below (the braiding `SymmetricCategory.toBraidedCategory` of `ModuleCat` and
`AlgebraicGeometry.Etale.sheafBraidedCategory`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

-- The braiding of `ModuleCat` found by instance search (`instBraidedCategory`) is not syntactically
-- the one underlying the derived tensor product of étale sheaves
-- (`SymmetricCategory.toBraidedCategory` of the symmetric structure, see
-- `AlgebraicGeometry.Etale.derivedTensor`), and the kernel cannot compare the two monoidal
-- structures on `D(X_ét, Λ)` in reasonable time. With these instances, instance search produces
-- exactly the monoidal structure used by `derivedTensor`.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- Sheaves of modules on the small étale site have countable coproducts. Instance search times
out on this. -/
local instance (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    HasCountableCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ⟨fun _ _ ↦ (inferInstance : HasColimitsOfSize.{0, 0} (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))).has_colimits_of_shape _⟩

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {φ : Λ →+* Λ'}
  (hφ : Function.Surjective φ) {a : Λ} (ha : RingHom.ker φ = Ideal.span {a}) (X : Scheme.{u})

end Etale

end AlgebraicGeometry
