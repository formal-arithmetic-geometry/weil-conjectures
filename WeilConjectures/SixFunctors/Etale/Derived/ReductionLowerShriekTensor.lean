/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ReductionHom
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.TensorSingle

/-!
# The reduction of coefficients as a tensor product

Let `ρ : Λ →+* Λ'` be a surjective morphism of commutative rings with principal kernel and
`Ψ = - ⊗ᴸ_Λ Λ'` the derived extension of scalars. With scalars restricted back to `Λ`, `Ψ` is the
derived tensor product with the constant sheaf `(Λ ⧸ ker ρ)_X`: both are left derived functors of
`P ↦ P ⊗ (Λ ⧸ ker ρ)_X ≅ Res(Λ' ⊗_Λ P)` (`CategoryTheory.Sheaf.extendScalarsCompRestrictScalarsQuotientIso`),
whence a natural isomorphism `K ⊗ᴸ (Λ ⧸ ker ρ)_X ≅ Res Ψ K`
(`AlgebraicGeometry.Etale.derivedExtendScalarsTensorIso'`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

set_option hygiene false in
/-- The homotopy category `K(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐊(" X ", " Λ ")" =>
  HomotopyCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ)

/-- The small étale site of a scheme is essentially small. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a}) (X : Scheme.{u})

instance : (Sheaf.extendScalars X.smallEtaleTopology ρ).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

variable (ρ) in
/-- The constant sheaf `(Λ ⧸ ker ρ)_X`. -/
noncomputable abbrev quotientConstantSheaf : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (ModuleCat.of Λ (Λ ⧸ RingHom.ker ρ))

variable (ρ) in
/-- The constant sheaf `(Λ ⧸ ker ρ)_X` placed in degree `0`, in the homotopy category. -/
noncomputable abbrev quotientConstantHomotopy : 𝐊(X, Λ) :=
  (HomotopyCategory.quotient _ _).obj
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (quotientConstantSheaf ρ X))

/-- On complexes, `Res(Λ' ⊗_Λ -)` is the tensor product with `(Λ ⧸ ker ρ)_X` placed in degree `0`. -/
noncomputable def extendScalarsRestrictScalarsComplexIso :
    (Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      tensorRight ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (quotientConstantSheaf ρ X)) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl _) _ ≪≫
    NatIso.mapHomologicalComplex
      (Sheaf.extendScalarsCompRestrictScalarsQuotientIso X.smallEtaleTopology hρ ha) _ ≪≫
    (CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor _)
      (quotientConstantSheaf ρ X)).symm



end AlgebraicGeometry.Etale
