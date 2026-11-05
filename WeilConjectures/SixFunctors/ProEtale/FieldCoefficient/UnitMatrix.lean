/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix

/-!
# Morphisms of finite free `Λ_V`-modules as matrices of functions

This is the counterpart, for a coefficient field `Λ` with an ultrametric norm (the case of
interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

An endomorphism `ψ` of the unit module `Λ_V` is multiplication by the continuous
function `AlgebraicGeometry.ProEtale.FieldSheaf.unitEndFun ψ` on `V`, the image of `1`
(`AlgebraicGeometry.ProEtale.fieldConstantSheaf_app_eq_mul`); conversely every such function `a`
gives the endomorphism `AlgebraicGeometry.ProEtale.FieldSheaf.unitMul a`. Composition corresponds to
multiplication. Consequently a morphism `Λ_Vⁿ ⟶ Λ_Vᵐ` is the same as an `m × n` matrix of
functions (`AlgebraicGeometry.ProEtale.FieldSheaf.unitMatrix`,
`AlgebraicGeometry.ProEtale.FieldSheaf.ofUnitMatrix`), compatibly with composition.

For a weakly étale `g : W ⟶ V`, pulling back an endomorphism of `Λ_V` pulls back its function
along `g` (`AlgebraicGeometry.ProEtale.fieldConstantSheafEndFun_fieldUpperStar`): on sections the
comparison `g^* Λ_V ≅ Λ_W` is the identity (`AlgebraicGeometry.ProEtale.
upperStarIsoLocalizationRestriction_inv_app_comp_fieldUpperStarUnitIso`).
-/

@[expose] public section

universe w

open PadicAlgCl (sumComplEquiv sumComplEquiv_symm_inl)

namespace AlgebraicGeometry

variable {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ] {T : Type*} [TopologicalSpace T]

section ConstantRank

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

end ConstantRank

end AlgebraicGeometry

open CategoryTheory MonoidalCategory Limits Opposite Functor.LaxMonoidal

universe u

open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ] {V : Scheme.{u}}

section Restriction

variable {W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g)

end Restriction

namespace FieldSheaf

end FieldSheaf

namespace FieldSheaf

attribute [local instance] Abelian.hasFiniteBiproducts

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

end FieldSheaf

namespace FieldSheaf

attribute [local instance] Abelian.hasFiniteBiproducts

variable {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

section Block

variable [DecidableEq ι] [DecidableEq κ] {r : ℕ} (ρ : Fin r → κ) (γ : Fin r → ι)
  (hρ : Function.Injective ρ) (hγ : Function.Injective γ)

end Block

end FieldSheaf

namespace FieldSheaf

attribute [local instance] Abelian.hasFiniteBiproducts

variable {ι κ : Type} [Fintype ι] [Fintype κ] {W : Scheme.{u}}

end FieldSheaf

end AlgebraicGeometry.ProEtale
