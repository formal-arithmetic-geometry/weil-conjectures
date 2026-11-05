/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic

/-!
# Extension of scalars from `ℤ_ℓ,X`-modules to `ℚ̄_ℓ,X`-modules

On the small pro-étale site of a scheme `X`, the inclusion `ℤ_ℓ ⟶ ℚ̄_ℓ` induces a morphism of
commutative ring objects of abelian sheaves `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X`
(`AlgebraicGeometry.ProEtale.padicIntSheafToPadicAlgClSheaf`), where `ℚ̄_ℓ,X` is the ring object
`AlgebraicGeometry.ProEtale.padicAlgClSheaf`, isomorphic as an abelian sheaf to the unit
`adicConstantSheaf` of the `ℓ`-adic sheaves (`padicAlgClSheafIsoAdicConstantSheaf`). Extension of
scalars along it, `M ↦ ℚ̄_ℓ,X ⊗_{ℤ_ℓ,X} M`, is left adjoint to restriction of scalars
(`AlgebraicGeometry.ProEtale.padicIntExtendRestrictAdjunction`): this is the rationalisation of
integral lattices `lim_n Fₙ` of lisse sheaves.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

end AlgebraicGeometry.ProEtale
