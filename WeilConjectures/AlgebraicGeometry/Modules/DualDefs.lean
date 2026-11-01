/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-!
# The internal hom and the dual of sheaves of modules on a scheme

For sheaves of modules `M` and `N` on a scheme `X`, `Hom(M, N)` is the internal hom sheaf
`U ↦ Hom_{𝒪_U}(M|_U, N|_U)`, and the dual of `M` is `M^∨ = Hom(M, 𝒪_X)`. This file only
contains the definitions; their properties are in `WeilConjectures.AlgebraicGeometry.Modules.Dual`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.homObj`: the internal hom `Hom(M, N)`.
- `AlgebraicGeometry.Scheme.Modules.dual`: the dual `M^∨ = Hom(M, 𝒪_X)`, with notation `Mᵛ`.
- `AlgebraicGeometry.Scheme.Modules.dualMap`: the transpose `Nᵛ ⟶ Mᵛ` of `f : M ⟶ N`.
- `AlgebraicGeometry.Scheme.Modules.dualFunctor`: `M ↦ Mᵛ` as a contravariant functor.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The internal hom `Hom(M, N)` of sheaves of modules on a scheme, the sheaf of modules
`U ↦ Hom_{𝒪_U}(M|_U, N|_U)`. -/
noncomputable abbrev homObj (M N : X.Modules) : X.Modules :=
  SheafOfModules.homObj (R := X.sheaf) M N

/-- The dual `M^∨ = Hom(M, 𝒪_X)` of a sheaf of modules on a scheme. -/
noncomputable abbrev dual (M : X.Modules) : X.Modules :=
  homObj M (SheafOfModules.unit _)

@[inherit_doc] scoped postfix:max "ᵛ" => AlgebraicGeometry.Scheme.Modules.dual

/-- The transpose `Nᵛ ⟶ Mᵛ` of a morphism `f : M ⟶ N` of sheaves of modules on a scheme. -/
noncomputable abbrev dualMap {M N : X.Modules} (f : M ⟶ N) : Nᵛ ⟶ Mᵛ :=
  SheafOfModules.homObjMap (R := X.sheaf) f (𝟙 _)

variable (X) in
/-- The dual `M ↦ Mᵛ` as a contravariant functor on sheaves of modules on a scheme. -/
noncomputable abbrev dualFunctor : X.Modulesᵒᵖ ⥤ X.Modules :=
  (SheafOfModules.homFunctor X.sheaf).flip.obj (SheafOfModules.unit _)

end AlgebraicGeometry.Scheme.Modules
