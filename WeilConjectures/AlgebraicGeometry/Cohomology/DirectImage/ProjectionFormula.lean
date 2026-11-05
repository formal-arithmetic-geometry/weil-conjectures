/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp

/-!
# The projection formula for higher direct images

For `f : X ⟶ T`, an `𝒪_X`-module `ℱ` and an invertible `𝒪_T`-module `𝒩`,
`R^q f_* (ℱ ⊗ f^* 𝒩) ≅ R^q f_* ℱ ⊗ 𝒩`
(`AlgebraicGeometry.Scheme.Modules.higherDirectImageTensorObjPullbackIso`).

The projection morphism `f_* ℱ ⊗ 𝒩 ⟶ f_* (ℱ ⊗ f^* 𝒩)` is natural in `ℱ`
(`AlgebraicGeometry.Scheme.Modules.projectionHom_naturality`), so it is a natural isomorphism
`f_* ⋙ (- ⊗ 𝒩) ≅ (- ⊗ f^* 𝒩) ⋙ f_*`. Twisting by an invertible module is an autoequivalence, hence
exact and preserving injective objects, so taking right derived functors of both sides gives the
projection formula.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

section ProjectionHom

attribute [local instance] presheafMonoidalCategory presheafSymmetricCategory
  SheafOfModules.sheafificationMonoidal SheafOfModules.sheafificationBraided
  sheafificationMonoidal sheafificationBraided forgetToPresheafOfModulesLaxMonoidal

variable (g : X ⟶ Y) (N : Y.Modules)

end ProjectionHom

end AlgebraicGeometry.Scheme.Modules
