/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Adjunction.Basic

import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Additivity and linearity of a right adjoint

Source: Stacks Project, Tags 09MJ and 09MK, `dga.tex`,
`definition-linear-category` and `definition-functor-linear-categories`, and the
ordinary-adjunction counit calculation in the node (blueprint: lem-sbc-linear-right-adjoint).
-/

@[expose] public section

set_option autoImplicit false

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory.Adjunction

/-- A right adjoint to an additive `A`-linear functor is additive and `A`-linear.

Source: Stacks Project, Tags 09MJ and 09MK, `dga.tex`,
`definition-linear-category` and `definition-functor-linear-categories`; agent counit
refinement (blueprint: lem-sbc-linear-right-adjoint).

Proof: Write `ψ` for the inverse ordinary adjunction bijection, and define the counit
`ε_Y = ψ (𝟙 (G.obj Y))`. Naturality in the source gives
`ψ(h) = F.map h ≫ ε_Y`; naturality in the target gives
`ψ(G.map s) = ε_Y ≫ s`. The maps `ψ` are injective because they are bijections.
For parallel arrows `s,t : Y ⟶ Z`, preadditive bilinearity and additivity of `F` give
`ψ(G.map (s + t)) = ε_Y ≫ (s + t) = ε_Y ≫ s + ε_Y ≫ t`
`= F.map (G.map s) ≫ ε_Z + F.map (G.map t) ≫ ε_Z`
`= F.map (G.map s + G.map t) ≫ ε_Z = ψ(G.map s + G.map t)`.
Injectivity yields additivity. For `a : A`, bilinearity and linearity of `F` similarly give
`ψ(G.map (a • s)) = ε_Y ≫ (a • s) = a • (ε_Y ≫ s)`
`= a • (F.map (G.map s) ≫ ε_Z) = F.map (a • G.map s) ≫ ε_Z`
`= ψ(a • G.map s)`. Injectivity yields scalar linearity. These calculations use only the
ordinary adjunction and the two linear-category and linear-functor definitions; they need
no additivity or linearity assumption on the Hom bijections or on `G`.
-/
theorem right_adjoint_additive_linear
    {A : Type w} [CommRing A] {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] [Preadditive C] [Preadditive D]
    [Linear A C] [Linear A D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) [F.Additive] [F.Linear A] : G.Additive ∧ G.Linear A := by
  exact ⟨adj.right_adjoint_additive, adj.right_adjoint_linear⟩

end CategoryTheory.Adjunction
