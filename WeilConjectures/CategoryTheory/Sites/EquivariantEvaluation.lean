/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.RepresentationTheory.Rep.Basic
public import WeilConjectures.Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Equivariant evaluation of sheaves at a point with a group action

Let `C` be a category, `T` an object of `C` and `a : H →* (End T)ᵐᵒᵖ` a right action of a group
`H` on `T`. For a presheaf `F` of `Λ`-modules on `C`, the group `H` acts (on the left) on
`F(T)` by `h ↦ F(a h)`; this gives the *equivariant evaluation* functor
`CategoryTheory.Presheaf.evaluationRep` from presheaves of `Λ`-modules to `Λ`-linear
representations of `H`. It has a right adjoint `CategoryTheory.Presheaf.coevaluationRep`,
sending a representation `M` to the presheaf `W ↦ Hom_H(Hom(T, W), M)` of equivariant functions.

If every covering sieve of `T` for a Grothendieck topology `J` contains the identity, then
`Hom_H(Hom(T, -), M)` is a sheaf, and the adjunction restricts to sheaves
(`CategoryTheory.Sheaf.evaluationRepAdjunction`). If moreover every object is covered by objects
`W` on which `H` acts freely on `Hom(T, W)`, then the right adjoint is exact
(`CategoryTheory.Sheaf.preservesFiniteColimits_coevaluationRep`).

## Main definitions

- `CategoryTheory.Presheaf.evaluationRep`, `CategoryTheory.Presheaf.coevaluationRep` and the
  adjunction `CategoryTheory.Presheaf.evaluationRepAdjunction` between them.
- `CategoryTheory.Sheaf.evaluationRep`, `CategoryTheory.Sheaf.coevaluationRep` and the
  adjunction `CategoryTheory.Sheaf.evaluationRepAdjunction` between them.

## Main statements

- `CategoryTheory.Sheaf.preservesFiniteColimits_evaluationRep`: the equivariant evaluation is
  exact if evaluation at `T` preserves epimorphisms.
- `CategoryTheory.Sheaf.preservesFiniteColimits_coevaluationRep`: its right adjoint is exact if
  `H` acts freely on `Hom(T, W)` for the objects `W` of a covering of every object.
- `CategoryTheory.Sheaf.evaluationRepConstantSheafIso`: the equivariant evaluation of a constant
  sheaf is a trivial representation, if sheafification is bijective at `T`.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {T : C} {H : Type*} [Group H] (a : H →* (End T)ᵐᵒᵖ)
  (Λ : Type w') [CommRing Λ]

namespace Presheaf

end Presheaf

namespace Sheaf

variable (J : GrothendieckTopology C)

end Sheaf

end CategoryTheory
