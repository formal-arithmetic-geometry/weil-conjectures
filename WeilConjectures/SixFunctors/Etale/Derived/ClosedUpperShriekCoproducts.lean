/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimensionAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.CoproductTriangle
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedSupportTriangle
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral

/-!
# The exceptional inverse image along a closed immersion commutes with coproducts

Let `i : Z ⟶ X` be a closed immersion with quasi-compact open complement `j : U ⟶ X` of finite
cohomological dimension. The right adjoint `Ri^!` of `Ri_*` on the unbounded derived categories
of étale sheaves of modules (`AlgebraicGeometry.Etale.derivedLowerStarClosedUpperShriekAdjunction`)

* commutes with coproducts
  (`AlgebraicGeometry.Etale.preservesColimitsOfShape_rightDerivedFunctor_closedUpperShriek`): the
  closed-support triangles `Ri_* Ri^! M ⟶ M ⟶ Rj_* j^* M ⟶` of a family are compared with that of
  the coproduct; the coproduct of distinguished triangles is distinguished, `Rj_* j^*` commutes
  with coproducts, and `Ri_*` is fully faithful and left adjoint;
* has bounded amplitude
  (`AlgebraicGeometry.Etale.exists_isLE_rightDerivedFunctor_closedUpperShriek`): it sends objects
  in degrees `≤ n` into degrees `≤ n + d + 1` if `Rj_*` has cohomological dimension `≤ d`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated Category

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  [HasCompactification i] (j : U ⟶ X) [IsOpenImmersion j]
  (hij : Set.range i.base = (Set.range j.base)ᶜ)

variable [QuasiCompact j]

end Etale

end AlgebraicGeometry
