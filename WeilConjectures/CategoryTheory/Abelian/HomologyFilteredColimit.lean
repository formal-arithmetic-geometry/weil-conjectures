/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Homology commutes with exact colimits

In an abelian category `C` in which colimits of shape `J` are exact, the homology functors of
cochain complexes commute with colimits of shape `J`
(`HomologicalComplex.preservesColimitsOfShape_homologyFunctor`).

We also record two facts on natural transformations and colimits:

- `CategoryTheory.NatTrans.isIso_app_of_isColimit_mapCocone`: a natural transformation
  `τ : P ⟶ R` between
  functors preserving a colimit cocone `c` is an isomorphism at its point as soon as it is an
  isomorphism at all objects of the diagram;
- `CategoryTheory.Limits.isColimitMapCoconeOfNatTrans`: if `β : P ⟶ R` is an isomorphism at all
  objects of a cocone `c` and its diagram, then `P` maps `c` to a colimit cocone as soon as `R`
  does.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace HomologicalComplex

variable (C : Type*) [Category* C] [Abelian C] (J : Type w) [Category.{v} J]
  [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]

end HomologicalComplex

namespace CategoryTheory

variable {C D J : Type*} [Category* C] [Category* D] [Category* J] {P R : C ⥤ D}

end CategoryTheory
