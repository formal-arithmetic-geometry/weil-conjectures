/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.CategoryTheory.HomColimitExtension
import all Mathlib.CategoryTheory.Triangulated.Pretriangulated
import all Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all Mathlib.Algebra.Category.Grp.Colimits
import all Mathlib.CategoryTheory.Filtered.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all Mathlib.CategoryTheory.Triangulated.Yoneda
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartGeneration

/-!
# Devissage for continuity of derived Hom

Source: blueprint main-20261015, sec-six-functors-basics/
sk-lem-constructible-ext-continuity/sk-lem-constructible-ext-continuity-devissage.md
(blueprint: det-lem-constructible-ext-continuity-devissage).

The comparison is built from the actual cocone by the abelian-group colimit universal
property. The formal assertion imposes no boundedness condition. The final assertion uses
finite constant-model constructibility and the specified two field coefficient rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v t a

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
