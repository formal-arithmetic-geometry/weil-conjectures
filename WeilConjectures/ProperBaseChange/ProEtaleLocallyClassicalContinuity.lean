/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Data.Finite.Prod

/-!
# Continuity of locally classical pro-etale sheaves

Source: Bhatt--Scholze, Lemma 5.1.4. The finite-presieve argument generalizes
`WeilConjectures.CategoryTheory.FinitePresieveFilteredColimit` to a locally small
site whose objects and section sets lie in the next universe.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory Opposite

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false in
private abbrev restriction (X : Scheme.{u}) (U : X.ProEt) :=
  @Functor.sheafPushforwardContinuous U.left.ProEt _ X.ProEt _
    (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop)
    (Type (u + 1)) _ (ProEt.topology U.left) (ProEt.topology X)
    (ProEt.isContinuous_overMap U.prop)

end AlgebraicGeometry.Scheme
