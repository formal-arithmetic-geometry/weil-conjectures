/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.RingTheory.FiniteType
import WeilConjectures.ConstructibleSheaf.DenseOpenUnit
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import Mathlib.AlgebraicGeometry.Artinian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportBaseChangeQcqs
import WeilConjectures.AlgebraicGeometry.Good.GoodCurvesPreimageConstructible
import WeilConjectures.AlgebraicGeometry.Good.GoodCurvesGenericDiagram
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleSurjectivePullback
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteShriekConstructible
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportOpenClosedTriangle
import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothCurvesFiniteModule
import WeilConjectures.AlgebraicGeometry.Etale.EtaleShriekQcqsComposition
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# Constructible compact support for constant finite coefficients on affine smooth curves

Source: Stacks Project, Tag 0GKX, `lemma-constant-shriek-rel-dim-1`, specialized to
finite commutative coefficients and affine bases of finite type over the integers.
(blueprint: lem-weil-pbc-etale-constant-shriek-rel-dim-1)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
