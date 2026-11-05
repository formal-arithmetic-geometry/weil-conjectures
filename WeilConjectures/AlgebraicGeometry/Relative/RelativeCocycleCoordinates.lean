/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeEtaleCohomology
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.CategoryTheory.Preadditive.Comma
public import WeilConjectures.CategoryTheory.Sites.FramedLift.FramedLifts
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Coordinates on relative degree-one cocycles

Source: Stacks Project, Tag 03AJ, relative injective-resolution refinement, step 2.
(blueprint: lem-amb-relative-cocycle-coordinates).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

variable (T : Scheme.{u}) (U : T.Etale)
  (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)

variable {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
  (R : InjectiveResolution G)

section Maps

variable {T' : Scheme.{u}} (U' : T'.Etale)
  (J : CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
  (α : (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
      I) ⟶ (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T'))).mapHomologicalComplex (.up ℕ)).obj
      J))
  (β : (((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I) ⟶
      (((etaleSectionFunctor U').mapHomologicalComplex (.up ℕ)).obj J))
  (h : HomologicalComplex.extendMap α ComplexShape.embeddingUpNat ≫
      relativeSectionRestriction T' U' J =
    relativeSectionRestriction T U I ≫
      HomologicalComplex.extendMap β ComplexShape.embeddingUpNat)

end Maps

end AlgebraicGeometry.Etale

-- Check the axioms of the completed construction.
