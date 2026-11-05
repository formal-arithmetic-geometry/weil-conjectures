/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Retract
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux
import WeilConjectures.AlgebraicGeometry.DerivedTensorRightCoproducts
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh
import WeilConjectures.AlgebraicGeometry.DerivedTensorQCohClosure
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-! # Closure of the affine projection-mate locus

Source: Stacks Project, Tag 08EU.
(blueprint: lem-pc-qcqs-projection-mate-affine-locus).
-/

@[expose] public section

universe u w wA
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

variable (A : Type u) [CommRing A]
  [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
  (X : Scheme.{u})
  [CompactSpace X] [QuasiSeparatedSpace X]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
  (f : X ⟶ Spec (.of A)) [QuasiCompact f] [QuasiSeparated f]
  (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
  (t : tensor (schemeDerivedCategory (Spec (.of A))) ⋙ derivedPullback f ≅
    (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
  (L : schemeDerivedQCohCategory X)
  (e : DerivedCategory (ModuleCat.{u} A) ≌ schemeDerivedQCohCategory (Spec (.of A)))

-- Keep the existing compactness and quasi-separatedness binders in the public signature.

end AlgebraicGeometry
