/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift

/-! # Signed shifts of a representative-normalized tensor comparison

Source: Stacks Project, Cohomology on Sites, Tag 07A4; More on Algebra, Tag 0FNH.
(blueprint: lem-weil-pbc-ringed-projection-tensor-shifts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι

-- The pure-unit formula determines naturality of the ordinary comparison.

-- Totalize the ordinary comparison; left-adjoint pullback preserves the coproducts.

@[no_expose] private def fixedFirst
    {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ A) (T' : B × B ⥤ B) (G : A ⥤ B)
    (t : T ⋙ G ⟶ (G.prod G) ⋙ T') (N : A) :
    (Functor.curry.obj T).flip.obj N ⋙ G ⟶
      G ⋙ (Functor.curry.obj T').flip.obj (G.obj N) where
  app M := t.app (M, N)
  naturality {M M'} f := by
    have h := t.naturality (Prod.mkHom f (𝟙 N))
    change G.map (T.map (Prod.mkHom f (𝟙 N))) ≫ _ =
      _ ≫ T'.map (Prod.mkHom (G.map f) (G.map (𝟙 N))) at h
    simpa only [CategoryTheory.Functor.map_id, Functor.comp_map,
      Functor.flip_obj_map, Functor.curry_obj_map_app, Functor.curry_obj_obj_map] using h

@[no_expose] private def fixedSecond
    {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ A) (T' : B × B ⥤ B) (G : A ⥤ B)
    (t : T ⋙ G ⟶ (G.prod G) ⋙ T') (M : A) :
    (Functor.curry.obj T).obj M ⋙ G ⟶
      G ⋙ (Functor.curry.obj T').obj (G.obj M) where
  app N := t.app (M, N)
  naturality {N N'} g := by
    have h := t.naturality (Prod.mkHom (𝟙 M) g)
    change G.map (T.map (Prod.mkHom (𝟙 M) g)) ≫ _ =
      _ ≫ T'.map (Prod.mkHom (G.map (𝟙 M)) (G.map g)) at h
    simpa only [CategoryTheory.Functor.map_id, Functor.comp_map,
      Functor.flip_obj_map, Functor.curry_obj_map_app, Functor.curry_obj_obj_map] using h

-- Fix one resolving argument in the supplied representative isomorphism.

-- Only essential surjectivity is needed; no full-faithfulness theorem is used.

-- Cancel the shift-compatible outer edges of a commutative comparison diagram.

end AlgebraicGeometry.Scheme.ProjectionRestriction
