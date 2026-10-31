/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.SmoothPurity.EtaleTorsorExtensionPresentationExists
import WeilConjectures.AlgebraicGeometry.Curve.ExtensionPresentationShortExact
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! # Relative extensions of a torsor

Source: Stacks Project, Tags 03AJ and 0A45. The quotient of the free torsor
extension by the prescribed lift on an open subset gives the relative class.
(blueprint: lem-sp-relative-torsor-extension). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ShortComplex

end CategoryTheory.ShortComplex

namespace CategoryTheory.Sheaf.Torsor
open AlgebraicGeometry Abelian

private abbrev integral (X : Scheme.{u}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

private def one (X : Scheme.{u}) (U : X.Etaleᵒᵖ) : (integral X).obj.obj U :=
  (toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U ⟨1⟩

end CategoryTheory.Sheaf.Torsor
