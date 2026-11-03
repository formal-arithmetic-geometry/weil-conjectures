/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Data.Finite.Sigma
import Mathlib.CategoryTheory.Subfunctor.Image
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.SimplicialMatchingObject
import WeilConjectures.CategoryTheory.ProperFaceMatchingObject

/-! Intermediate degree component for `lem-weil-pbc-hypercover-free-resolution`. -/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SplitEtaleHypercover
/-- This is the degree-positive component of the hypercover free resolution.
Source: Stacks Project, Hypercoverings, Tags 01GC, 01GD, 01GE and 01GW.
(blueprint: lem-weil-pbc-hypercover-free-module-positive)

The full resolution is obtained by assembling these degree components with
`quasiIso_iff`; the present theorem records only the indicated component. -/
theorem hypercover_freeModule_quasiIsoAt_pos
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X) (R : Type (w + 1)) [CommRing R] :
    let e := (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj X.Etale _
        (uliftYoneda.{w + 1} ⋙
          (Functor.whiskeringRight X.Etaleᵒᵖ (Type (w + 1)) (ModuleCat.{w + 1} R)).obj
            (ModuleCat.free R) ⋙
          presheafToSheaf X.smallEtaleTopology (ModuleCat.{w + 1} R))).obj
        (U.simplicial.augmentOfIsTerminal (terminalIsTerminal (C := X.Etale)))));
    ∀ i : ℕ, 0 < i → QuasiIsoAt e i := by
  sorry

end AlgebraicGeometry.SplitEtaleHypercover
