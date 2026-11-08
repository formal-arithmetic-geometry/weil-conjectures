/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Submission.WeilConjectures.AlgebraicGeometry.ObjectCohomologyPresheafResolution

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Object cohomology stalks and section complexes

Source: Stacks Project, Cohomology on Sites, Tag 03F3; Etale Cohomology, Tag 09AX.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

/-- Evaluate an etale sheaf on the given open objects and take its Zariski stalk. 
(blueprint: lem-weil-pbc-etale-object-cohomology-stalk-complex)
-/
noncomputable abbrev etaleObjectStalkSections
    (X : Scheme.{u + 1}) (i : X.Opens ⥤ X.Etale) (x : X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
      ((OpenNhds.inclusion (X := X.toLocallyRingedSpace.toTopCat) x) ⋙ i).op ⋙
        colim

instance (X : Scheme.{u + 1}) (i : X.Opens ⥤ X.Etale) (x : X) :
    (etaleObjectStalkSections X i x).Additive := inferInstance
