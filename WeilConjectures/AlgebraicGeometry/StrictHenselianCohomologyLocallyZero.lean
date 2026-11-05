/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.StrictHenselianStalkSectionsEpi
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.ExactFunctor

/-! # Positive étale cohomology classes are Zariski locally zero

Source: Stacks Project, Étale Cohomology, Tag 09AX, proof, Tags 03Q6 and 03QO.
(blueprint: lem-weil-pbc-strict-henselian-cohomology-locally-zero)
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

