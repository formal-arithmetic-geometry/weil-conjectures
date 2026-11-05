/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Positive-degree Zariski cohomology classes vanish locally

Source: Stacks Project, Etale Cohomology, Lemma 0GY0 (label `lemma-gabber-criterion`),
line 14228, proof (blueprint: lem-weil-pbc-zariski-cohomology-locally-zero).
-/

@[expose] public section

universe u v

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

-- Stacks 01FW: an exact triple of sheaves lifts kernel sections locally.

end AlgebraicGeometry
