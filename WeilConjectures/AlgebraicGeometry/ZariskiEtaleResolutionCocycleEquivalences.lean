/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
import WeilConjectures.AlgebraicGeometry.ObjectCohomologyPresheafResolution

/-! # Additive equivalences for Zariski–étale resolution cocycles

Source: Stacks Project, Section 01FT, equation-cohomology-object-site;
Tag 06XR (1), lemma-compute-ext-resolutions.
(blueprint: lem-weil-pbc-zariski-etale-resolution-cocycle-equivalences)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

-- The unchanged statement includes an unused comparison map and existential names.
