/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalStalkSectionsComparisonMap
import WeilConjectures.AlgebraicGeometry.LocalStalkSectionsAffineVanishing

/-! # Descent of equality for local-scheme sections

Source: Stacks Project, Tag 03Q6, degree zero of Lemma 59.51.5.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

