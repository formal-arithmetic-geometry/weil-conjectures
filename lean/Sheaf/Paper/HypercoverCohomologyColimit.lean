/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import WeilConjectures.AlgebraicGeometry.HypercoverCohomologyColimit

/-!
# The universal property of hypercover cohomology

Source: Stacks Project, Hypercoverings, Sections 25.9–25.10, Tag 01H0.
(blueprint: def-weil-pbc-hypercover-cohomology-colimit)

The colimit is specified by its universal property, without choosing a skeleton of the
category of hypercovers. Homotopy invariance makes this exactly the colimit over refinements
modulo simplicial homotopy. The coefficient category may be abelian groups or modules.
-/
