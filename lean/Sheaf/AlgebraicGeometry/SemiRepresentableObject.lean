/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.SemiRepresentableObject

/-!
# Semi-representable étale objects and hypercovers

Source: Stacks Project, Tags 01G0, 01G3, 01G5, 0183, 0186
(blueprint: def-weil-pbc-semi-representable-object).

The category is Mathlib's `FormalCoproduct X.Etale`, without a second category definition.
Matching objects are the canonical limits of the recorded boundary diagrams;
the coskeleton comparison is the recorded `matching_object_coskeleton` theorem.
-/
