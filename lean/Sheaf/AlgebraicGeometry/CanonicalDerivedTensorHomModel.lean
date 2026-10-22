/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomModel
public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison

/-! # Canonical derived tensor/internal-Hom bijections
Source: Stacks Project, cohomology.tex, Tag 08DJ (lemma-internal-hom).
(blueprint: def-pc-canonical-derived-tensor-hom-bijection).
The representative equation uses the actual Hom-complex projections, sheaf tensor-Hom
currying, the localization factorization, and the functorial K-injective resolution.
-/

@[expose] public section
