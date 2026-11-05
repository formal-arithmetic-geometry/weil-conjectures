/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Hypercover.ProEtaleHypercoverTotal
public import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative

/-!
# The restriction augmentation into total hypercover sections

Source: Stacks Project, Tag 09A2, lemma-compute-cohomology.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

variable (X : Scheme.{u}) (R : Sheaf (topology X) CommRingCat.{u + 1})
  (W : X.ProEt) (U : SimplicialObject (Over W))

end AlgebraicGeometry.Scheme.ProEt
