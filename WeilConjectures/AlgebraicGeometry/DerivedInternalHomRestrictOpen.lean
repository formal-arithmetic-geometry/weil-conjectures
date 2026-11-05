/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.Algebra.Homology.HomComplexRestrictOpen

/-!
# Derived internal Hom commutes with restriction to opens

Source: literature/stacks-project/cohomology.tex, Lemma 08DL
(blueprint: lem-sc-derived-internal-hom-restrict-open).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
universe u w

namespace CategoryTheory

end CategoryTheory
