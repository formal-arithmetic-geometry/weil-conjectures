/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaArrows
import WeilConjectures.CategoryTheory.Projection.ProjectionMateSquareCoherence
import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaArrows
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback

/-!
# Operator and base-change naturality of the projection formula

Source: blueprint, proper base change, order 1274; Stacks Tags 0B56, 0944 and 0E48
(blueprint: lemma-weil-pbc-projection-formula-base-change-naturality).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u w v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

end CategoryTheory

namespace SheafOfModules

end SheafOfModules

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
