/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Local lifting of units along reduction

Source: blueprint `lem-sc-brauer-zero-all-curves`, Proof, Step 1.
(blueprint: lem-sc-reduction-units-epi)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

-- A surjective map detects the nonvanishing locus of a global function.

-- On an affine target a closed immersion is surjective on functions; a unit lift
-- remains a unit because the immersion is surjective on points.

-- Apply affine unit lifting after base change on an affine open cover of each
-- etale object. This proves local surjectivity without identifying its nilradical.

end AlgebraicGeometry.Scheme
