/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeCoefficientsSupplement

/-!
# Continuous coefficients in the universe of module values

Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3
(blueprint: def-weil-pbc-lisse-lattice-coefficients).
The coefficient universe is allowed to be the larger site universe. The old
small-coefficient constructions and slice-site inclusion remain available.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
