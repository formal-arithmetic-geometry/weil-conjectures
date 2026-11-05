/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CohomologyFractionPresentation
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.LocalizedCohomologyMayerVietoris
import WeilConjectures.AlgebraicGeometry.CohomologySectionDivision
import Mathlib.Algebra.FiveLemma

universe u_1
@[expose] public section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/- Historical counterexample to the former interface: on Spec k for a nonzero field,
 U = V = S = top, L = F = O, s = 1, and c W p = 0 satisfied the old local
 premises but gave the nonbijective zero map k -> k in degree zero. The old
 STATEMENT-DISPUTED interface omitted hc and replaced the intersection formula
 by True. The corrected hc excludes this example. -/

end AlgebraicGeometry.Scheme.Modules
