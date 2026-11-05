/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement

/-!
# Normalized continuous integral coefficient comparison

Source: Bhatt--Scholze, Lemmas 4.2.12 and 6.8.2(1), and Section 6.5.
(blueprint: lem-weil-pbc-continuous-integral-coefficient-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
open Scheme

end AlgebraicGeometry.ProEtale
