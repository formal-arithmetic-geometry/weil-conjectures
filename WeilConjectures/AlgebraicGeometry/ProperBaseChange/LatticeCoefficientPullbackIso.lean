/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientPullbackIso

/-!
# Immersion restriction in the lattice coefficient presentation

Source: Bhatt--Scholze, Lemma 6.5.8(1), Definition 6.8.1 and the paragraph before
Definition 6.8.6 (blueprint: lem-weil-pbc-lattice-coefficient-pullback-isIso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
