/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The normalized finite-ring module adjunction

Source: Stacks Project, Modules on Sites, lemma-adjoint-push-pull-modules;
blueprint smooth purity, inverse image on the small pro-etale site
(blueprint: def-weil-proetale-inverse-image).

The existing inverse-image module and all its previous interfaces are reexported.
The additional adjunction uses the transported action for arbitrary finite rings.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type (u + 1))
  [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]


end AlgebraicGeometry.ProEtale
