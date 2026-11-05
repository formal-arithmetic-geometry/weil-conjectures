/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom

import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import all WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageScalarComparison
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootLocalModels
import all WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Tate twists with finite coefficients are locally free of rank one

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.md`, clauses (1)--(3) for finite coefficients
(blueprint: det-def-sp-tate-twist-locally-free).

The finite part of `WeilConjectures.AlgebraicGeometry.Tate.TateTwistLocallyFree`, in its own module
so that the finite twists do not depend on the integral, rational and algebraically closed
coefficient clauses.
All positive root levels are indexed by `n + 1`.

## Main definitions

* `tateFiniteLine` is the recorded roots module tensored with a finite coefficient ring.
* `TateSignedLine` states rank one, same-cover triviality and the tensor inverse.
* `TateInverseTwists` fixes the actual functor and negative inverse of an equivalence.

## Main statements

* `tateTwist_finite_locallyFree` states the common cover, the compatible root generators and
  the finite coefficient clauses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u v d c h

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] HasDerivedCategory.standard

attribute [local instance 20000] tateAbSheafify
attribute [local instance 20000] tateAbBijective

attribute [local instance 20000] tateWeakSheafify

attribute [local instance 20000] tateSiteSmall

@[instance_reducible] private def tateDerived (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1} (purTwistRing X R)) :=
  HasDerivedCategory.standard _
attribute [local instance 20000] tateDerived

end AlgebraicGeometry.Scheme
