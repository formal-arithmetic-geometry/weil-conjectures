/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ChowRelativeAmpleGeometric
import WeilConjectures.AlgebraicGeometry.ChowRelativeAmpleTwist

/-!
# Chow immersion and relative ampleness

Source: Stacks Project, Cohomology of Schemes, Remark 30.18.2 and
Proposition 30.19.1, Tag 02O5 (blueprint: lem-pc-chow-relative-ample).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

end AlgebraicGeometry
