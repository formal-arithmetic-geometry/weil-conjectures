/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.QCqsDerivedProjectionMate
import WeilConjectures.AlgebraicGeometry.DerivedTensorQCohClosure
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh

/-! # Coherated sheaf derived Hom adjunction

Source: Stacks Project, Duality for Schemes, Lemma 48.3.6 (Tag 0A9Q), with
equation-sheafy-trace (48.3.5.1) defining the sheafy trace
(blueprint: lem-pc-qcqs-sheaf-rhom-adjunction).
-/

@[expose] public section

universe u₁ w₁

open CategoryTheory MonoidalCategory Opposite
open scoped CategoryTheory.Prod

namespace AlgebraicGeometry

set_option autoImplicit false

end AlgebraicGeometry
