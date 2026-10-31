/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Standard.ProjectiveSpaceStandardChartsNonvanishing
import WeilConjectures.AlgebraicGeometry.NonvanishingTensorPullback
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-!
# Projective space as a functor of points

Source: literature/stacks-project/constructions.tex, Lemma 27.13.1 (Tag 01NE)
(blueprint: lem-weil-pbc-projective-space-functor-of-points)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

set_option hygiene false in
local notation "P" n:max => ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of (ULift.{u} ℤ)))
set_option hygiene false in
local notation "O" n:max => ProjectiveSpace.twist
  (ULift.{u} (Fin (n + 1))) (Spec (CommRingCat.of (ULift.{u} ℤ))) 1
set_option hygiene false in
local notation "T" n:max i:max => ProjectiveSpace.twistOneSection
  (ULift.{u} (Fin (n + 1))) (Spec (CommRingCat.of (ULift.{u} ℤ))) (ULift.up i)
set_option hygiene false in
local notation "pb" f:max M:max s:max => (((Classical.choose
  (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app M).val.app (Opposite.op ⊤) s)

open Scheme.Modules ProjectiveSpace in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Scheme.Modules ProjectiveSpace in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Scheme.Modules ProjectiveSpace in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 400000 in
-- Comparing the two explicit module pullbacks needs additional elaboration heartbeats.
end AlgebraicGeometry
