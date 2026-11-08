/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.TensorPullback
public import Submission.WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Submission.WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.SheafTensorPushoutCancellation
import Submission.WeilConjectures.Topology.InverseImageRegularExtension
import Submission.WeilConjectures.Topology.InverseImageOperationExt

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Algebra base change compared with module tensor pullback

Source: Stacks Project, Sheaves on Spaces, Tags 0095 and 0096; Tag 09MS, coefficient quotient.
(blueprint: lem-sc-algebra-tensor-pullback-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

section
variable {U X : Scheme.{u}} (f : U ⟶ X) (B : X.CommAlgebraSheaf)
set_option hygiene false in
local notation "𝓙" T => Opens.grothendieckTopology T
set_option hygiene false in
local notation "𝓡" A => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj A
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a
set_option hygiene false in
local notation "A" => B.right
set_option hygiene false in
local notation "ρ" => B.hom
set_option hygiene false in
local notation "S" => SheafOfModules.restrictScalars.{u} (𝓻 ρ)
set_option hygiene false in
local notation "I" => TopCat.Sheaf.inverseImageModule f.base A
set_option hygiene false in
local notation "t₀" => (TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map ρ

-- Unlike the affine helper, B is an arbitrary algebra sheaf, not f_* O_U.
end

section
set_option hygiene false in
local notation "𝓡" E =>
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E

end

end
end AlgebraicGeometry.Scheme.Modules
