/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
/-! # Quasi-coherence of the affine tensor pushout algebra

Source: Stacks Project, Morphisms, Lemma 01SB.
(blueprint: lem-weil-pbc-affine-module-tensor-algebra-quasi-coherent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {U X : Scheme.{u}} (f : U ⟶ X)

set_option hygiene false in
local notation "𝓙" T => Opens.grothendieckTopology T
set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a
set_option hygiene false in
local notation "A" => (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
set_option hygiene false in
local notation "ρ" => (show X.sheaf ⟶ A from ⟨f.c⟩)
set_option hygiene false in
local notation "R" => SheafOfModules.pushforward.{u} (F := Opens.map f.base)
  (S := 𝓡 A) (R := U.ringCatSheaf) (𝟙 (𝓡 A))
set_option hygiene false in
local notation "S" => SheafOfModules.restrictScalars.{u} (𝓻 ρ)
set_option hygiene false in
local notation "I" => TopCat.Sheaf.inverseImageModule f.base A
set_option hygiene false in
local notation "IA" => TopCat.Sheaf.inverseImageRing f.base A
set_option hygiene false in
local notation "r₀" => tensorPullbackRingMap f
set_option hygiene false in
local notation "t₀" => (TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map ρ
set_option hygiene false in
local notation "e₀" =>
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)).homEquiv A U.sheaf).symm (𝟙 A)
set_option hygiene false in
local notation "adj₀" => Classical.choose (exists_tensorPullbackAdjunction f)
set_option hygiene false in
local notation "qU" => SheafOfModules.isQuasicoherent U.ringCatSheaf
set_option hygiene false in
local notation "qA" => SheafOfModules.isQuasicoherent (𝓡 A)

/-- The tensor pushout of the affine direct-image algebra is quasi-coherent.
Source: Stacks Project, Morphisms, Lemma 01SB, construction of h.
(blueprint: lem-weil-pbc-affine-module-tensor-algebra-quasi-coherent).

Proof: The algebra f_* O_U is quasi-coherent since f is affine. On each affine
open of X it is the tilde of its section algebra. Pulling this algebra to U gives
O_U tensor over f^{-1} O_X with f^{-1}(f_* O_U); pullback of its underlying
quasi-coherent module is quasi-coherent. The pushout universal property identifies
B, with its b action, with this tensor algebra, on pure tensors and hence on the
sheafification. Transfer quasi-coherence along the resulting O_U-module isomorphism.
This uses arbitrary affine morphisms and remains valid for the empty scheme and
zero section rings: the tensor and pushout universal properties hold there too. -/
theorem affine_module_tensor_algebra_quasiCoherent [IsAffineHom f]
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B) (t : IA ⟶ B)
    (hpush : IsPushout r₀ t₀ b t) :
    (Scheme.CommAlgebraSheaf.toModule (Under.mk b)).IsQuasicoherent := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
