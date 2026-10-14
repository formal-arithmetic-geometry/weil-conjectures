/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.SquareZeroTensorGradedPresentation

/-! # Homogeneous quotient multiplication on the degree kernels

Source: Stacks Project, Tags 09MS and 0B8S.
(blueprint: lem-sc-tensor-homogeneous-kernel-action).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

/-- Multiply an ideal tensor by a section of a pulled-back tensor power.
All maps are explicit; the equality h merely identifies the output degree.
Source: Stacks Project, Tag 09MS, multiplication in the graded ideal sequence.
(blueprint: lem-sc-tensor-homogeneous-kernel-action). -/
def tensorIdealSectionMultiply {X Z : Scheme.{u}} (j : Z ⟶ X) (L : X.Modules)
    (a d t : ℕ) (h : d + a = t)
    (s : 𝟙_ Z.Modules ⟶ (tensorPullback j).obj (L.tensorPow a)) :
    (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow d) ⟶
      (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow t) :=
  (ρ_ _).inv ≫ ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow d)) ◁ s ≫
    (boundaryPullbackTensorIso j (j.ker.toModules ⊗ L.tensorPow d)
      (L.tensorPow a)).inv ≫
    (tensorPullback j).map ((α_ _ _ _).hom ≫
      j.ker.toModules ◁ (L.tensorPowAddIso d a).inv ≫
      j.ker.toModules ◁ eqToHom (congrArg L.tensorPow h))

/-- Transport homogeneous ideal multiplication to the kernels using their canonical
inclusion comparisons and the unit on the annihilated ideal tensor.
Source: Stacks Project, Tags 09MS and 08KS.
(blueprint: lem-sc-tensor-homogeneous-kernel-action). -/
def tensorHomogeneousKernelMap {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (a d t : ℕ) (h : d + a = t)
    (s : 𝟙_ Z.Modules ⟶ (tensorPullback j).obj (L.tensorPow a)) :
    kernel (tensorGradedUnit j (L.tensorPow d)) ⟶
      kernel (tensorGradedUnit j (L.tensorPow t)) := by
  letI := square_zero_ideal_tensor_unit_isIso j L hI t
  exact (boundaryIdealKernelIso j (L.tensorPow d)).inv ≫
    (Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
      (j.ker.toModules ⊗ L.tensorPow d) ≫
    (pushforward j).map (tensorIdealSectionMultiply j L a d t h s) ≫
    inv ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
      (j.ker.toModules ⊗ L.tensorPow t)) ≫
    (boundaryIdealKernelIso j (L.tensorPow t)).hom

/-- The raw quotient action on a homogeneous kernel is ideal tensor multiplication.
This statement has arbitrary degrees and no coefficient-degree comparison, block size,
or cohomology data.
Source: Stacks Project, Tag 09MS, graded ideal sequence; Tag 0B8S, quotient action.
(blueprint: lem-sc-tensor-homogeneous-kernel-action).
Proof: The closed-immersion unit on L^a is an epimorphism, so locally lift the
restriction of s evaluated at 1 to a section x of L^a. The equation b_quotient
identifies c_a(s) with p(b_a(x)) on that cover. Precompose the desired identity
with boundaryIdealKernelIso in degree d and evaluate on a section y of J tensor
L^d. Its inclusion is multiplication of the ideal factor, by the defining
inclusion equation of boundaryIdealKernelIso. Apply hglobal and hlocal, then
k_inclusion and b_multiply. The resulting section is the degree d+a inclusion
of the product of y with x; interchange the two factors using symmetry of the
tensor product and commutativity of B. Naturality of the monoidal pullback
comparison and the adjunction unit identifies this with tensorIdealSectionMultiply.
The unit on J tensor L^t is invertible by square-zero annihilation. Its inverse
and the kernel comparison therefore give exactly tensorHomogeneousKernelMap.
Cancel the monic i and the source kernel isomorphism. Local lifts give the same
product: their differences lie in the kernel and squareZero kills their product
with the ideal section. Sheaf separation gives the equality globally. Zero degrees
use the same unitors and do not require the degrees to be distinct. -/
theorem tensorHomogeneousKernel_action {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (T : TensorGradedPresentation j L) (a d t : ℕ) (h : d + a = t)
    (s : 𝟙_ Z.Modules ⟶ (tensorPullback j).obj (L.tensorPow a))
    (σ : ∀ U : X.Opens, T.C.right.obj.obj (op U) →+*
      Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (T.I.val.obj (op U)))
    (μ : T.C.right.obj.obj (op ⊤) →+* End T.I)
    (hlocal : ∀ (U : X.Opens) (b : T.B.right.obj.obj (op U)) (y : T.I.val.obj (op U)),
      @id (T.B.right.obj.obj (op U))
        (T.i.val.app (op U) (σ U (T.p.right.hom.app (op U) b) y)) =
        b * @id (T.B.right.obj.obj (op U)) (T.i.val.app (op U) y))
    (hglobal : ∀ (g : T.C.right.obj.obj (op ⊤)) (U : X.Opens)
      (y : T.I.val.obj (op U)),
      (μ g).val.app (op U) y = σ U (T.C.right.obj.map (homOfLE le_top).op g) y) :
    T.k d ≫ μ ((T.c a).app ⊤ (s.app ⊤ (1 : Γ(Z, ⊤)))) =
      tensorHomogeneousKernelMap j L hI a d t h s ≫ T.k t := by sorry

end
end AlgebraicGeometry.Scheme.Modules
