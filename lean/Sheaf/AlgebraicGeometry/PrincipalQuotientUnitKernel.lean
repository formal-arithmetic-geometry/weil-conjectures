/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Sheaf.AlgebraicGeometry.ClosedImmersionUnitKernel
import Sheaf.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree

/-! # Multiplication is the kernel of restriction to a principal quotient

Source: Stacks Project, More on Morphisms, Tag 0EX8, the divisibility step in both
proofs; Modules, Tag 08KS, the description of pullback to a closed subscheme.
(blueprint: lem-sc-principal-quotient-unit-kernel)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- Over a domain, for a flat scheme and an invertible module, multiplication by a
nonzero base scalar is the kernel of the unit restricting to its principal quotient.

Source: Stacks Project, Tag 0EX8, the step asserting that a section which vanishes
modulo pi can be divided by pi; Modules, Tag 08KS, pullback to a closed subscheme.
(blueprint: lem-sc-principal-quotient-unit-kernel)

Proof:
1. The quotient map A -> A/(pi) is surjective, so its spectrum and its base change
   i to X are closed immersions. On an affine chart Spec B of X, the closed
   subscheme is Spec(B/pi B); consequently its ideal sheaf is pi O_X.
2. Apply injective_smul_sections_of_flat on each open restriction of X and L.
   The composite of the open immersion with f is flat and the restricted line
   bundle is invertible. Thus multiplication by pi is injective on every open's
   sections, hence is a monomorphism of sheaves. Equivalently, the stalk argument
   tensors the injective map A --pi--> A with flat local rings of X and uses the
   local rank-one trivializations of L.
3. Apply closedImmersion_unit_kernel: the kernel of its adjunction unit is the
   image of multiplication J tensor L -> L, where J = pi O_X. This image equals
   the image of L.smulHom(pi): on each trivializing neighbourhood both consist
   precisely of the multiples pi l. Since multiplication is a monomorphism, L
   itself with this multiplication map is a kernel object.
4. The kernel theorem chooses an adjunction via nonempty_tensorPullbackAdjunction,
   whereas the statement uses exists_tensorPullbackAdjunction. Uniqueness of left
   adjoints compares these units by an invertible map on their targets. Composing
   with an isomorphism preserves the kernel fork, proving the displayed limit.

Edge cases: a unit pi gives an empty quotient scheme and invertible multiplication;
the kernel is all of L. The zero module and the empty scheme give zero kernel
objects. The assumption pi != 0 is essential for multiplication to be a kernel
monomorphism on a nonzero module. Neither properness nor integrality of a fibre
nor the valuation-ring condition is used. -/
theorem principal_quotient_unit_kernel
    (A : Type u) [CommRing A] [IsDomain A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [Flat f]
    (L : X.Modules) [L.IsInvertible] (π : A) (hπ : π ≠ 0) :
    let i := pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {π}))))
    let η := (Classical.choose (exists_tensorPullbackAdjunction i)).unit.app L
    let μ := L.smulHom (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom π)
    ∃ w : μ ≫ η = 0, Nonempty (IsLimit (KernelFork.ofι μ w)) := by sorry

end AlgebraicGeometry.Scheme.Modules
