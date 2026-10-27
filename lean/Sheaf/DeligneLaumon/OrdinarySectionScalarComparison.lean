/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData

/-! # Ordinary scalars in section-action coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.StratifiedContinuousLattices

local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0} X.ProEt

/-- Ordinary scalar extension under the section-action equivalence, with pure tensors fixed.

Source: Stacks Project, Tags 00YV, 03EK and 03EL; step 4 of
lem-zl-continuous-constructible-stratified-lattices.
(blueprint: lem-zl-ordinary-section-scalar-comparison).

Proof: sectionModuleComapIso identifies scalar restriction under the section-action
encodings by the identity on the underlying sections. Transport the internal
extension/restriction adjunction through these equivalences. The transported right
adjoint is ordinary scalar restriction. Uniqueness of left adjoints identifies its
left adjoint with pbcExtend. Choose the unique comparison preserving the adjunction
units. The internal unit sends m to 1 tensor m, and the ordinary unit has the same
formula by pbcScalarAdjunction_exists. Thus the comparison sends 1 tensor m to
1 tensor m. Its S-linearity then sends s times this element to s tensor m, which is
exactly pure_tensors. This works for every module and every test object, including
the empty object, zero modules and zero rings; no freeness hypothesis is used. -/
theorem ordinary_section_scalar_comparison (X : Scheme.{u})
    (R S : Sheaf (ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] : Nonempty (OrdinaryScalars X R S φ) := by sorry

end WeilConjectures.StratifiedContinuousLattices
