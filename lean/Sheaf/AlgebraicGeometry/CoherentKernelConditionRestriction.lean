/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Restricting the finite-type kernel condition

Source: Stacks Project, Modules, Definition 01BV and Section 01AF.
(blueprint: lem-weil-pbc-coherent-kernel-condition-restriction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The kernel condition alone, without assuming the module is of finite type,
passes to restriction to an open subscheme.
Source: Stacks Project, Modules, Definition 01BV (definition-coherent), Definition 01B5
(definition-finite-type), and Section 01AF (section-kernels).
(blueprint: lem-weil-pbc-coherent-kernel-condition-restriction).

Proof: For an open `V` of `W`, its image is an open `V'` of `X` contained in `W`.
The equivalence between modules on the open subscheme and modules on the slice site,
followed by the equivalence for an iterated slice, identifies the restriction of
`F|_W` to `V` with `F.over V'`. This equivalence preserves the structure module,
finite coproducts, and kernels. Transfer the given map from a free module of rank `n`
to a map over `V'`; its kernel is finite type by the hypothesis. Transfer the kernel
back. Finite type is preserved by these site equivalences: each finite family of
local generators and its epimorphism transfers to the same finite family on the
corresponding open neighbourhood, and the corresponding neighbourhoods cover.
This applies also to the empty open and rank zero. -/
theorem coherent_kernel_condition_restriction (X : Scheme.{u}) (F : X.Modules)
    (hK : ∀ (U : X.Opens) (n : ℕ)
      (f : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin n)) ⟶
        F.over U), (kernel f).IsFiniteType)
    (W : X.Opens) (V : W.toScheme.Opens) (n : ℕ)
    (f : SheafOfModules.free (R := W.toScheme.ringCatSheaf.over V)
      (ULift.{u} (Fin n)) ⟶ ((Scheme.Modules.restrictFunctor W.ι).obj F).over V) :
    (kernel f).IsFiniteType := by sorry

end AlgebraicGeometry
