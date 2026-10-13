/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Finite type of a kernel restricted to one open intersection

Source: Stacks Project, Modules, Definitions 01BV and 01B5 and Section 01AF.
(blueprint: lem-weil-pbc-coherent-kernel-intersection-finite-type).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The kernel condition on a single open `U` controls the restriction to `W ∩ U`
of a kernel initially defined on `W`. This comparison requires neither an open
cover nor a finite-type hypothesis on `F`.
Source: Stacks Project, Modules, Definition 01BV (definition-coherent),
Definition 01B5 (definition-finite-type), and Section 01AF (section-kernels).
(blueprint: lem-weil-pbc-coherent-kernel-intersection-finite-type).

Proof: Put `Z = W ∩ U`, regarded as an open of `U`. Restrict `f` to `Z`.
Restriction sends the structure module to the structure module and preserves
finite coproducts; its source is therefore the free module of rank `n` on `Z`.
Transitivity identifies its target with `(F|_U)|_Z`. Precompose with the free-module
comparison isomorphism to obtain a map of precisely the kind in `hK`, and apply
`hK` to that map. Its kernel is finite type. By the sectionwise description of
kernels in 01AF, this kernel identifies with the restriction of `kernel f` to `Z`.
The equivalence between opens of `Z` and the corresponding slice category sends
a local finite generating family to the same sections on the corresponding open:
it preserves the free module, epimorphisms, and the covering family. Consequently
the finite local generating data transfer to `(kernel f).over (Z ⟶ W)`, giving
its finite type by 01B5. Empty intersections and rank zero require no changes. -/
theorem coherent_kernel_intersection_finiteType
    (X : Scheme.{u}) (F : X.Modules) (U : X.Opens) (n : ℕ)
    (hK : ∀ (V : U.toScheme.Opens)
      (g : SheafOfModules.free (R := U.toScheme.ringCatSheaf.over V)
        (ULift.{u} (Fin n)) ⟶ ((Scheme.Modules.restrictFunctor U.ι).obj F).over V),
      (kernel g).IsFiniteType)
    (W : X.Opens)
    (f : SheafOfModules.free (R := X.ringCatSheaf.over W) (ULift.{u} (Fin n)) ⟶
      F.over W) :
    ((kernel f).over (Over.mk (homOfLE (inf_le_left : W ⊓ U ≤ W)))).IsFiniteType := by
  sorry

end AlgebraicGeometry
