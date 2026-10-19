/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import Sheaf.CategoryTheory.Galois.AutProfinite

/-! # The geometric fibre functor on finite locally constant sheaves

Source: Stacks Project, Definition 03RU and Theorem 0BND
(blueprint: def-galois-fibre-functor).
The values are the actual geometric stalks. Finiteness is the existing FLC predicate;
the topology on natural automorphisms is `CategoryTheory.SetFunctorAut.functorTopology`.
Finite continuous actions are Mathlib's `ContAction FintypeCat`.

## Main definitions

* `AlgebraicGeometry.Scheme.flcFiber`: the actual geometric stalk restricted to FLC sheaves.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The fibre functor on FLC set sheaves, with the actual geometric stalk as value and
stalk maps as arrows. The finite-etale version remains `FiniteEtale.fiber` and its
comparison is `FiniteEtale.exists_fiber_flc_equivalence`.
Source: Stacks 03RU and 0BND (blueprint: def-galois-fibre-functor). -/
noncomputable abbrev flcFiber {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) : Y.FLC ⥤ Type (u + 1) :=
  ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber

end AlgebraicGeometry.Scheme
