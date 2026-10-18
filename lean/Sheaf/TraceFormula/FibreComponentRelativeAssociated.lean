module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import Sheaf.AlgebraicGeometry.AssociatedPoints

@[expose] public section

universe u

open Set
open AlgebraicGeometry

namespace AlgebraicGeometry

/-!
# Fibre-component generic points are relative associated points

Source: Stacks Project, Divisors Tags 05AT, 02OJ and 05AH, with
Morphisms Tag 01T6 (blueprint: lem-trf-fibre-component-relative-associated).
-/

/-- A generic point of an irreducible component of a locally finite type flat
scheme-theoretic fibre is associated to the fibre structure sheaf and belongs
to the relative assassin, written as the union of the images of all fibrewise
associated-point sets.
Source: Stacks Project, Divisors Tags 05AT, 02OJ and 05AH, with
Morphisms Tag 01T6 (blueprint: lem-trf-fibre-component-relative-associated).
The proof first makes the fibre locally Noetherian by base change to the
residue field and Tag 01T6.  It identifies the component generic point with a
minimal prime on a Noetherian affine neighbourhood, applies the minimal-prime
associated-prime theorem, and localizes the associated prime to the stalk.
The definition of associated points then gives the fibrewise conclusion, and
membership in the displayed union gives the relative-assassin conclusion.
-/
theorem fibre_component_relative_associated
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFiniteType f]
    (t : S) (C : Set (f.fiber t)) (y : f.fiber t)
    (hC : C ∈ irreducibleComponents (f.fiber t))
    (hy : IsGenericPoint y C) :
    y ∈ associatedPoints (f.fiber t) ∧
      f.fiberι t y ∈ ⋃ s : S, (f.fiberι s) '' associatedPoints (f.fiber s) := by
  sorry

end AlgebraicGeometry
