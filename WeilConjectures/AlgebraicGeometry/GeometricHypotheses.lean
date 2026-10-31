/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Geometric hypotheses over the global finite field

Source: Weil conjectures blueprint, `sec-nagata-compactification`,
`sk-prop-nagata-sketch-comp-category/def-weil-geometric-hypotheses.md`, order 412
(blueprint: def-weil-geometric-hypotheses).

## Main definitions

- `WeilConjectures.FiniteFieldDatum.IsSmoothOfPureDimension`: smoothness over `k₀` and
  pure dimension `d` of the specified geometric fibre.

For a finite-type `Y₀ : Over (Spec (.of D.k₀))`, the other two hypotheses reuse the
existing definitions: properness is `AlgebraicGeometry.IsProper Y₀.hom`, and geometric
connectedness is `AlgebraicGeometry.GeometricallyConnected Y₀.hom`. Properness includes
separatedness, universal closedness and local finite type; universal closedness also
implies quasi-compactness, giving finite type. Geometric connectedness tests connectedness
on every field extension and includes nonemptiness, since `ConnectedSpace` is nonempty.
The imported `AlgebraicGeometry.geometricallyConnected_iff_connectedSpace_of_isAlgClosed`
is the node's equivalent criterion on the fixed algebraic closure. Together with
`AlgebraicGeometry.GeometricallyConnected.nonempty_over_field`, it supplies the explicit
nonemptiness clause. No second predicates for these existing notions are introduced.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

/-- A finite-type `k₀`-scheme is smooth of pure dimension `d` if its structure morphism
is smooth and its geometric fibre over the fixed algebraic closure has pure dimension `d`.
Here `d : ℕ` is the nonnegative integer in the source; pure dimension means that every
irreducible component, with its subspace topology, has topological Krull dimension `d`.
In particular, no nonemptiness assumption is imposed on this predicate.
Source: Weil conjectures blueprint, order 412, `def-weil-geometric-hypotheses.md`
(blueprint: def-weil-geometric-hypotheses). -/
def IsSmoothOfPureDimension (D : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (d : ℕ) : Prop :=
  Smooth Y₀.hom ∧ (D.geometricFiber Y₀).left.IsPureDimension d

end WeilConjectures.FiniteFieldDatum
