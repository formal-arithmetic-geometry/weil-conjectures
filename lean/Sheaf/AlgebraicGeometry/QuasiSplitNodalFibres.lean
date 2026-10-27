/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Rational nodes and branches of nodal fibres

Source: de Jong, Families of curves and alterations, definition before Lemma 5.7,
pp. 614--615 (blueprint: def-sfb-quasi-split-nodal-fibres).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The quasi-splitness condition for a nodal family. Every nonsmooth point of every
residue-field fibre is rational over the residue field of the base, and its normalization
has exactly two points above it, both rational over that same field. This imposes no
smoothness on the irreducible components and permits self-nodes.
Source: de Jong, Families of curves and alterations, definition before Lemma 5.7,
pp. 614--615 (blueprint: def-sfb-quasi-split-nodal-fibres). -/
def HasQuasiSplitNodalFibres {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (t : S) (x : f.fiber t),
    (¬ ∃ U : (f.fiber t).Opens, x ∈ U ∧ Smooth (U.ι ≫ f.fiberToSpecResidueField t)) →
    Function.Surjective ((f.fiberToSpecResidueField t).residueFieldMap x).hom ∧
    Nat.card {z : (f.fiber t).reducedNormalization //
      (f.fiber t).fromReducedNormalization z = x} = 2 ∧
    ∀ z : (f.fiber t).reducedNormalization,
      (f.fiber t).fromReducedNormalization z = x →
      Function.Surjective
        (((f.fiber t).fromReducedNormalization ≫ f.fiberToSpecResidueField t).residueFieldMap z).hom

end AlgebraicGeometry
