/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.JacobsonSpace
public import WeilConjectures.ZetaSeries

import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.FieldTheory.AlgClosedFinitelyGeneratedFinite
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# An abstract nodal completion forces a rational closed point

Source: Stacks Project, curves.tex, Tag 0C56, lemma-node-field-extension, closed-point
reduction, adapted to an abstract ring isomorphism without a dimension hypothesis
(blueprint: lem-trf-nodal-completion-rational-point).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An abstract split nodal completion forces closedness and rationality through the
specified structure morphism, including the corresponding statement on every finite-type
affine neighbourhood. The completion isomorphism need not respect the ground field.

Source: Stacks Project, curves.tex, Tag 0C56, lemma-node-field-extension, closed-point
reduction, and the finite-generation argument in the DAG proof
(blueprint: lem-trf-nodal-completion-rational-point).

Proof plan:
1. In `k[[u,v]]/(uv)`, a series with nonzero constant term is a unit: write its inverse
   as the geometric series after dividing by its constant term. Each coefficient involves
   finitely many terms. A series with zero constant term cannot be a unit, by evaluation
   at zero. Thus this quotient is local with residue field abstractly isomorphic to `k`.
   The first projection from the completed stalk to its residue field is surjective,
   since every residue class has a lift in the stalk. Its kernel is therefore the unique
   maximal ideal. The residue field of the stalk is abstractly isomorphic to `k` and is
   algebraically closed. This does not identify the structure homomorphism from `k`.
2. Choose a finite-type affine neighbourhood of `x`. The affine-open stalk localization
   theorem identifies the stalk with the localization at its corresponding prime.
   The finite-type residue-extension theorem makes its residue field finitely generated
   as a field over `k`, through the actual structure map.
3. Apply `FieldExtension.finiteDimensional_of_isAlgClosed_of_fg` to that map, obtaining
   a finite extension. Since the base is algebraically closed,
   `IsAlgClosed.algebraMap_bijective_of_isIntegral` makes the structure map bijective.
4. On every finite-type affine neighbourhood, clause (a) of
   `closedPoint_iff_residueField_trdeg_zero_and_finite` makes the prime maximal.
   Localization at a maximal ideal does not change its field quotient, compatibly with
   `k`, so the structure map to that quotient is bijective too. Finally, if `z` specializes
   `x`, a finite-type affine neighbourhood of `z` also contains `x`; closedness there
   gives `z = x`. This proves global closedness without a separatedness hypothesis.
-/
theorem nodalCompletion_closed_rational
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X)
    (hcompletion : Nonempty
      (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)
        ≃+* (MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
            MvPowerSeries.X 1}))) :
    x ∈ closedPoints X ∧ Function.Bijective (f.residueFieldAlgebraMap x) ∧
      ∀ (U : X.affineOpens) (hxU : x ∈ U.1),
        ((f.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).FiniteType →
        (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.IsMaximal ∧
          Function.Bijective
            ((Ideal.Quotient.mk (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal).comp
              ((f.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)) := by
  sorry

end AlgebraicGeometry
