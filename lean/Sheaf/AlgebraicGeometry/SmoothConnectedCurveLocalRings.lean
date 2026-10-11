/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Sheaf.AlgebraicGeometry.FunctionField

/-!
# Local rings and normalized valuations of a smooth connected curve

Source: Stacks Project, Properties, Tags 033M and 02IZ; Algebra, Tag 00PD;
the standing setting of Divisors, Tag 0BE9
(blueprint: lem-sc-smooth-connected-curve-local-rings).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A smooth connected curve over an algebraically closed field is Noetherian and integral,
its nongeneric points are exactly its closed points, and its closed stalks are DVRs with
fraction field the generic stalk. Their normalized valuations are independent of uniformizer.
Source: Stacks Project, Properties, Tags 033M and 02IZ; Algebra, Tag 00PD; the standing
hypotheses of Divisors, Tag 0BE9 (blueprint: lem-sc-smooth-connected-curve-local-rings).

Proof:
1. Finite type over the Noetherian field spectrum gives Noetherianity
   (`lem-weil-pbc-finite-type-over-noetherian`). Smoothness gives regular local rings
   (`lem-sc-smooth-regular`, `def-weil-regular-scheme`).
2. Nonempty connected regular schemes are integral (`lem-sc-regular-connected-integral`,
   the regular form of 033M). Integrality implies irreducibility
   (`lem-pc-integral-scheme-irreducible`); sobriety gives the unique generic point
   (`lem-sc-scheme-sober`). It belongs to every nonempty open. The generic stalk is a field
   (`lem-sc-integral-function-field-affine-fraction`). Germ maps and specialization maps
   to this field are injective, and each stalk has it as fraction field
   (`lem-sc-integral-scheme-stalks-in-function-field`).
3. Sobriety makes distinct points have distinct closures. Every nonempty closed subset of
   the quasi-compact underlying space contains a closed point
   (`lem-sc-quasi-compact-kolmogorov-closed-point`). In particular closed points exist.
4. A strict chain of two generalizations would give dimension at least two, excluded by
   dimension one (`lem-sc-scheme-stalk-dimension-generalization-chains`,
   `def-kun-topological-krull-dimension`, `def-pc-dimension`). A one-point scheme would
   have dimension zero, so the generic point is not closed.
5. If a nongeneric point were not closed, a closed point in its closure, that point, and
   the generic point would form a forbidden length-two chain. Thus it is closed.
6. At a closed point, the chain from it to the generic point has length one, and no longer
   chain exists. Thus its stalk has dimension one (02IZ and
   `lem-sc-scheme-stalk-dimension-generalization-chains`).
7. Its regular local ring of dimension one is a DVR (`lem-sc-regular-dim1-dvr`, 00PD).
   Its fraction field is the generic stalk by step 2.
8. Fix a uniformizer t. Each nonzero stalk element is a unit times a nonnegative power of t
   (`lem-weil-pbc-dvr-unit-times-uniformizer-power`). Express a nonzero fraction a/b using
   these forms to obtain u times an integer power of t. Two different exponents would put
   a unit in the maximal ideal, so the exponent and then the unit are unique. A different
   uniformizer is a unit times t, so the exponent is unchanged. Multiplication adds
   exponents; powers of t realize all integers; the nonzero stalk elements are exactly
   the fractions with nonnegative exponent.

The existential integral instance is a conclusion, not an additional hypothesis. For this
integral curve `C.functionField` is the generic stalk, as in `def-sc-function-field`.
The homomorphism uses `Multiplicative ℤ` to express an additive integer valuation on the
multiplicative group of nonzero field elements. -/
theorem Scheme.smooth_connected_curve_local_rings
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] :
    ∃ hC : IsIntegral C,
      letI := hC
      IsNoetherian C ∧
      IsGenericPoint (genericPoint C) (Set.univ : Set C) ∧
      IsField C.functionField ∧
      (∀ (V : C.Opens) (_ : Nonempty V) (x : V),
        Function.Injective (C.presheaf.germ V x x.property)) ∧
      (∀ x : C, Function.Injective (algebraMap (C.presheaf.stalk x) C.functionField)) ∧
      (∀ x : C, x ≠ genericPoint C → x ∈ closedPoints C) ∧
      genericPoint C ∉ closedPoints C ∧
      (∃ P : C, P ∈ closedPoints C) ∧
      (∀ P : C, P ∈ closedPoints C →
        IsDiscreteValuationRing (C.presheaf.stalk P) ∧
        IsFractionRing (C.presheaf.stalk P) C.functionField ∧
        ∃ v : C.functionFieldˣ →* Multiplicative ℤ,
          Function.Surjective v ∧
          (∀ (t : C.presheaf.stalk P),
            IsLocalRing.maximalIdeal (C.presheaf.stalk P) = Ideal.span {t} →
            ∀ g : C.functionFieldˣ,
              (∃! q : (C.presheaf.stalk P)ˣ × ℤ,
                (g : C.functionField) =
                  algebraMap (C.presheaf.stalk P) C.functionField (q.1 : C.presheaf.stalk P) *
                    (algebraMap (C.presheaf.stalk P) C.functionField t) ^ q.2) ∧
              (∀ q : (C.presheaf.stalk P)ˣ × ℤ,
                (g : C.functionField) =
                    algebraMap (C.presheaf.stalk P) C.functionField (q.1 : C.presheaf.stalk P) *
                      (algebraMap (C.presheaf.stalk P) C.functionField t) ^ q.2 →
                  Multiplicative.toAdd (v g) = q.2)) ∧
          (∀ g : C.functionFieldˣ,
            (∃ r : C.presheaf.stalk P, r ≠ 0 ∧
              algebraMap (C.presheaf.stalk P) C.functionField r = (g : C.functionField)) ↔
            0 ≤ Multiplicative.toAdd (v g))) :=
  sorry

end AlgebraicGeometry
