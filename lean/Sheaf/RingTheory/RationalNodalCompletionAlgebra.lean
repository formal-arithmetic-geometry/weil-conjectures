/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Sheaf.RingTheory.SeparableClosedPointFormalPresentation
import Sheaf.TraceFormula.FormalJacobianQuadraticCriterion
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete

/-! # Coefficient-compatible rational nodal completions

Source: Stacks Project, curves.tex, Tag 0C49 (lemma-nodal-algebraic), and varieties.tex,
Tag 0C52 (lemma-complete-local-ring-structure-as-algebra)
(blueprint: lem-trf-rational-nodal-completion-algebra).

The topologies are specified explicitly. On the completion we use the extension of the
local ring's maximal ideal; on the nodal quotient we use the image of the variable ideal.
These are the respective maximal ideals. Thus no ambient topology on the field, series
ring, or inverse limit is silently used.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- An abstract rational split-node completion has a coefficient-compatible presentation,
including the continuous quotient-map formulation, without a dimension assumption on `S`.

Source: Stacks Project, curves.tex, Tag 0C49, and varieties.tex, Tag 0C52
(blueprint: lem-trf-rational-nodal-completion-algebra).

Proof:
1. Identify `S/p` with `k` via the structural isomorphism. Apply
   lem-trf-separable-closed-point-formal-presentation to the identity separable extension.
   The resulting finite formal presentation has at least two variables (dummy variables
   are allowed). Its coefficient section is the structural map, since it is a `k`-algebra
   section of `k` itself.
2. Compose the presentation with the assumed ring isomorphism to the split node. Apply
   (c) implies (b) of lem-trf-formal-jacobian-quadratic-criterion, starting with the
   quadratic form `uv`, to obtain a coefficient-compatible binary quadratic presentation
   with discriminant `b^2 - 4ac` nonzero. This uses no dimension hypothesis on `S`.
3. Split the quadratic into independent linear factors. If `a = 0`, use `y` and
   `bx + cy`, whose determinant is `-b`. Otherwise choose a root `r` of `aT^2+bT+c`,
   set `s = -b/a-r`, and use `a(x-ry)` and `x-sy`. Here `rs = c/a` and
   `b^2-4ac = a^2(r-s)^2`, so the determinant `a(r-s)` is nonzero, also in characteristic 2.
4. Use lem-weil-pbc-power-series-field-cohen-regular-complete and
   lem-weil-pbc-power-series-universal-property-complete to substitute these two linear
   forms into the series ring. If their matrix is [[A,B],[C,D]] with determinant `d`,
   substitute `(DU-BV)/d` and `(-CU+AV)/d` for the inverse. Uniqueness in the universal
   property makes the composites identities. The maps preserve the variable ideals and
   their powers and carry `(UV)` onto the quadratic ideal, so descend to inverse algebra
   maps on the quotients. Combine with step 2.
5. Local ring isomorphisms preserve the unique maximal ideals and all their powers,
   hence both directions are continuous. Compose the inverse algebra equivalence with
   Ideal.Quotient.mkₐ to obtain the continuous surjection from the series ring. Its
   kernel is `(uv)` by injectivity of the equivalence; it fixes constants because both
   maps are algebra maps. The quotient map sends each power of the variable ideal into
   the corresponding power of the quotient maximal ideal. This proves both formulations.
-/
theorem rational_nodal_completion_algebra
    {k : Type u} {S : Type v} [Field k] [IsAlgClosed k] [CommRing S] [Algebra k S]
    (hS : (algebraMap k S).FiniteType) (p : Ideal S) [p.IsMaximal]
    (hp : Function.Bijective (algebraMap k (S ⧸ p)))
    (hnode : Nonempty
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p) ≃+*
        (MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1}))) :
    (∃ e : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p) ≃ₐ[k]
        (MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1}),
      @Continuous _ _
        ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
          (algebraMap (Localization.AtPrime p)
            (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
              (Localization.AtPrime p)))).adicTopology
        ((Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) k))).map
          (Ideal.Quotient.mk
            (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
              MvPowerSeries.X 1}))).adicTopology e ∧
      @Continuous _ _
        ((Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) k))).map
          (Ideal.Quotient.mk
            (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
              MvPowerSeries.X 1}))).adicTopology
        ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
          (algebraMap (Localization.AtPrime p)
            (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
              (Localization.AtPrime p)))).adicTopology e.symm) ∧
    (∃ π : MvPowerSeries (Fin 2) k →ₐ[k]
        AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p),
      Function.Surjective π ∧
      RingHom.ker π.toRingHom =
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1} ∧
      @Continuous _ _
        (Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) k))).adicTopology
        ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
          (algebraMap (Localization.AtPrime p)
            (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
              (Localization.AtPrime p)))).adicTopology π ∧
      ∀ c : k, π (MvPowerSeries.C c) =
        algebraMap k (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p)) c) := by
  sorry

end Algebra
