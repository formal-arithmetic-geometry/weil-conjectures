/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

import Mathlib.RingTheory.Unramified.Field
import Sheaf.RingTheory.CompletionKaehlerDifferentialComparison
import Sheaf.RingTheory.FormalPowerSeriesContinuousDifferentials

/-!
# Jacobian presentation of completed Kähler differentials

Source: Stacks Project, Curves, Tag 0C4D, with the coefficient-field section of
Varieties, Tag 0C52 (blueprint: lem-trf-completed-jacobian-differentials).

The auxiliary completed-presentation comparison is the one recorded in the DAG;
Tag 0C4D itself states the polynomial Jacobian presentation.

## Main definitions

* `completedResidueMap`: reduction to the specified residue field `S/p`.
* `completedDifferentialTarget`: the written tensor target `Ω[A/k] ⊗[A] Â`.
* `IsCompletedDifferentialExtension`: continuity and the two characterizing identities.
* `completedJacobianMatrix` and `completedDifferentialCoordinateMap`: the explicit maps.

## Main statements

* `completedJacobianDifferentials`: the unique extension and its Jacobian cokernel isomorphism.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public section

universe u v

open scoped BigOperators

namespace AlgebraicGeometry

/-- The localization `A = Sₚ`.
Source: Stacks Project, Curves, Tag 0C4D
(blueprint: lem-trf-completed-jacobian-differentials). -/
abbrev completedLocalRing (S : Type v) [CommRing S] (p : Ideal S) [p.IsPrime] :=
  Localization.AtPrime p

/-- The maximal ideal `pA` of the localized ring.
Source: Stacks Project, Curves, Tag 0C4D
(blueprint: lem-trf-completed-jacobian-differentials). -/
abbrev completedIdeal (S : Type v) [CommRing S] (p : Ideal S) [p.IsPrime] :=
  Ideal.map (algebraMap S (completedLocalRing S p)) p

/-- The maximal-ideal completion of `Sₚ`, with its canonical algebra map.
Source: Stacks Project, Curves, Tag 0C4D
(blueprint: lem-trf-completed-jacobian-differentials). -/
abbrev completedRing (S : Type v) [CommRing S] (p : Ideal S) [p.IsPrime] :=
  AdicCompletion (completedIdeal S p) (completedLocalRing S p)

/-- The tensor product `Ω[A/k] ⊗[A] Â`, in the order specified in the node.
Source: Stacks Project, Curves, Tag 0C4D
(blueprint: lem-trf-completed-jacobian-differentials). -/
abbrev completedDifferentialTarget (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime] :=
  TensorProduct (completedLocalRing S p)
    (KaehlerDifferential k (completedLocalRing S p)) (completedRing S p)

/-- The action on the right tensor factor, transported through tensor symmetry.
Source: Stacks Project, Curves, Tag 0C4D
(blueprint: lem-trf-completed-jacobian-differentials). -/
noncomputable instance completedDifferentialTargetSMul
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime] :
    SMul (completedRing S p) (completedDifferentialTarget k S p) where
  smul c x :=
    (TensorProduct.comm (completedLocalRing S p)
      (KaehlerDifferential k (completedLocalRing S p)) (completedRing S p)).symm
      (c • (TensorProduct.comm (completedLocalRing S p)
        (KaehlerDifferential k (completedLocalRing S p)) (completedRing S p)) x)

/-- The completion-module structure on the written tensor target `Ω ⊗ Â`.
Source: Stacks Project, Curves, Tag 0C4D
(blueprint: lem-trf-completed-jacobian-differentials). -/
noncomputable instance completedDifferentialTargetModule
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime] :
    Module (completedRing S p) (completedDifferentialTarget k S p) :=
  Function.Injective.module (completedRing S p)
    (TensorProduct.comm (completedLocalRing S p)
      (KaehlerDifferential k (completedLocalRing S p)) (completedRing S p)).toAddMonoidHom
    (TensorProduct.comm (completedLocalRing S p)
      (KaehlerDifferential k (completedLocalRing S p)) (completedRing S p)).injective
    (fun _ _ ↦ LinearEquiv.apply_symm_apply _ _)

/-- The canonical residue map: evaluate a compatible sequence modulo `pA`, then
identify `A/pA` with `S/p` by the localization residue-field equivalence.
Source: Stacks Project, Varieties, Tag 0C52
(blueprint: lem-trf-completed-jacobian-differentials). -/
noncomputable def completedResidueMap
    {S : Type v} [CommRing S]
    (p : Ideal S) [p.IsMaximal] [p.IsPrime] :
    completedRing S p →+* (S ⧸ p) :=
  ((IsLocalization.AtPrime.equivQuotMaximalIdeal p (completedLocalRing S p)).symm.toRingHom).comp
    ((Ideal.quotEquivOfEq
      (IsLocalization.AtPrime.map_eq_maximalIdeal p (completedLocalRing S p))).toRingHom.comp
      (AdicCompletion.evalOneₐ (completedIdeal S p)).toRingHom)

/-- A continuous extension of the universal derivation that vanishes on the coefficient field.
Continuity is the ideal-power criterion for the indicated adic ring and module topologies.
Source: Stacks Project, Curves, Tag 0C4D; More Algebra, Tag 0C34
(blueprint: lem-trf-completed-jacobian-differentials). -/
def IsCompletedDifferentialExtension
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime]
    (σ : (S ⧸ p) →ₐ[k] completedRing S p)
    (dhat : Derivation k (completedRing S p) (completedDifferentialTarget k S p)) : Prop :=
  (∀ r : ℕ, ∃ N : ℕ, ∀ z : completedRing S p,
      z ∈ (Ideal.map (algebraMap (completedLocalRing S p) (completedRing S p))
        (completedIdeal S p)) ^ N →
      dhat z ∈ (Ideal.map (algebraMap (completedLocalRing S p) (completedRing S p))
        (completedIdeal S p)) ^ r •
        (⊤ : Submodule (completedRing S p) (completedDifferentialTarget k S p))) ∧
  (∀ a : completedLocalRing S p,
      dhat (AdicCompletion.of (completedIdeal S p) (completedLocalRing S p) a) =
        TensorProduct.tmul (completedLocalRing S p)
          ((KaehlerDifferential.D k (completedLocalRing S p)) a) (1 : completedRing S p)) ∧
  (∀ c : S ⧸ p, dhat (σ c) = 0)

/-- The Jacobian matrix after a continuous formal-power-series presentation.

Source: Stacks Project, Curves, Tag 0C4D (blueprint: lem-trf-completed-jacobian-differentials). -/
noncomputable def completedJacobianMatrix
    {S : Type v} [CommRing S]
    (p : Ideal S) [p.IsPrime]
    (n s : ℕ) (f : Fin s → MvPowerSeries (Fin n) (S ⧸ p))
    (π : MvPowerSeries (Fin n) (S ⧸ p) →+* completedRing S p) :
    Matrix (Fin n) (Fin s) (completedRing S p) :=
  fun i j ↦ π ((MvPowerSeries.pderiv (S ⧸ p) i) (f j))

/-- The coordinate map sending the formal variables to their continuous differentials.

Source: Stacks Project, Curves, Tag 0C4D (blueprint: lem-trf-completed-jacobian-differentials). -/
noncomputable def completedDifferentialCoordinateMap
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime]
    (n : ℕ)
    (π : MvPowerSeries (Fin n) (S ⧸ p) →+* completedRing S p)
    (dhat : Derivation k (completedRing S p) (completedDifferentialTarget k S p)) :
    (Fin n → completedRing S p) →ₗ[completedRing S p]
      completedDifferentialTarget k S p :=
  Fintype.linearCombination _ (fun i ↦ dhat (π (MvPowerSeries.X i)))

/-- **Jacobian presentation of completed Kähler differentials.**

Let `k` be a field, `S` a finitely generated `k`-algebra, and `p` a maximal ideal.
Put `A = Sₚ`, `F = S ⧸ p`, and complete `A` at its maximal ideal. Assume `F/k`
is finite separable and choose a coefficient-field section of the residue map. For a
continuous surjection from `F[[t₁,…,tₙ]]` with kernel generated by
`f₁,…,fₛ` in the variable ideal, the
completed Jacobian cokernel is identified with `Ω[A⁄k] ⊗[A] Â`; the class of `eᵢ`
maps to the continuous differential of `tᵢ`.

Source: Stacks Project, Curves, Tag 0C4D (blueprint: lem-trf-completed-jacobian-differentials).
Proof:
1. `lem-trf-completion-kahler-differential-comparison` (i) gives the unique continuous
extension of `d`. Its restriction along the coefficient section factors through `Ω[F/k]`
by the universal property of Kähler differentials. This module is zero by
`lem-trf-separable-field-differentials-vanish`, so the restriction vanishes.
2. Part (ii) of the completion comparison identifies the tensor target with continuous
`F`-differentials of the completion, carrying the extended derivation to the continuous
universal `F`-derivation on every element of the completion.
3. Continuity makes each variable image topologically nilpotent, so it lies in the
extended maximal ideal. Surjectivity and the specified coefficient section then identify
the image of the variable ideal with that maximal ideal: the quotient is the nonzero
residue field. Thus both continuous differential constructions use the same adic topology.
Apply `lem-trf-formal-power-series-continuous-differentials` to obtain its Jacobian
cokernel presentation, with the prescribed coordinate differential images.
4. Compose this isomorphism with the inverse of the comparison in step 2. It sends the
class of every basis vector to `dhat(π(tᵢ))`, hence its composite with the quotient map
is exactly `completedDifferentialCoordinateMap`. Uniqueness of the extension in step 1
provides the quantified uniqueness clause. No derivation is assumed as extra data. -/
theorem completedJacobianDifferentials
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (hfinite : RingHom.FiniteType (algebraMap k S))
    (p : Ideal S) [p.IsMaximal]
    [FiniteDimensional k (S ⧸ p)] [Algebra.IsSeparable k (S ⧸ p)]
    (n s : ℕ)
    (σ : (S ⧸ p) →ₐ[k] completedRing S p)
    (hsection : (completedResidueMap p).comp σ.toRingHom = RingHom.id (S ⧸ p))
    (f : Fin s → MvPowerSeries (Fin n) (S ⧸ p))
    (hf : ∀ j : Fin s, f j ∈ Ideal.span (Set.range (fun i : Fin n ↦
      (MvPowerSeries.X i : MvPowerSeries (Fin n) (S ⧸ p)))))
    (π : MvPowerSeries (Fin n) (S ⧸ p) →+* completedRing S p)
    (hπsurj : Function.Surjective π)
    (hπcontinuous : @Continuous (MvPowerSeries (Fin n) (S ⧸ p)) (completedRing S p)
      (@MvPowerSeries.WithPiTopology.instTopologicalSpace (Fin n) (S ⧸ p) ⊤)
      ((Ideal.map (algebraMap (completedLocalRing S p) (completedRing S p))
        (completedIdeal S p)).adicTopology) π)
    (hπcoeff : ∀ c : S ⧸ p, π (MvPowerSeries.C c) = σ c)
    (hkernel : RingHom.ker π = Ideal.span (Set.range f)) :
    ∃ dhat : Derivation k (completedRing S p) (completedDifferentialTarget k S p),
      IsCompletedDifferentialExtension p σ dhat ∧
      (∀ dhat' : Derivation k (completedRing S p) (completedDifferentialTarget k S p),
        IsCompletedDifferentialExtension p σ dhat' → dhat' = dhat) ∧
      ∃ e : ((Fin n → completedRing S p) ⧸
        LinearMap.range
          ((Matrix.toLin' (completedJacobianMatrix (S := S) p n s f π)) :
            (Fin s → completedRing S p) →ₗ[completedRing S p]
              (Fin n → completedRing S p))) ≃ₗ[completedRing S p]
          completedDifferentialTarget k S p,
        ∀ v : Fin n → completedRing S p,
          e ((LinearMap.range
            ((Matrix.toLin' (completedJacobianMatrix (S := S) p n s f π)) :
              (Fin s → completedRing S p) →ₗ[completedRing S p]
                (Fin n → completedRing S p))).mkQ v) =
            completedDifferentialCoordinateMap p n π dhat v := by
  sorry

end AlgebraicGeometry
