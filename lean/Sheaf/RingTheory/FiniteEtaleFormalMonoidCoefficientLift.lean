/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup

import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import WeilConjectures.RingTheory.CompleteLocalQuotient
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.Locus
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Sheaf.RingTheory.HenselianFiniteEtaleEquivalence
import WeilConjectures.RingTheory.FiniteModuleComplete
import Sheaf.RingTheory.RegularLocalLocalization
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.RingHom.Etale
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Finite étale coefficient lifts for formal monoid rings

Source: Stacks Project, Tags 09ZL, 07NF and 031B, with the finite-basis
formal-monoid calculation used in ILO VI 2.3
(blueprint: lem-per-finite-etale-formal-monoid-coefficient-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace AdicCompletion

/-- The canonical map on completions induced by a ring map, completing the target at
its extended ideal. It is constructed at every quotient level, not chosen from an
existence assertion. Source: the inverse-limit definition of adic completion,
Stacks Tag 0317 (blueprint: lem-per-finite-etale-formal-monoid-coefficient-lift). -/
noncomputable def mapRingHomAlong {R : Type u} {T : Type v} [CommRing R] [CommRing T]
    (I : Ideal R) (φ : R →+* T) :
    AdicCompletion I R →+* AdicCompletion (Ideal.map φ I) T :=
  AdicCompletion.liftRingHom (Ideal.map φ I)
    (fun n ↦ (Ideal.quotientMap ((Ideal.map φ I) ^ n) φ
      (Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_pow]))).comp
        (AdicCompletion.evalₐ I n).toRingHom)
    (fun {m n} hmn ↦ by
      ext x
      obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
      simpa using congrArg
        (Ideal.quotientMap ((Ideal.map φ I) ^ m) φ
          (Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_pow])))
        (AdicCompletion.Ideal.mk_eq_mk I hmn a))

end AdicCompletion

namespace AddMonoidAlgebra

/-- Coefficientwise extension of a completed monoid algebra. The target is completed
at the extended ideal; when `m_D = m_E D` this is exactly `(m_D,[s]:s≠0)`.
Source: the finite-basis calculation for ILO VI 2.3
(blueprint: lem-per-finite-etale-formal-monoid-coefficient-lift). -/
noncomputable def formalCoefficientMap (E : Type u) [CommRing E]
    (S : Type v) [AddCommMonoid S] (a : Ideal (AddMonoidAlgebra E S))
    (D : Type w) [CommRing D] [Algebra E D] :=
  AdicCompletion.mapRingHomAlong a (AddMonoidAlgebra.mapRingHom S (algebraMap E D))

/-- The formal monoid hypersurface after the specified coefficient extension.
This is the actual quotient by the coefficientwise image of `f`.
Source: ILO VI 2.3 and the quotient calculation following Stacks Tag 09ZL
(blueprint: lem-per-finite-etale-formal-monoid-coefficient-lift). -/
abbrev CoefficientHypersurface (E : Type u) [CommRing E]
    (S : Type v) [AddCommMonoid S] (a : Ideal (AddMonoidAlgebra E S))
    (f : AdicCompletion a (AddMonoidAlgebra E S))
    (D : Type w) [CommRing D] [Algebra E D] :=
  AdicCompletion (Ideal.map (AddMonoidAlgebra.mapRingHom S (algebraMap E D)) a)
    (AddMonoidAlgebra D S) ⧸ Ideal.span {formalCoefficientMap E S a D f}

/-- The quotient topology on the coefficient-extended formal monoid hypersurface.
It is defined by the image of the completion ideal, and is the maximal-ideal topology
under the hypotheses of the coefficient-lifting theorem.
Source: ILO VI 2.3 and Stacks Tag 05GG
(blueprint: lem-per-finite-etale-formal-monoid-coefficient-lift). -/
@[instance_reducible]
noncomputable def coefficientHypersurfaceTopology (E : Type u) [CommRing E]
    (S : Type v) [AddCommMonoid S] (a : Ideal (AddMonoidAlgebra E S))
    (f : AdicCompletion a (AddMonoidAlgebra E S))
    (D : Type w) [CommRing D] [Algebra E D] :
    TopologicalSpace (CoefficientHypersurface E S a f D) :=
  (Ideal.map (Ideal.Quotient.mk (Ideal.span {formalCoefficientMap E S a D f}))
    (Ideal.map (algebraMap (AddMonoidAlgebra D S) _)
      (Ideal.map (AddMonoidAlgebra.mapRingHom S (algebraMap E D)) a))).adicTopology

/-- A local finite étale algebra over `E[[S]]/(f)` comes from a complete regular local
finite étale coefficient algebra `D`. The displayed identity on every `h` expresses
precisely that the equivalence is an `E[[S]]/(f)`-algebra equivalence. Continuity uses
the maximal-ideal topology on `K` and the quotient completion topology on the target.

Source: Stacks Tags 09ZL, 07NF and 031B, with the explicit formal-monoid finite-basis
calculation used in ILO VI 2.3
(blueprint: lem-per-finite-etale-formal-monoid-coefficient-lift).

Proof plan:
1. Sharpness gives the augmentation `E[S] → E`. Finite generation makes `E[S]`
   Noetherian, and completion permanence and Tag 05GG make its completion complete
   Noetherian with residue field `k = E/m_E`.
2. Geometric series make the completion local with maximal ideal `aH`. Quotienting
   by `f` gives a complete Noetherian local ring `A₀` (Tag 0325); completeness makes
   `E` and `A₀` henselian (Tag 0ALJ).
3. Integrality and maximal contraction, followed by the étale local calculation
   (Tags 00GK, 00OI, 00U4), give `m_K = m_A₀ K`. Its residue field `L` is finite
   separable over `k`, hence finite étale (Tag 00U3).
4. Essential surjectivity of the henselian finite-étale equivalence (04GK/09ZL)
   lifts `L` to a finite étale `E`-algebra `D`. Maximal contraction and the field
   quotient show that `D` is local with `m_D = m_E D`. Finite-module completeness
   makes it complete; finite-type permanence makes it Noetherian.
5. Étale implies smooth, so regularity ascends to `D` (Tag 07NF).
6. Étale flatness and the finite-flat-local theorem (00NZ) make `D` finite free.
7. In a finite `E`-basis of `D`, every quotient modulo `a^n` and its inverse limit
   is a finite direct sum. Thus `D ⊗[E] H ≅ D[[S]]` by the actual coefficient map.
8. Multiplication by `f` acts coordinatewise, giving
   `D ⊗[E] A₀ ≅ D[[S]]/(f)` without requiring `f ≠ 0`.
9. Étale base change and full faithfulness of 04GK over `A₀` identify this algebra
   with `K`, since both reduce to `L`.
10. Tag 05GG and the geometric-series argument identify the quotient completion
    topology with the maximal-ideal topology. The isomorphism matches all powers
    of maximal ideals and is continuous in both directions.
11. The local flat map `E → D` is faithfully flat (00HR). Contraction of `m_E²`
    (05CK) then preserves every class in `m_E \ m_E²`.
-/
theorem finiteEtale_formalMonoid_coefficientLift
    (E : Type u) [CommRing E] [IsRegularLocalRing E]
    [IsAdicComplete (IsLocalRing.maximalIdeal E) E]
    (S : Type v) [AddCommMonoid S]
    (hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative S))
    (hsharp : ∀ s : S, IsUnit (Multiplicative.ofAdd s) → s = 0)
    (a : Ideal (AddMonoidAlgebra E S))
    (ha : a = Ideal.map (algebraMap E (AddMonoidAlgebra E S))
      (IsLocalRing.maximalIdeal E) ⊔
        Ideal.span {b | ∃ s : S, s ≠ 0 ∧ b = single s (1 : E)})
    (f : AdicCompletion a (AddMonoidAlgebra E S))
    (hf : f ∈ Ideal.map (algebraMap (AddMonoidAlgebra E S) _) a)
    (K : Type w) [CommRing K] [IsLocalRing K]
    [Algebra (AdicCompletion a (AddMonoidAlgebra E S) ⧸ Ideal.span {f}) K]
    [Module.Finite (AdicCompletion a (AddMonoidAlgebra E S) ⧸ Ideal.span {f}) K]
    [Algebra.Etale (AdicCompletion a (AddMonoidAlgebra E S) ⧸ Ideal.span {f}) K] :
    ∃ (D : Type (max u v w)) (_ : CommRing D) (_ : IsRegularLocalRing D)
      (_ : Algebra E D),
      Module.Finite E D ∧ Algebra.Etale E D ∧
      IsAdicComplete (IsLocalRing.maximalIdeal D) D ∧
      Nonempty (IsLocalRing.ResidueField D ≃+* IsLocalRing.ResidueField K) ∧
      IsLocalRing.maximalIdeal D = Ideal.map (algebraMap E D) (IsLocalRing.maximalIdeal E) ∧
      (∀ x : E, x ∈ IsLocalRing.maximalIdeal E →
        x ∉ (IsLocalRing.maximalIdeal E) ^ 2 →
        algebraMap E D x ∈ IsLocalRing.maximalIdeal D ∧
          algebraMap E D x ∉ (IsLocalRing.maximalIdeal D) ^ 2) ∧
      ∃ e : K ≃+* CoefficientHypersurface E S a f D,
        (∀ h : AdicCompletion a (AddMonoidAlgebra E S),
          e (algebraMap (AdicCompletion a (AddMonoidAlgebra E S) ⧸ Ideal.span {f}) K
              (Ideal.Quotient.mk (Ideal.span {f}) h)) =
            Ideal.Quotient.mk (Ideal.span {formalCoefficientMap E S a D f})
              (formalCoefficientMap E S a D h)) ∧
        @Continuous K (CoefficientHypersurface E S a f D)
          (IsLocalRing.maximalIdeal K).adicTopology
          (coefficientHypersurfaceTopology E S a f D) e ∧
        @Continuous (CoefficientHypersurface E S a f D) K
          (coefficientHypersurfaceTopology E S a f D)
          (IsLocalRing.maximalIdeal K).adicTopology e.symm := by
  sorry

end AddMonoidAlgebra
