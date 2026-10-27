/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q155
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.PrimitiveElement
import WeilConjectures.RingTheory.HenselianLocalRootLifting
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.SeparableDegree
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas

/-!
# Tame equivariant Cohen–Gabber presentations

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé IV, Theorem 2.2.2
and 2.2.4–2.2.6, printed pp.53–55; perfect constants: IV 2.1.4
(blueprint: lem-per-tame-equivariant-cohen-gabber).

The auxiliary predicate merely spells out the promised presentation. Its algebra
structure on the target is the one induced by the displayed evaluation map.
Continuity is expressed by the ideal-power criterion, so no topology on the
complete local ring has to be supplied. Constants, variables and continuity
characterize formal evaluation uniquely in an adically separated target.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace IsLocalRing

/-- The clauses of the tame equivariant Cohen–Gabber presentation for a given
coefficient section, tuple, and evaluation map. The generic fibre is written with
scalars on the left, canonically the same algebra as `C ⊗[R] FractionRing R`.
The `letI` binding selects the actual algebra structure induced by `f`,
not an extra hypothesis or existential choice.

Source: ILO, Exposé IV, 2.2.2 and 2.2.4–2.2.6, printed pp.53–55
(blueprint: lem-per-tame-equivariant-cohen-gabber). -/
def IsTameEquivariantCohenGabberPresentation
    (C : Type u) [CommRing C] [IsLocalRing C]
    (H : Type v) [Group H] (ρ : H →* RingAut C) (e : ℕ)
    (s : ResidueField C →+* C) (x : Fin e → C)
    (f : MvPowerSeries (Fin e) (ResidueField C) →+* C) : Prop :=
  letI := f.toAlgebra
  (residue C).comp s = RingHom.id (ResidueField C) ∧
  (∀ (h : H) (a : ResidueField C), ρ h (s a) = s (ResidueField.mapEquiv (ρ h) a)) ∧
  (∀ i : Fin e, x i ∈ maximalIdeal C) ∧
  (∀ (h : H) (i : Fin e), ρ h (x i) = x i) ∧
  (∀ a : ResidueField C, f (MvPowerSeries.C a) = s a) ∧
  (∀ i : Fin e, f (MvPowerSeries.X i) = x i) ∧
  (∀ r : ℕ, ∃ N : ℕ,
    ((Ideal.span (Set.range (fun i : Fin e ↦
      (MvPowerSeries.X i : MvPowerSeries (Fin e) (ResidueField C))))) ^ N).map f ≤
        maximalIdeal C ^ r) ∧
  Function.Injective f ∧ IsLocalHom f ∧
  Module.Finite (MvPowerSeries (Fin e) (ResidueField C)) C ∧
  Module.IsTorsionFree (MvPowerSeries (Fin e) (ResidueField C)) C ∧
  (∀ F : MvPowerSeries (Fin e) (ResidueField C),
    residue C (f F) = MvPowerSeries.constantCoeff F) ∧
  (Ideal.span (Set.range x)).radical = maximalIdeal C ∧
  (∀ (h : H) (F : MvPowerSeries (Fin e) (ResidueField C)),
    ρ h (f F) = f (MvPowerSeries.map (ResidueField.mapEquiv (ρ h)).toRingHom F)) ∧
  (∃ (n : ℕ) (L : Fin n → Type u) (_ : ∀ i : Fin n, Field (L i))
      (_ : ∀ i : Fin n, Algebra (FractionRing (MvPowerSeries (Fin e) (ResidueField C)))
        (L i)),
    (∀ i : Fin n,
      Module.Finite (FractionRing (MvPowerSeries (Fin e) (ResidueField C))) (L i) ∧
      Algebra.IsSeparable (FractionRing (MvPowerSeries (Fin e) (ResidueField C))) (L i)) ∧
    Nonempty ((FractionRing (MvPowerSeries (Fin e) (ResidueField C)) ⊗[
      MvPowerSeries (Fin e) (ResidueField C)] C) ≃ₐ[
      FractionRing (MvPowerSeries (Fin e) (ResidueField C))] (∀ i : Fin n, L i)))

/-- A reduced equidimensional complete local ring in positive characteristic admits
an equivariant coefficient field and fixed parameters giving a finite torsion-free,
generically separable formal normalization for a tame finite group action.
`constants = none` specifies no subfield. For `some ι`, the subfield is perfect,
stable under the given action, and the resulting section agrees with its inclusion.

Source: ILO, Exposé IV, Theorem 2.2.2 and 2.2.4–2.2.6, printed pp.53–55;
perfect-subfield compatibility: IV 2.1.4
(blueprint: lem-per-tame-equivariant-cohen-gabber).

Proof:
1. Apply lem-per-tame-fixed-ring-generic-components to B = C^H. The ring B is
   reduced complete Noetherian local, equidimensional of dimension e; its residue
   field is λ = k^H. The extensions C/B and k/λ are finite, the latter separable.
   Each generic component field of C is finite separable over that of B.
2. By lem-per-coefficient-field-generic-differential-basis choose a coefficient
   section λ → B and a_i in its maximal ideal with generically independent
   differentials. Choose parameters τ_i by
   lem-weil-pbc-noetherian-local-system-of-parameters. Put u_i = τ_i^p(1+a_i).
   Their ideal has maximal radical since 1+a_i are units. Case (a) of
   lem-per-parameter-ideal-formal-normalization gives a finite injective
   torsion-free map R₀ = λ[[T]] → B and its generic product of component fields.
3. Compute d(u_i) = τ_i^p d(a_i). Apply the same normalization lemma to τ:
   torsion-freeness makes each τ_i nonzero on every generic component. Thus d(u_i)
   are still a generic basis. Apply lem-per-finite-formal-map-differential-cokernel
   and lem-weil-pbc-tensor-right-exact. The resulting relative differentials vanish
   on every component. Use lem-weil-pbc-kahler-differentials-localization first
   over R₀ minus zero and then at each component idempotent; derivations also
   annihilate inverses from R₀. The universal property
   def-weil-pbc-kahler-differentials and
   lem-weil-pbc-fg-field-zero-differentials-separable give generic separability.
4. By lem-weil-pbc-complete-pair-henselian C is henselian. Choose a primitive
   element of k/λ by lem-weil-pbc-finite-separable-primitive-element. Lift its
   simple minimal-polynomial root by lem-weil-pbc-henselian-local-root-lifting
   and use lem-weil-pbc-minimal-polynomial-quotient-field-iso to obtain s : k → C.
   It is a residue section. By lem-weil-pbc-simple-root-uniqueness it is the unique
   λ-algebra section; conjugating by H therefore proves its equivariance.
5. The u_i belong to B and are H-fixed. By lem-weil-pbc-finite-algebra-is-integral
   and lem-weil-pbc-integral-prime-over-maximal-maximal their ideal in C has
   maximal radical. Apply lem-per-parameter-ideal-formal-normalization to C, s, u.
   It gives the injective local finite torsion-free map with identity residue map
   and generic product of finite component fields. Evaluation is adically continuous.
   It is equivariant on polynomial truncations; adic separation
   (def-weil-pbc-adically-complete-ring) then gives equivariance on all series.
6. For every generic component field L of C the tower K₀ ⊂ M ⊂ L is separable
   by step 3 and step 1, using lem-zl-separable-permanence. Since s extends the
   section on B, K₀ ⊂ Frac(k[[T]]) ⊂ L. Apply
   lem-sfb-separable-algebraic-intermediate-base; the component extensions over
   Frac(k[[T]]) are finite by step 5 and separable by this tower argument.
7. For a in a specified perfect subfield choose a_N with a_N^(p^N) = a. Then
   s(residue a_N) - a_N lies in the maximal ideal. By def-weil-ring-frobenius,
   s(residue a) - a is its p^N-th power, hence lies in every maximal-ideal power.
   Separation forces it to vanish, even when H acts nontrivially on the subfield. -/
theorem tame_equivariant_cohen_gabber
    (p : ℕ) [Fact p.Prime] (C : Type u) [CommRing C] [IsLocalRing C]
    [IsNoetherianRing C] [IsReduced C] [CharP C p]
    [IsAdicComplete (maximalIdeal C) C]
    (e : ℕ) (he : 1 ≤ e) (hdim : ringKrullDim C = (e : WithBot ℕ∞))
    (hequidim : ∀ q : Ideal C, IsMinimalPrime q →
      ringKrullDim (C ⧸ q) = (e : WithBot ℕ∞))
    (H : Type v) [Group H] [Finite H] (ρ : H →* RingAut C)
    (htame : IsUnit (Nat.card H : ResidueField C))
    (K₀ : Type w) [Field K₀] (constants : Option (K₀ →+* C))
    (hperfect : ∀ ι : K₀ →+* C, constants = some ι →
      Function.Bijective (fun a : K₀ ↦ a ^ p))
    (hstable : ∀ ι : K₀ →+* C, constants = some ι →
      ∀ (h : H) (a : K₀), ∃ b : K₀, ρ h (ι a) = ι b) :
    ∃ (s : ResidueField C →+* C) (x : Fin e → C)
      (f : MvPowerSeries (Fin e) (ResidueField C) →+* C),
      IsTameEquivariantCohenGabberPresentation C H ρ e s x f ∧
      (∀ ι : K₀ →+* C, constants = some ι →
        ∀ a : K₀, s (residue C (ι a)) = ι a) := by
  sorry

end IsLocalRing
