/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ContinuousKaehlerDifferential
public import WeilConjectures.RingTheory.CompletedJacobianPresentation
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Localization.Submodule

/-!
# Comparison with continuous differentials after completion

Source: Stacks Project, curves.tex, Tag 0C4D, the completed Jacobian calculation;
algebra.tex, Tags 00RS, 00RU, 00RX; more-algebra.tex, Tag 0C34
(blueprint: lem-trf-completion-kahler-differential-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace Algebra

/-- A continuous extension of the universal differential to the local completion.
Continuity is the neighbourhood-of-zero criterion for the extended maximal-ideal powers.
`CompletedDifferentials` uses the canonical symmetry to put the completion tensor factor first.
Source: Stacks Project, Tag 0C4D; Algebra, Tags 07BK, 00RO and 05GG
(blueprint: lem-trf-completion-kahler-differential-comparison). -/
def IsCompletedDifferentialExtension (k : Type u) (A : Type v)
    [CommRing k] [CommRing A] [Algebra k A] [IsLocalRing A]
    (D : Derivation k (LocalCompletion A) (CompletedDifferentials k A)) : Prop :=
  (∀ a : A, D (algebraMap A (LocalCompletion A) a) =
    (1 : LocalCompletion A) ⊗ₜ[A] KaehlerDifferential.D k A a) ∧
  ∀ r : ℕ, ∃ N : ℕ, ∀ x : LocalCompletion A,
    x ∈ ((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A))) ^ N →
    D x ∈ ((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A))) ^ r •
      (⊤ : Submodule (LocalCompletion A) (CompletedDifferentials k A))

/-- The universal differential extends uniquely and identifies completed differentials with
continuous differentials relative to the specified separable coefficient section. The algebra
structure on the completion is that section; the scalar tower says it is a `k`-algebra map.
Since `p` is maximal, `p.ResidueField` is canonically `S/p`. The isomorphism is uniquely
specified already by the values on differentials of elements of the local ring; its agreement
with the continuous differential is asserted on every element of the completion.

Source: Stacks Project, curves.tex, Tag 0C4D; Algebra, Tags 00RS, 00RU, 00RX, 00RO,
00RT, 00MA, 05GG; More Algebra, Tag 0C34
(blueprint: lem-trf-completion-kahler-differential-comparison).

Proof:
1. A field is Noetherian, finite type preserves Noetherianity, and localization preserves
   Noetherianity. Thus `A = S_p` is Noetherian and its maximal ideal is finitely generated.
   Differentials of finitely many algebra generators generate the differentials of `S`;
   localization of differentials gives finiteness of `M = Ω[A/k]` (00RT). The finite-module
   completion/tensor theorem (00MA) identifies its completion `N` with the displayed tensor.
   Completeness (05GG) identifies the quotients of `N` and of the completed ring with the
   corresponding quotients of `M` and `A`, by their canonical projections.
2. Leibniz gives `d(m^(r+1)) ⊆ m^r M`. Lift `x` modulo `m^(r+1)` to `a` in `A` and define
   `δ_r(x) = da mod m^r M`. Independence of the lift follows from that inclusion. Addition
   and multiplication of lifts prove the derivation identities. The compatible coordinates
   define `D` by completeness, and the same estimate proves continuity. Any other continuous
   extension agrees modulo every `m^r` by lifting sufficiently far; separatedness gives
   uniqueness.
3. The restriction of `D` to the coefficient section factors through `Ω[F/k]`, which vanishes
   for the finite separable field extension (lem-trf-separable-field-differentials-vanish).
   Consequently `D` is an `F`-derivation.
4. Put `B_r = Â/m^rÂ`, `Q_r = N/m^rN`, and `E_r = Ω[B_r/F]`. Universality of differentials
   yields `α_r : Q_r → E_r` from `da ↦ d(a mod m^r)`. The quotient maps commute with these
   maps on differential generators, hence they define `Φ : N → lim E_r`.
5. The derivation `δ_r` kills both the coefficient field and `m^(r+1)Â`. Universality gives
   `β_r : E_(r+1) → Q_r`. These maps satisfy `q_r β_(r+1) = β_r t_(r+1)` on generators.
   For a compatible family `z`, use the coordinates `β_r(z_(r+1))` and completeness to
   construct `Ψ : lim E_r → N`. Both constructions are linear over the completion.
6. On generators, `β_r α_(r+1) = q_r` and `α_r β_r = t_r`; symbols from `B_(r+1)` lift
   from `A`. Componentwise these identities give `ΨΦ = id` and `ΦΨ = id`, including at
   the first positive index.
7. Lifting `x` modulo `m^(r+1)` shows `Φ(D x)_r = d(x mod m^r)` for every `x`. In
   particular it has the required values on `1 ⊗ da`. These tensors generate the tensor
   module over the completion, proving uniqueness of the linear isomorphism from those
   values alone. Step 2 gives the independent uniqueness of the extension.
-/
theorem completion_kahler_differential_comparison
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (hS : (algebraMap k S).FiniteType) (p : Ideal S) [p.IsMaximal]
    [FiniteDimensional k p.ResidueField] [Algebra.IsSeparable k p.ResidueField]
    [Algebra p.ResidueField (LocalCompletion (Localization.AtPrime p))]
    [IsScalarTower k p.ResidueField (LocalCompletion (Localization.AtPrime p))]
    (hσ : ∀ c : p.ResidueField,
      AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (algebraMap p.ResidueField (LocalCompletion (Localization.AtPrime p)) c) = c) :
    ∃ D : Derivation k (LocalCompletion (Localization.AtPrime p))
        (CompletedDifferentials k (Localization.AtPrime p)),
      IsCompletedDifferentialExtension k (Localization.AtPrime p) D ∧
      (∀ D' : Derivation k (LocalCompletion (Localization.AtPrime p))
          (CompletedDifferentials k (Localization.AtPrime p)),
        IsCompletedDifferentialExtension k (Localization.AtPrime p) D' → D' = D) ∧
      ∃ e : CompletedDifferentials k (Localization.AtPrime p) ≃ₗ[
          LocalCompletion (Localization.AtPrime p)]
          KaehlerDifferential.Continuous p.ResidueField (LocalCompletion (Localization.AtPrime p))
            ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
              (algebraMap (Localization.AtPrime p) (LocalCompletion (Localization.AtPrime p)))),
        (∀ a : Localization.AtPrime p,
          e ((1 : LocalCompletion (Localization.AtPrime p)) ⊗ₜ[Localization.AtPrime p]
              KaehlerDifferential.D k (Localization.AtPrime p) a) =
            KaehlerDifferential.continuousD _ _ _
              (algebraMap (Localization.AtPrime p) (LocalCompletion (Localization.AtPrime p)) a)) ∧
        (∀ e' : CompletedDifferentials k (Localization.AtPrime p) ≃ₗ[
            LocalCompletion (Localization.AtPrime p)]
            KaehlerDifferential.Continuous p.ResidueField
              (LocalCompletion (Localization.AtPrime p))
              ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
                (algebraMap (Localization.AtPrime p) (LocalCompletion (Localization.AtPrime p)))),
          (∀ a : Localization.AtPrime p,
            e' ((1 : LocalCompletion (Localization.AtPrime p)) ⊗ₜ[Localization.AtPrime p]
                KaehlerDifferential.D k (Localization.AtPrime p) a) =
              KaehlerDifferential.continuousD _ _ _
                (algebraMap (Localization.AtPrime p)
                  (LocalCompletion (Localization.AtPrime p)) a)) →
          e' = e) ∧
        ∀ x : LocalCompletion (Localization.AtPrime p),
          e (D x) = KaehlerDifferential.continuousD _ _ _ x := by
  sorry

end Algebra
