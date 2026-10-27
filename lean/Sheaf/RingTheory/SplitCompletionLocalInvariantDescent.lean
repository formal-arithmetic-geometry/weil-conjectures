/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # Reducedness from a split completed geometric stalk

Source: Stacks Project, curves.tex, Tags 0C49 (lemma-nodal-algebraic), (3) => (1),
and 0C4D (lemma-nodal), arbitrary-field paragraph
(blueprint: lem-sfb-split-completion-local-invariant-descent).

The auxiliary constructions are the evaluation, its kernel point, its local ring,
and its completion specified in the statement. The local map is characterized on
localization generators, which determines it uniquely by the localization universal property.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v w

open scoped TensorProduct

namespace SplitCompletion

/-- Evaluation sends `s ⊗ λ` to `ι (s mod p) * λ`.
Source: Stacks Project, curves.tex, Tags 0C49 and 0C4D
(blueprint: lem-sfb-split-completion-local-invariant-descent). -/
noncomputable def evaluation {k : Type u} {S : Type v} {K : Type w}
    [Field k] [CommRing S] [Field K] [Algebra k S] [Algebra k K]
    (p : Ideal S) (ι : (S ⧸ p) →ₐ[k] K) : S ⊗[k] K →ₐ[k] K :=
  Algebra.TensorProduct.lift (ι.comp (Ideal.Quotient.mkₐ k p)) (AlgHom.id k K)
    (fun _ _ ↦ Commute.all _ _)

/-- The evaluation kernel, bundled with its primeness as a point of the spectrum.
Source: Stacks Project, curves.tex, Tags 0C49 and 0C4D
(blueprint: lem-sfb-split-completion-local-invariant-descent). -/
noncomputable def evaluationPoint {k : Type u} {S : Type v} {K : Type w}
    [Field k] [CommRing S] [Field K] [Algebra k S] [Algebra k K]
    (p : Ideal S) (ι : (S ⧸ p) →ₐ[k] K) : PrimeSpectrum (S ⊗[k] K) :=
  ⟨RingHom.ker (evaluation p ι), RingHom.ker_isPrime (evaluation p ι)⟩

/-- The actual localization `B = (S ⊗ K)_q` at the evaluation kernel.
Source: Stacks Project, curves.tex, Tags 0C49 and 0C4D
(blueprint: lem-sfb-split-completion-local-invariant-descent). -/
noncomputable abbrev geometricStalk {k : Type u} {S : Type v} {K : Type w}
    [Field k] [CommRing S] [Field K] [Algebra k S] [Algebra k K]
    (p : Ideal S) (ι : (S ⧸ p) →ₐ[k] K) :=
  Localization.AtPrime (evaluationPoint p ι).asIdeal

/-- The `qB`-adic completion of the specified geometric stalk.
Source: Stacks Project, curves.tex, Tags 0C49 and 0C4D
(blueprint: lem-sfb-split-completion-local-invariant-descent). -/
noncomputable abbrev completedGeometricStalk {k : Type u} {S : Type v} {K : Type w}
    [Field k] [CommRing S] [Field K] [Algebra k S] [Algebra k K]
    (p : Ideal S) (ι : (S ⧸ p) →ₐ[k] K) :=
  AdicCompletion ((evaluationPoint p ι).asIdeal.map
    (algebraMap (S ⊗[k] K) (geometricStalk p ι))) (geometricStalk p ι)

/-- The split node is reduced and restriction to its two axes is injective.
The coefficient identities specify the actual axis map, including its value on constants.
Source: Stacks Project, curves.tex, Tag 0C49, proof of (3) => (1)
(blueprint: lem-sfb-split-completion-local-invariant-descent).

Proof: Restriction to the axes preserves multiplication by the convolution formula.
Both restrictions vanish precisely when all coefficients on either axis vanish; shifting
both exponents down by one then writes the original series as `uv` times a series.
Thus the kernel is `(uv)`, and the induced quotient map is injective. By
lem-weil-pbc-power-series-domain each one-variable factor is a domain. A nilpotent
maps to zero in both factors, and injectivity makes it zero. These are steps 1 and 2
of the node's proof. -/
theorem split_node_axes (L : Type u) [Field L] :
    IsReduced (MvPowerSeries (Fin 2) L ⧸
      Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) L) * MvPowerSeries.X 1}) ∧
    ∃ E : (MvPowerSeries (Fin 2) L ⧸
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) L) * MvPowerSeries.X 1})
          →+* (PowerSeries L × PowerSeries L),
      Function.Injective E ∧
      ∀ (h : MvPowerSeries (Fin 2) L) (n : ℕ),
        PowerSeries.coeff n (E (Ideal.Quotient.mk _ h)).1 =
          MvPowerSeries.coeff (Finsupp.single 0 n) h ∧
        PowerSeries.coeff n (E (Ideal.Quotient.mk _ h)).2 =
          MvPowerSeries.coeff (Finsupp.single 1 n) h := by
  sorry

/-- Both canonical maps are injective, and a split-node ring isomorphism of the completion
implies reducedness of the completion, geometric stalk, and original local ring.
The equation on `S` characterizes the canonical localized base-change map uniquely;
no extra choice of map or hypothesis about that map is supplied by the caller.
Source: Stacks Project, curves.tex, Tags 0C49, proof of (3) => (1), and 0C4D,
arbitrary-field paragraph
(blueprint: lem-sfb-split-completion-local-invariant-descent).

Proof: Step 3 applies lem-trf-separable-evaluation-local-base-change to the specified
evaluation point: the local rings are Noetherian and their canonical map is faithfully
flat. The zero-ideal case of lem-weil-pbc-faithfully-flat-ideal-contraction proves its
injectivity. Step 4 applies lem-weil-pbc-local-completion-faithfully-flat to `B` and its
maximal ideal `qB`; the same zero-ideal contraction proves injectivity of completion.
For step 5, transport a nilpotent across the ring isomorphism and use split_node_axes.
Then descend its vanishing through the two injections. Only ring operations enter,
so the isomorphism need not preserve `K`-scalars. -/
theorem split_completion_local_invariant_descent
    (k : Type u) (S : Type v) (K : Type w)
    [Field k] [CommRing S] [Field K] [Algebra k S] [Algebra k K]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsMaximal]
    [FiniteDimensional k (S ⧸ p)] [Algebra.IsSeparable k (S ⧸ p)]
    (ι : (S ⧸ p) →ₐ[k] K) :
    ∃ f : Localization.AtPrime p →+* geometricStalk p ι,
      (∀ s : S, f (algebraMap S (Localization.AtPrime p) s) =
        algebraMap (S ⊗[k] K) (geometricStalk p ι) (s ⊗ₜ[k] (1 : K))) ∧
      Function.Injective f ∧
      Function.Injective
        (algebraMap (geometricStalk p ι) (completedGeometricStalk p ι)) ∧
      (Nonempty (completedGeometricStalk p ι ≃+*
          (MvPowerSeries (Fin 2) K ⧸ Ideal.span
            {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) * MvPowerSeries.X 1})) →
        IsReduced (completedGeometricStalk p ι) ∧
        IsReduced (geometricStalk p ι) ∧ IsReduced (Localization.AtPrime p)) := by
  sorry

end SplitCompletion
