/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Quasi-finiteness at a prime and zero dimension of the fibre at that point

Source: Stacks Project, Morphisms, Tag 0397, second proof, and Properties, Tag 0H7C
(blueprint: lem-weil-pbc-ring-quasifinite-zero-fibre-dimension).
-/

@[expose] public section

universe u v

namespace Algebra

/-- For a finite-type ring map, quasi-finiteness at a prime is equivalent to dimension zero
at the corresponding point of the fibre spectrum. The fibre is written `κ(p) ⊗[R] T`,
canonically isomorphic to `T ⊗[R] κ(p)` by tensor commutation. Its spectrum is the underlying
space of `Spec` of the fibre ring, and `preimageHomeomorphFiber` supplies the unique fibre
prime contracting to `q`.

Source: Stacks Project, Morphisms, Tag 0397, second proof; Properties, Tag 0H7C
(blueprint: lem-weil-pbc-ring-quasifinite-zero-fibre-dimension).

Proof:
1. Base change preserves finite type, so the fibre is a finite-type algebra over the
   residue field. It is therefore a Noetherian ring, and its spectrum is Noetherian.
2. If the singleton of the fibre point is open, its dimension is at most zero because
   it is discrete. Every neighbourhood contains the point, so its dimension is nonnegative.
   Taking the infimum proves that the local dimension is zero.
3. Conversely, if the infimum is zero, some open neighbourhood has dimension less than
   one, hence at most zero. The subspace is Noetherian and T0. Apply the existing
   topological finiteness and closed-singleton theorem to its whole closed subset.
4. A finite T1 space is discrete, so the singleton is open in the neighbourhood.
   The neighbourhood's open inclusion sends this singleton to an open singleton in the
   fibre spectrum, which is exactly quasi-finiteness at the original prime. -/
theorem isQuasiFiniteAtPrime_iff_topologicalKrullDimAt_eq_zero
    (R : Type u) (T : Type v) [CommRing R] [CommRing T]
    [Algebra R T] [Algebra.FiniteType R T] (q : PrimeSpectrum T) :
    IsQuasiFiniteAtPrime R T q ↔
      topologicalKrullDimAt
        (PrimeSpectrum.preimageHomeomorphFiber R T (q.comap (algebraMap R T))
          ⟨q, rfl⟩) = 0 := by
  classical
  let p := q.comap (algebraMap R T)
  let X := PrimeSpectrum (p.asIdeal.Fiber T)
  let x : X := PrimeSpectrum.preimageHomeomorphFiber R T p ⟨q, rfl⟩
  change IsOpen ({x} : Set X) ↔ topologicalKrullDimAt x = 0
  have hnonneg (U : TopologicalSpace.Opens X) (hx : x ∈ U) :
      0 ≤ topologicalKrullDim U := by
    have : Nonempty (TopologicalSpace.IrreducibleCloseds U) :=
      ⟨⟨closure {(⟨x, hx⟩ : U)}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_nonneg
  constructor
  · intro hx
    let U : TopologicalSpace.Opens X := ⟨{x}, hx⟩
    have hxU : x ∈ U := Set.mem_singleton x
    have : Subsingleton U := ⟨fun a b ↦ Subtype.ext (a.property.trans b.property.symm)⟩
    apply le_antisymm
    · exact (iInf₂_le U hxU).trans (topologicalKrullDim_zero_of_discreteTopology U)
    · exact le_iInf₂ hnonneg
  · intro hx
    have : IsNoetherianRing (p.asIdeal.Fiber T) :=
      Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField (p.asIdeal.Fiber T)
    have : TopologicalSpace.NoetherianSpace X :=
      inferInstanceAs (TopologicalSpace.NoetherianSpace (PrimeSpectrum (p.asIdeal.Fiber T)))
    have hlt : topologicalKrullDimAt x < (0 : WithBot ℕ∞) + 1 := by
      rw [hx]
      exact ENat.WithBot.lt_add_one_iff.mpr le_rfl
    obtain ⟨U, hU⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hxU, hdim⟩ := iInf_lt_iff.mp hU
    have : TopologicalSpace.NoetherianSpace U :=
      Topology.IsInducing.subtypeVal.noetherianSpace
    have hdimU : topologicalKrullDim U ≤ 0 := ENat.WithBot.lt_add_one_iff.mp hdim
    have h :=
      IsClosed.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero
        (X := U) (Z := (Set.univ : Set U)) isClosed_univ (by
          rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ U).isHomeomorph]
          exact hdimU)
    have : Finite U := Set.finite_univ_iff.mp h.1
    have : T1Space U := ⟨fun y ↦ by simpa using h.2 y trivial⟩
    have : DiscreteTopology U := inferInstance
    have hopen := U.isOpen.isOpenMap_subtype_val _
      (isOpen_discrete ({⟨x, hxU⟩} : Set U))
    simpa using hopen

end Algebra
