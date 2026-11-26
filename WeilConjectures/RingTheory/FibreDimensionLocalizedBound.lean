/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Topology.LocalAtTarget
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-!
# A localized fibre comparison used by the principal-neighbourhood theorem

If every point of a basic open `D(g) ⊆ Spec S` has local fibre dimension at most `d`, then every
nonempty fibre of `R → S_g` has dimension at most `d`.

## Implementation details

For a base prime `p`, put `F = κ(p) ⊗[R] S` and `a = 1 ⊗ g`. Base change of principal
localization identifies `κ(p) ⊗[R] S_g` with `F_a`, and `Spec F_a` embeds as the open `D(a)` of
`Spec F`. Local dimension is monotone along inducing maps and unchanged on open subspaces, so
each point of the localized fibre has dimension at most `d`; the dimension-supremum formula then
bounds the whole fibre. Empty fibres are covered too, their dimension being `⊥`.

## References

* [Stacks, Tag 00DK], [Stacks, Tag 00DL], [Stacks, Tag 00E4], [Stacks, Tag 0B7I]
-/

@[expose] public section

universe u v

namespace Algebra

/-- For an inducing map `f`, the local dimension at `x` is at most the local dimension
at `f x`. -/
private theorem dimAt_inducing_le {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Topology.IsInducing f) (x : X) :
    topologicalKrullDimAt x ≤ topologicalKrullDimAt (f x) := by
  refine le_iInf₂ fun U hx ↦ ?_
  let V : TopologicalSpace.Opens X := ⟨f ⁻¹' U, U.isOpen.preimage hf.continuous⟩
  exact (iInf₂_le V hx).trans
    ((hf.restrictPreimage (U : Set Y)).topologicalKrullDim_le)

/-- Reindex the fibre bound at a fixed base prime using the fibre equivalence. -/
private theorem fibre_bound_at_fixed_base
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (g : S) (d : ℕ)
    (hV : ∀ q : PrimeSpectrum S, q ∈ PrimeSpectrum.basicOpen g →
      topologicalKrullDimAt
        (PrimeSpectrum.preimageEquivFiber R S (PrimeSpectrum.comap (algebraMap R S) q)
          ⟨q, rfl⟩) ≤ (d : WithBot ℕ∞))
    (p : PrimeSpectrum R) (Q : PrimeSpectrum (p.asIdeal.Fiber S))
    (hg : _root_.TensorProduct.tmul R (1 : p.asIdeal.ResidueField) g ∉ Q.asIdeal) :
    topologicalKrullDimAt Q ≤ (d : WithBot ℕ∞) := by
  obtain ⟨⟨q, hq⟩, rfl⟩ := (PrimeSpectrum.preimageEquivFiber R S p).surjective Q
  have hp : PrimeSpectrum.comap (algebraMap R S) q = p := hq
  subst p
  apply hV q
  change g ∉ q.asIdeal
  let e := PrimeSpectrum.preimageEquivFiber R S (PrimeSpectrum.comap (algebraMap R S) q)
  have he := congrArg Subtype.val (e.symm_apply_apply ⟨q, rfl⟩)
  change g ∉ (PrimeSpectrum.comap TensorProduct.includeRight.toRingHom
    (PrimeSpectrum.preimageEquivFiber R S (PrimeSpectrum.comap (algebraMap R S) q)
      ⟨q, rfl⟩)).asIdeal at hg
  change PrimeSpectrum.comap TensorProduct.includeRight.toRingHom
    (PrimeSpectrum.preimageEquivFiber R S (PrimeSpectrum.comap (algebraMap R S) q)
      ⟨q, rfl⟩) = q at he
  rwa [he] at hg

/-- If all points of the basic open `D(g)` have local fibre dimension at most `d`,
then every nonempty fibre after localizing away from `g` has global dimension at most `d`. -/
theorem localized_fibre_dimension_le_of_basicOpen
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [FiniteType R S] (g : S) (d : ℕ)
    (hV : ∀ q' : PrimeSpectrum S, q' ∈ PrimeSpectrum.basicOpen g →
      topologicalKrullDimAt
        (PrimeSpectrum.preimageEquivFiber R S (PrimeSpectrum.comap (algebraMap R S) q')
          ⟨q', rfl⟩) ≤ (d : WithBot ℕ∞)) :
    ∀ p' : PrimeSpectrum R,
      Nontrivial (p'.asIdeal.Fiber (Localization.Away g)) →
        topologicalKrullDim (PrimeSpectrum (p'.asIdeal.Fiber (Localization.Away g))) ≤
          (d : WithBot ℕ∞) := by
  intro p _
  let k := p.asIdeal.ResidueField
  let F := p.asIdeal.Fiber S
  let F₁ := p.asIdeal.Fiber (Localization.Away g)
  let a : F := _root_.TensorProduct.tmul R (1 : k) g
  let e : F₁ ≃ₐ[k] Localization.Away a :=
    IsLocalization.Away.tensorProductEquivTMulRight R k g (Localization.Away g)
  let E := PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
  let f := PrimeSpectrum.comap (algebraMap F (Localization.Away a))
  have hf := PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away a) a
  rw [topologicalKrullDim_eq_iSup_topologicalKrullDimAt]
  refine iSup_le fun Q₁ ↦ ?_
  let Qg := E Q₁
  let Q := f Qg
  have ha : a ∉ Q.asIdeal := by
    have hmem : Q ∈ Set.range f := ⟨Qg, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away a) a] at hmem
    exact hmem
  have hQ := fibre_bound_at_fixed_base g d hV p Q ha
  let H := hf.toIsEmbedding.toHomeomorph
  have hlocal := dimAt_inducing_le H.isEmbedding.toIsInducing Qg
  have hopen := hf.isOpen_range.topologicalKrullDimAt_eq
    (show f Qg ∈ Set.range f from ⟨Qg, rfl⟩)
  exact (dimAt_inducing_le E.isEmbedding.toIsInducing Q₁).trans
    (hlocal.trans (hopen.le.trans hQ))

end Algebra
