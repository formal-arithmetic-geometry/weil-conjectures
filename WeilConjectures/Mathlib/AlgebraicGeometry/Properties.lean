/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Field
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# The dimension of a scheme of finite type over a field

## Main results

* `AlgebraicGeometry.exists_topologicalKrullDim_le`: a quasi-compact scheme of finite type over a
  field has finite Krull dimension.
* `AlgebraicGeometry.topologicalKrullDim_lt_of_ne_univ`: **passing to a proper closed subset
  lowers the dimension.** If `X` is an irreducible quasi-compact scheme of finite type over a
  field and `Z` is a proper irreducible closed subset of `X`, then `dim Z < dim X`.
* `AlgebraicGeometry.topologicalKrullDim_eq_zero_of_finite`: a nonempty scheme of finite type over
  a field with finitely many points has dimension `0`.

The dimension of a scheme is `topologicalKrullDim`, the supremum of the lengths of chains of
irreducible closed subsets. Two elementary comparisons are recorded on the way:
`AlgebraicGeometry.topologicalKrullDim_eq_krullDim` identifies it with the order-theoretic Krull
dimension of the specialization order on the points, and
`AlgebraicGeometry.topologicalKrullDim_eq_ringKrullDim` identifies it with the Krull dimension of
the ring of global sections of an affine scheme.
-/

@[expose] public section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The topological Krull dimension of a scheme is the Krull dimension of its specialization
order, since a scheme is sober and `T0`. -/
theorem topologicalKrullDim_eq_krullDim (X : Scheme.{u}) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints

/-- The dimension of an affine scheme is the Krull dimension of its ring of global sections. -/
theorem topologicalKrullDim_eq_ringKrullDim (Y : Scheme.{u}) [IsAffine Y] :
    topologicalKrullDim Y = ringKrullDim Γ(Y, ⊤) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact IsHomeomorph.topologicalKrullDim_eq _ Y.isoSpec.hom.homeomorph.isHomeomorph

/-- A quasi-compact scheme of finite type over a field has finite dimension.

The scheme is covered by finitely many affine opens, each of them the spectrum of a finitely
generated algebra over the field, hence of finite Krull dimension; and the coheight of a point of
the scheme is the coheight of that point in any open neighbourhood. -/
theorem exists_topologicalKrullDim_le {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] : ∃ n : ℕ, topologicalKrullDim X ≤ n := by
  let 𝒰 := X.affineCover.finiteSubcover
  have hbound : ∀ i, ∃ n : ℕ, topologicalKrullDim (𝒰.X i) ≤ n := by
    intro i
    have hft : RingHom.FiniteType ((𝒰.f i ≫ f).appTop).hom :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
    have hiso : RingHom.FiniteType ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom :=
      RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective
    obtain ⟨n, hn⟩ := (hft.comp hiso).exists_ringKrullDim_le
    exact ⟨n, by rwa [topologicalKrullDim_eq_ringKrullDim]⟩
  choose m hm using hbound
  obtain ⟨n, hn⟩ := (Set.finite_range m).bddAbove
  refine ⟨n, ?_⟩
  rw [topologicalKrullDim_eq_krullDim, Order.krullDim_eq_iSup_coheight]
  have key : ∀ (i : 𝒰.I₀) (y : 𝒰.X i), (Order.coheight ((𝒰.f i).base y) : WithBot ℕ∞) ≤ n := by
    intro i y
    rw [coheight_eq_of_isOpenImmersion (𝒰.f i)]
    calc (Order.coheight y : WithBot ℕ∞) ≤ Order.krullDim (𝒰.X i) := Order.coheight_le_krullDim y
      _ = topologicalKrullDim (𝒰.X i) := (topologicalKrullDim_eq_krullDim _).symm
      _ ≤ (m i : ℕ) := hm i
      _ ≤ (n : ℕ) := by exact_mod_cast hn ⟨i, rfl⟩
  refine iSup_le fun x ↦ ?_
  obtain ⟨y, hy⟩ := 𝒰.covers x
  exact hy ▸ key _ y

/-- **A proper closed subset of an irreducible scheme of finite type over a field has strictly
smaller dimension.**

If `X` is an irreducible quasi-compact scheme of finite type over a field and `Z` is an
irreducible closed subset of `X` other than `X` itself, then `dim Z < dim X`. -/
theorem topologicalKrullDim_lt_of_ne_univ {k : Type u} [Field k] {X : Scheme.{u}}
    [IrreducibleSpace X] [CompactSpace X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    {Z : Set X} (hZc : IsClosed Z) (hZi : IsIrreducible Z) (hZ : Z ≠ Set.univ) :
    topologicalKrullDim Z < topologicalKrullDim X := by
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_le f
  have hle := topologicalKrullDim_add_one_le hZc hZi hZ
  have hZn : topologicalKrullDim Z ≤ (n : ℕ) := (topologicalKrullDim_subspace_le X Z).trans hn
  have hne : topologicalKrullDim Z ≠ ⊥ := by
    have : Nonempty Z := hZi.nonempty.to_subtype
    have : Nonempty (IrreducibleCloseds Z) :=
      ⟨⟨closure {Classical.arbitrary Z}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact (Order.krullDim_ne_bot_iff).mpr inferInstance
  lift topologicalKrullDim Z to ℕ∞ using hne with d hd
  have hdn : d ≤ (n : ℕ∞) := by exact_mod_cast hZn
  lift d to ℕ using ne_top_of_le_ne_top (ENat.natCast_ne_top n) hdn with j
  exact ENat.WithBot.add_one_le_iff.mp hle

/-- A nonempty scheme of finite type over a field with finitely many points has dimension `0`.

A scheme of finite type over a field is a Jacobson space, and a finite Jacobson space is
discrete. -/
theorem topologicalKrullDim_eq_zero_of_finite {k : Type u} [Field k] {X : Scheme.{u}} [Finite X]
    [Nonempty X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    topologicalKrullDim X = 0 := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : Nonempty (IrreducibleCloseds X) :=
    ⟨⟨closure {Classical.arbitrary X}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology X) Order.krullDim_nonneg

end AlgebraicGeometry
