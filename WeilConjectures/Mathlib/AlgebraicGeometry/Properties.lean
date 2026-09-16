/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import WeilConjectures.Mathlib.Data.ENat.Basic
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Field
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# The dimension of a scheme of finite type over a field, and Krull's principal ideal theorem

## Main results

* `AlgebraicGeometry.exists_topologicalKrullDim_le`: a quasi-compact scheme of finite type over a
  field has finite Krull dimension.
* `AlgebraicGeometry.topologicalKrullDim_lt_of_ne_univ`: **passing to a proper closed subset
  lowers the dimension.** If `X` is an irreducible quasi-compact scheme of finite type over a
  field and `Z` is a closed subset of `X` other than `X` itself, then `dim Z < dim X`.
* `AlgebraicGeometry.topologicalKrullDim_eq_zero_of_finite`: a nonempty scheme of finite type over
  a field with finitely many points has dimension `0`.
* `AlgebraicGeometry.coheight_le_one_of_minimal_notMem_basicOpen` and
  `AlgebraicGeometry.coheight_le_one_of_minimal_mem_zeroLocus`: **Krull's principal ideal theorem
  for schemes.** On a locally Noetherian scheme every irreducible component of the vanishing locus
  of a section of the structure sheaf has codimension at most `1`. The codimension of a point is
  its `Order.coheight`, compared with the height of the corresponding prime ideal by
  `AlgebraicGeometry.IsAffineOpen.coheight_fromSpec`.

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

If `X` is an irreducible quasi-compact scheme of finite type over a field and `Z` is a closed
subset of `X` other than `X` itself, then `dim Z < dim X`.

This is the case `S = univ` of `topologicalKrullDim_lt_of_forall_maximal`: in an irreducible
space the only maximal irreducible subset of `univ` is `univ` itself. -/
theorem topologicalKrullDim_lt_of_ne_univ {k : Type u} [Field k] {X : Scheme.{u}}
    [IrreducibleSpace X] [CompactSpace X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    {Z : Set X} (hZc : IsClosed Z) (hZ : Z ≠ Set.univ) :
    topologicalKrullDim Z < topologicalKrullDim X := by
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_le f
  rw [← topologicalKrullDim_univ X]
  refine topologicalKrullDim_lt_of_forall_maximal (Set.subset_univ Z)
    (hZc.preimage continuous_subtype_val) Set.univ_nonempty ?_
    fun _ hT hTZ ↦ hZ (Set.univ_subset_iff.1 (eq_univ_of_maximal_isIrreducible hT ▸ hTZ))
  rw [topologicalKrullDim_univ]
  exact ne_top_of_le_ne_top (ENat.WithBot.natCast_ne_top n) hn

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

/-!
## Krull's principal ideal theorem for schemes

A point `z` of the vanishing locus of a section `f` of `𝒪_X` is the generic point of an
irreducible component of that vanishing locus exactly when no other point of the vanishing locus
generalizes to `z`. Krull's principal ideal theorem says that such a `z` has codimension at most
one in `X`, the codimension of `z` being `Order.coheight z`, the supremum of the lengths of the
chains of generalizations of `z`.

The statement for a section `s` of a line bundle `L` on `X` — every irreducible component of the
zero scheme of `s` has codimension at most one — follows from the statement below by trivialising
`L` on an affine open neighbourhood of `z`, on which `s` becomes a section of `𝒪_X` with the same
vanishing locus.
-/

/-- The codimension of a point of an affine open subset of a scheme is the height of the
corresponding prime ideal of the ring of sections. -/
theorem IsAffineOpen.coheight_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (p : PrimeSpectrum Γ(X, U)) : coheight (hU.fromSpec p) = p.asIdeal.height := by
  rw [idealHeight_eq_coheight Γ(X, U) p]
  exact hU.fromSpec.isOpenEmbedding.coheight_eq

/-- The codimension of a point of an affine open subset of a scheme is the height of the prime
ideal of the ring of sections that corresponds to it. -/
theorem IsAffineOpen.coheight_eq_height_primeIdealOf {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) : coheight x.1 = (hU.primeIdealOf x).asIdeal.height := by
  rw [← hU.coheight_fromSpec (hU.primeIdealOf x), hU.fromSpec_primeIdealOf]

/-- **Krull's principal ideal theorem for schemes.** Let `f` be a section of `𝒪_X` over an open
`U` of a locally Noetherian scheme `X`, and let `z ∈ U` be a point where `f` vanishes such that
no other point of `U` at which `f` vanishes generalizes to `z` — that is, `z` is the generic
point of an irreducible component of the vanishing locus of `f` in `U`. Then `z` has codimension
at most one in `X`. -/
theorem coheight_le_one_of_minimal_notMem_basicOpen {X : Scheme.{u}} [IsLocallyNoetherian X]
    {U : X.Opens} (f : Γ(X, U)) {z : X} (hzU : z ∈ U) (hz : z ∉ X.basicOpen f)
    (hmin : ∀ y ∈ U, y ∉ X.basicOpen f → y ⤳ z → y = z) :
    coheight z ≤ 1 := by
  -- Pass to an affine open neighbourhood `V` of `z` contained in `U`, and restrict `f` to it.
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hzU U.2
  have hV' : IsAffineOpen V := hV
  have hVU' : V ≤ U := hVU
  obtain ⟨g, hg⟩ : ∃ g : Γ(X, V), g = X.presheaf.map (homOfLE hVU').op f := ⟨_, rfl⟩
  have hbo : X.basicOpen g = V ⊓ X.basicOpen f := hg ▸ Scheme.basicOpen_res _ _ _
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  -- The points of `V` are the primes of `Γ(X, V)`, and `X.basicOpen g` is the basic open of `g`.
  have hmem (p : PrimeSpectrum Γ(X, V)) : hV'.fromSpec p ∈ V := by
    have : hV'.fromSpec p ∈ Set.range hV'.fromSpec.base := Set.mem_range_self _
    rwa [hV'.range_fromSpec] at this
  have hbasic (p : PrimeSpectrum Γ(X, V)) : hV'.fromSpec p ∈ X.basicOpen g ↔ g ∉ p.asIdeal := by
    rw [show (hV'.fromSpec p ∈ X.basicOpen g) ↔ p ∈ hV'.fromSpec ⁻¹ᵁ X.basicOpen g from Iff.rfl,
      hV'.fromSpec_preimage_basicOpen]
    exact PrimeSpectrum.mem_basicOpen g p
  obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum Γ(X, V), p = hV'.primeIdealOf ⟨z, hzV⟩ := ⟨_, rfl⟩
  have hpz : hV'.fromSpec p = z := hp ▸ hV'.fromSpec_primeIdealOf ⟨z, hzV⟩
  -- `g` lies in the prime of `z`, since `f` vanishes at `z`.
  have hgp : g ∈ p.asIdeal := by
    by_contra hgp
    exact hz (hbo ▸ (hpz ▸ (hbasic p).mpr hgp) : z ∈ V ⊓ X.basicOpen f).2
  -- and the prime of `z` is minimal over `(g)`, because `z` is minimal in the vanishing locus.
  have hmin' : p.asIdeal ∈ (Ideal.span {g}).minimalPrimes := by
    refine ⟨⟨inferInstance, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgp)⟩, ?_⟩
    rintro q ⟨hq, hqle⟩ hqp
    have hgq : g ∈ q := hqle (Ideal.mem_span_singleton_self g)
    obtain ⟨y, hy⟩ : ∃ y : X, y = hV'.fromSpec ⟨q, hq⟩ := ⟨_, rfl⟩
    have hyV : y ∈ V := hy ▸ hmem ⟨q, hq⟩
    have hyf : y ∉ X.basicOpen f := fun h ↦
      (hbasic ⟨q, hq⟩).mp (hy ▸ (hbo ▸ ⟨hyV, h⟩ : y ∈ X.basicOpen g)) hgq
    have hyz : y ⤳ z := by
      have h₁ : (⟨q, hq⟩ : PrimeSpectrum Γ(X, V)) ⤳ p :=
        (PrimeSpectrum.le_iff_specializes _ _).mp ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hqp)
      rw [hy, ← hpz]
      exact h₁.map hV'.fromSpec.continuous
    have : (⟨q, hq⟩ : PrimeSpectrum Γ(X, V)) = p :=
      hV'.fromSpec.isOpenEmbedding.injective (by rw [← hy, hmin y (hVU hyV) hyf hyz, ← hpz])
    exact le_of_eq congr(($this).asIdeal).symm
  -- Krull's principal ideal theorem in `Γ(X, V)`, transported back to `X`.
  have hheight : p.asIdeal.height ≤ 1 :=
    have : (Ideal.span {g}).IsPrincipal := ⟨⟨g, rfl⟩⟩
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin'
  rw [← hpz, hV'.coheight_fromSpec p]
  exact hheight

/-- **Krull's principal ideal theorem for schemes**, for a global section: every irreducible
component of the vanishing locus of `f : Γ(X, ⊤)` on a locally Noetherian scheme `X` has
codimension at most one, the component being described by its generic point `z`. -/
theorem coheight_le_one_of_minimal_mem_zeroLocus {X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : Γ(X, ⊤)) {z : X} (hz : z ∈ X.zeroLocus {f})
    (hmin : ∀ y ∈ X.zeroLocus {f}, y ⤳ z → y = z) :
    coheight z ≤ 1 := by
  rw [Scheme.zeroLocus_singleton] at hz hmin
  exact coheight_le_one_of_minimal_notMem_basicOpen f trivial hz
    fun y _ hy hyz ↦ hmin y hy hyz

end AlgebraicGeometry
