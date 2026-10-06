/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Lemmas
public import WeilConjectures.Mathlib.Algebra.Lie.CartanCriterion
public import WeilConjectures.Mathlib.Algebra.Lie.LieTheorem
public import WeilConjectures.Mathlib.Algebra.Lie.Semisimple.Defs

/-!
# Lie algebras with a faithful semisimple representation

A finite-dimensional Lie algebra over a field of characteristic zero which admits a faithful
semisimple finite-dimensional representation is *reductive*: its radical is central, and the
algebra is the sum of its centre and its derived subalgebra.

Mathlib does not (yet) have a `LieModule.IsSemisimple` class, so "`M` is a semisimple
representation of `L`" is spelled here as `ComplementedLattice (LieSubmodule k L M)`, i.e. the
lattice of Lie submodules of `M` is complemented; `LieModule.IsSemisimple` below is an `abbrev`
for that. This mirrors `IsSemisimpleModule`, which is by definition
`ComplementedLattice (Submodule R M)`.

The two halves are stated separately, and each under the hypotheses it needs. Centrality of the
radical matches Mathlib's irreducible case
`LieAlgebra.hasCentralRadical_and_of_isIrreducible_of_isFaithful`, including its
`[LieModule.IsTriangularizable k L M]` hypothesis; like that lemma it cannot be an instance,
because the representation `M` does not appear in the conclusion. The reductive decomposition
`L = Z(L) + [L, L]` needs no module at all: it holds for every finite-dimensional
characteristic-zero Lie algebra with central radical.

## Main declarations

* `LieModule.IsSemisimple`: `M` is a semisimple representation of `L`.
* `LieModule.toEnd_lie_eq_zero_of_mem_radical`: on an irreducible module, brackets `⁅x, y⁆` with
  `y` in the radical act as zero.
* `LieAlgebra.hasTrivialRadical_quotient_center`: if the radical of `L` is central, then
  `L ⧸ Z(L)` has trivial radical.
* `LieAlgebra.hasCentralRadical_of_isFaithful`: a finite-dimensional Lie algebra with a faithful
  semisimple finite-dimensional representation has central radical.
* `LieAlgebra.center_sup_derivedSeries_eq_top`: a finite-dimensional characteristic-zero Lie
  algebra with central radical is the sum of its centre and its derived subalgebra.

## Blueprint

`LieAlgebra.hasCentralRadical_of_isFaithful` and `LieAlgebra.center_sup_derivedSeries_eq_top`
implement `sk-p-lie`. The first also implements `lem-ag-faithful-semisimple-lie-central-radical`;
`LieAlgebra.hasTrivialRadical_quotient_center` together with the second implements
`lem-ag-central-radical-quotient`.
-/

@[expose] public section

open LieModule

namespace LieModule

/-- A Lie module `M` over `L` is *semisimple* when its lattice of Lie submodules is
complemented, i.e. every Lie submodule has a complement. -/
abbrev IsSemisimple (k L M : Type*) [CommRing k] [LieRing L] [LieAlgebra k L] [AddCommGroup M]
    [Module k M] [LieRingModule L M] [LieModule k L M] : Prop :=
  ComplementedLattice (LieSubmodule k L M)

variable (k L M : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L] [Module.Finite k L]
  [AddCommGroup M] [Module k M] [LieRingModule L M] [LieModule k L M] [Module.Finite k M]

/-- On an irreducible finite-dimensional module `M` over a field of characteristic zero on which
`L` acts triangularizably, the radical of `L` acts by scalars, so every bracket `⁅x, y⁆` with
`y ∈ radical k L` acts as zero. The module need not be faithful.
(blueprint: part of `lem-ag-faithful-semisimple-lie-central-radical`) -/
lemma toEnd_lie_eq_zero_of_mem_radical [IsIrreducible k L M] [IsTriangularizable k L M] (x : L)
    {y : L} (hy : y ∈ LieAlgebra.radical k L) :
    toEnd k L M ⁅x, y⁆ = 0 := by
  have _i := nontrivial_of_isIrreducible k L M
  obtain ⟨χ, v, hv0, hv, -⟩ :=
    exists_ne_zero_forall_lie_eq_smul_of_isSolvable k (LieAlgebra.radical k L) M
  let N : LieSubmodule k L M := weightSpaceOfIsLieTower k M χ
  have hvN : v ∈ N := by
    simpa [N, weightSpaceOfIsLieTower, mem_weightSpace] using hv
  have : Nontrivial N := nontrivial_of_ne ⟨v, hvN⟩ 0 fun h ↦ hv0 (congrArg Subtype.val h)
  have hN : N = ⊤ := N.eq_top_of_isIrreducible k L M
  have hχ : toEnd k L M y = χ ⟨y, hy⟩ • LinearMap.id := by
    ext m
    have hm : m ∈ N := hN ▸ LieSubmodule.mem_top m
    have hm : ∀ (z : L) (hz : z ∈ LieAlgebra.radical k L),
        ⁅z, m⁆ = χ ⟨z, hz⟩ • m := by
      simpa [N, weightSpaceOfIsLieTower, mem_weightSpace] using hm
    simpa using hm y hy
  simp [LieHom.map_lie, hχ, lie_smul, (toEnd k L M x).commute_id_right.lie_eq]

end LieModule

namespace LieAlgebra

/-- A finite-dimensional Lie algebra over a field of characteristic zero admitting a faithful
semisimple finite-dimensional representation `M` has central radical: on each irreducible
summand of `M` the bracket `⁅L, rad L⁆` acts as zero, so it vanishes by faithfulness.
(blueprint: `sk-p-lie`, `lem-ag-faithful-semisimple-lie-central-radical`) -/
theorem hasCentralRadical_of_isFaithful (k L M : Type*) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [Module.Finite k L]
    [AddCommGroup M] [Module k M] [LieRingModule L M] [LieModule k L M] [Module.Finite k M]
    [IsFaithful k L M] [IsTriangularizable k L M] [LieModule.IsSemisimple k L M] :
    HasCentralRadical k L := by
  refine hasCentralRadical_of_radical_le k L fun y hy ↦ (mem_maxTrivSubmodule k L L y).mpr ?_
  intro x
  apply IsFaithful.injective_toEnd (R := k) (L := L) (M := M)
  rw [map_zero]
  ext m
  have hm : m ∈ (sSup {N : LieSubmodule k L M | IsAtom N}).toSubmodule := by
    rw [sSup_atoms_eq_top]
    exact Submodule.mem_top
  suffices (sSup {N : LieSubmodule k L M | IsAtom N}).toSubmodule ≤
      LinearMap.ker (toEnd k L M ⁅x, y⁆) from this hm
  rw [LieSubmodule.sSup_toSubmodule]
  refine sSup_le ?_
  rintro _ ⟨N, hN, rfl⟩ n hn
  have := LieSubmodule.isIrreducible_of_isAtom hN
  have h := LinearMap.congr_fun (toEnd_lie_eq_zero_of_mem_radical k L N x hy) ⟨n, hn⟩
  exact congrArg Subtype.val h

/-- The quotient map `L → L ⧸ Z(L)` as a morphism of Lie algebras. -/
private def mkCenter (k L : Type*) [CommRing k] [LieRing L] [LieAlgebra k L] :
    L →ₗ⁅k⁆ L ⧸ center k L :=
  { (LieSubmodule.Quotient.mk' (center k L) : L →ₗ[k] L ⧸ center k L) with
    map_lie' := fun {_ _} ↦ rfl }

private lemma mkCenter_surjective (k L : Type*) [CommRing k] [LieRing L] [LieAlgebra k L] :
    Function.Surjective (mkCenter k L) :=
  LieSubmodule.Quotient.surjective_mk' _

private lemma mkCenter_eq_zero_iff {k L : Type*} [CommRing k] [LieRing L] [LieAlgebra k L]
    {x : L} : mkCenter k L x = 0 ↔ x ∈ center k L :=
  LieSubmodule.Quotient.mk_eq_zero (center k L)

/-- If the radical of a finite-dimensional Lie algebra `L` over a field is central, then the
quotient `L ⧸ Z(L)` has trivial radical: the inverse image of an abelian ideal of the quotient is
solvable, hence contained in `rad L = Z(L)`.
(blueprint: part of `lem-ag-central-radical-quotient`) -/
theorem hasTrivialRadical_quotient_center (k L : Type*) [Field k] [LieRing L] [LieAlgebra k L]
    [Module.Finite k L] [HasCentralRadical k L] :
    HasTrivialRadical k (L ⧸ center k L) := by
  set π := mkCenter k L
  refine (hasTrivialRadical_iff_no_abelian_ideals k _).mpr fun I hI ↦ ?_
  let J : LieIdeal k L := I.comap π
  have hJ : ⁅J, J⁆ ≤ center k L := by
    rw [LieSubmodule.lie_le_iff]
    intro x hx y hy
    rw [← mkCenter_eq_zero_iff, LieHom.map_lie]
    have h := trivial_lie_zero I I ⟨π x, hx⟩ ⟨π y, hy⟩
    exact congrArg Subtype.val h
  have hZ : ⁅center k L, center k L⁆ = ⊥ := by
    rw [LieSubmodule.lie_eq_bot_iff]
    intro x hx y _
    rw [← lie_skew, (mem_maxTrivSubmodule k L L x).mp hx y, neg_zero]
  have : IsSolvable J := by
    refine IsSolvable.mk (R := k) (k := 2) ((LieIdeal.derivedSeries_eq_bot_iff J 2).mpr ?_)
    rw [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
      eq_bot_iff, ← hZ]
    exact LieSubmodule.mono_lie hJ hJ
  have hJZ : J ≤ center k L := by
    rw [← HasCentralRadical.radical_eq_center]
    exact (LieIdeal.solvable_iff_le_radical k L J).mp this
  refine (LieSubmodule.eq_bot_iff I).mpr fun a ha ↦ ?_
  obtain ⟨x, rfl⟩ := mkCenter_surjective k L a
  exact mkCenter_eq_zero_iff.mpr (hJZ ha)

/-- A finite-dimensional Lie algebra over a field of characteristic zero whose radical is central
is *reductive*: it is the sum of its centre `Z(L)` and its derived subalgebra `[L, L]`.
The quotient `L ⧸ Z(L)` has trivial radical, so its Killing form is non-degenerate and it is
perfect; lifting brackets gives the decomposition.
(blueprint: `sk-p-lie`, `lem-ag-central-radical-quotient`) -/
theorem center_sup_derivedSeries_eq_top (k L : Type*) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [Module.Finite k L] [HasCentralRadical k L] :
    center k L ⊔ derivedSeries k L 1 = ⊤ := by
  set Q := L ⧸ center k L
  have := hasTrivialRadical_quotient_center k L
  -- The quotient `Q` is perfect: the Killing complement of `⁅Q, Q⁆` is central, hence zero.
  have hQ : derivedSeries k Q 1 = ⊤ := by
    set I := derivedSeries k Q 1
    have hc := I.isCompl_killingCompl
    have hJ : I.killingCompl ≤ center k Q := fun z hz ↦ by
      refine (mem_maxTrivSubmodule k Q Q z).mpr fun x ↦ ?_
      have hI : ⁅x, z⁆ ∈ I := by
        have hI : I = ⁅(⊤ : LieIdeal k Q), ⊤⁆ := by
          simp only [I, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero]
        rw [hI]
        exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top z)
      have h : ⁅x, z⁆ ∈ I ⊓ I.killingCompl := ⟨hI, lie_mem_right k Q _ x z hz⟩
      rwa [hc.inf_eq_bot, LieSubmodule.mem_bot] at h
    have hZ : center k Q = ⊥ := by
      rw [eq_bot_iff, ← HasTrivialRadical.radical_eq_bot (R := k) (L := Q)]
      exact center_le_radical k Q
    have hJ : I.killingCompl = ⊥ := le_bot_iff.mp (hJ.trans hZ.le)
    have := hc.sup_eq_top
    rwa [hJ, sup_bot_eq] at this
  rw [← LieIdeal.derivedSeries_map_eq 1 (mkCenter_surjective k L)] at hQ
  refine eq_top_iff.mpr fun x _ ↦ (LieSubmodule.mem_sup _ _ x).mpr ?_
  obtain ⟨⟨y, hy⟩, hxy⟩ :=
    LieIdeal.mem_map_of_surjective (mkCenter_surjective k L) (hQ ▸ LieSubmodule.mem_top _ :
      mkCenter k L x ∈ (derivedSeries k L 1).map (mkCenter k L))
  refine ⟨x - y, mkCenter_eq_zero_iff.mp ?_, y, hy, sub_add_cancel x y⟩
  rw [map_sub, hxy, sub_self]

end LieAlgebra
