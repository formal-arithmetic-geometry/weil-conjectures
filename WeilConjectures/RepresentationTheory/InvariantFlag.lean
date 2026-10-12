/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Categorical filtrations from invariant flags

Let `M` be a finite-dimensional representation of a group `P` over `ZMod ℓ` and let
`0 = F 0 ⊆ F 1 ⊆ ⋯ ⊆ F n = M` be a full flag of `P`-stable subspaces such that `P` acts trivially
on each `F (i + 1) / F i`. We realise this flag inside the abelian category `Rep (ZMod ℓ) P`: a
sequence of monomorphisms `W 0 ⟶ W 1 ⟶ ⋯ ⟶ W n` with `W 0 = 0`, `W n ≅ M` and all cokernels
isomorphic to the trivial representation on `ULift (ZMod ℓ)`.

## Main results

* `Rep.ofStableSubmodule`: the subrepresentation on a `G`-stable submodule, as an object of `Rep`.
* `Rep.cokernelIsoOfRangeEqKer`: the cokernel of `f` is the target of a surjection `p` with
  `ker p = range f`.
* `Rep.exists_categorical_filtration_of_invariant_flag`: the main statement.
-/

@[expose] public section

universe u v w

namespace Rep

open CategoryTheory Limits Module

section CommRing

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

/-- The object of `Rep k G` given by a `G`-stable `k`-submodule `S` of `A`, with the restricted
action. -/
abbrev ofStableSubmodule (A : Rep.{w} k G) (S : Submodule k A)
    (hS : ∀ (g : G), ∀ x ∈ S, A.ρ g x ∈ S) : Rep.{w} k G :=
  Rep.of (Subrepresentation.toRepresentation (ρ := A.ρ) ⟨S, fun g _ hx ↦ hS g _ hx⟩)

/-- The inclusion `S ⟶ T` of `G`-stable submodules `S ≤ T`, as a morphism in `Rep k G`. -/
def ofStableSubmoduleInclusion (A : Rep.{w} k G) {S T : Submodule k A}
    (hS : ∀ (g : G), ∀ x ∈ S, A.ρ g x ∈ S) (hT : ∀ (g : G), ∀ x ∈ T, A.ρ g x ∈ T)
    (h : S ≤ T) : A.ofStableSubmodule S hS ⟶ A.ofStableSubmodule T hT :=
  Rep.ofHom ((Submodule.inclusion h).intertwiningMap_of_isIntertwiningMap fun _ _ ↦ rfl)

/-- The inclusion of a `G`-stable submodule `S` into `A`, as a morphism in `Rep k G`. -/
def ofStableSubmoduleSubtype (A : Rep.{w} k G) (S : Submodule k A)
    (hS : ∀ (g : G), ∀ x ∈ S, A.ρ g x ∈ S) : A.ofStableSubmodule S hS ⟶ A :=
  Rep.ofHom (S.subtype.intertwiningMap_of_isIntertwiningMap fun _ _ ↦ rfl)

/-- If `p : Y ⟶ Z` in `Rep k G` is surjective with kernel the range of `f : X ⟶ Y`, then
`cokernel f ≅ Z`. -/
noncomputable def cokernelIsoOfRangeEqKer {X Y Z : Rep.{w} k G} (f : X ⟶ Y) (p : Y ⟶ Z)
    (hp : Function.Surjective p.hom)
    (hfp : LinearMap.range f.hom.toLinearMap = LinearMap.ker p.hom.toLinearMap) :
    cokernel f ≅ Z :=
  have hzero : f ≫ p = 0 := by
    ext x
    have hx : f.hom.toLinearMap x ∈ LinearMap.ker p.hom.toLinearMap :=
      hfp ▸ LinearMap.mem_range_self _ x
    simpa using hx
  have hS : (ShortComplex.mk f p hzero).Exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact hfp
  have : Epi (ShortComplex.mk f p hzero).g := (epi_iff_surjective p).2 hp
  (cokernelIsCokernel f).coconePointUniqueUpToIso hS.gIsCokernel

end CommRing

section Field

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

/-- Let `S ≤ T` be `G`-stable subspaces of `A : Rep k G` with `T` finite-dimensional,
`dim T = dim S + 1`, and `G` acting trivially on `T / S`. Then the cokernel of the inclusion
`S ⟶ T` in `Rep k G` is isomorphic to the trivial representation on any one-dimensional
`k`-vector space `V`. -/
theorem nonempty_cokernel_ofStableSubmoduleInclusion_iso_trivial (A : Rep.{w} k G)
    {S T : Submodule k A} (hS : ∀ (g : G), ∀ x ∈ S, A.ρ g x ∈ S)
    (hT : ∀ (g : G), ∀ x ∈ T, A.ρ g x ∈ T) (hST : S ≤ T) [FiniteDimensional k T]
    (hrank : finrank k T = finrank k S + 1) (htriv : ∀ (g : G), ∀ x ∈ T, A.ρ g x - x ∈ S)
    (V : Type w) [AddCommGroup V] [Module k V] (hV : finrank k V = 1) :
    Nonempty (cokernel (A.ofStableSubmoduleInclusion hS hT hST) ≅ Rep.trivial k G V) := by
  set K := S.comap T.subtype
  have hK : finrank k K = finrank k S := (Submodule.comapSubtypeEquivOfLe hST).finrank_eq
  have hQ : finrank k (T ⧸ K) = finrank k V := by
    have := Submodule.finrank_quotient_add_finrank K
    omega
  have : FiniteDimensional k V := Module.finite_of_finrank_eq_succ hV
  let e : (T ⧸ K) ≃ₗ[k] V := LinearEquiv.ofFinrankEq _ _ hQ
  let π : T →ₗ[k] V := e.toLinearMap ∘ₗ K.mkQ
  have hπ (g : G) (v : T) : π ((A.ofStableSubmodule T hT).ρ g v) = π v := by
    have hv : (A.ofStableSubmodule T hT).ρ g v - v ∈ K := htriv g v v.2
    rw [← sub_eq_zero, ← map_sub, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero K).2 hv, map_zero]
  refine ⟨cokernelIsoOfRangeEqKer _ (Rep.ofHom (π.intertwiningMap_of_isIntertwiningMap hπ))
    (e.surjective.comp K.mkQ_surjective) ?_⟩
  exact (Submodule.range_inclusion _ _ _).trans (by rw [LinearEquiv.ker_comp, Submodule.ker_mkQ])

end Field

/-- **Categorical realization of an invariant rank-one flag.** Let `ℓ` be a prime, `P` a group
and `M` a finite-dimensional representation of `P` over `ZMod ℓ`, of dimension `n`. Let
`F : ℕ → Submodule (ZMod ℓ) M` with `F 0 = 0`, `F n = M`, `F i` stable under `P` for `i ≤ n`, and
for `i < n`: `F i ≤ F (i + 1)`, `dim F (i + 1) = i + 1` and `g • x - x ∈ F i` for `g : P`,
`x ∈ F (i + 1)`. Then there are representations `W i` and morphisms `ι i : W i ⟶ W (i + 1)` in
`Rep (ZMod ℓ) P` with `W 0` zero, `W n ≅ M`, and for `i < n`, `ι i` a monomorphism whose
cokernel is isomorphic to the trivial representation on `ULift (ZMod ℓ)`.
(blueprint: `lem-weil-pbc-invariant-flag-categorical-filtration`) -/
theorem exists_categorical_filtration_of_invariant_flag {ℓ : ℕ} [Fact ℓ.Prime] {P : Type v}
    [Group P] (M : Rep.{w} (ZMod ℓ) P) [FiniteDimensional (ZMod ℓ) M]
    (F : ℕ → Submodule (ZMod ℓ) M) (hF0 : F 0 = ⊥) (hFn : F (finrank (ZMod ℓ) M) = ⊤)
    (hstable : ∀ i ≤ finrank (ZMod ℓ) M, ∀ (g : P), ∀ x ∈ F i, M.ρ g x ∈ F i)
    (hle : ∀ i < finrank (ZMod ℓ) M, F i ≤ F (i + 1))
    (hdim : ∀ i < finrank (ZMod ℓ) M, finrank (ZMod ℓ) (F (i + 1)) = i + 1)
    (hquot : ∀ i < finrank (ZMod ℓ) M, ∀ (g : P), ∀ x ∈ F (i + 1), M.ρ g x - x ∈ F i) :
    ∃ (W : ℕ → Rep.{w} (ZMod ℓ) P) (ι : ∀ i, W i ⟶ W (i + 1)), IsZero (W 0) ∧
      Nonempty (W (finrank (ZMod ℓ) M) ≅ M) ∧ ∀ i < finrank (ZMod ℓ) M, Mono (ι i) ∧
        Nonempty (cokernel (ι i) ≅ Rep.trivial (ZMod ℓ) P (ULift.{w} (ZMod ℓ))) := by
  set n := finrank (ZMod ℓ) M
  have hB (i : ℕ) : ∀ (g : P), ∀ x ∈ F (min i n), M.ρ g x ∈ F (min i n) :=
    hstable _ (min_le_right _ _)
  have hBle (i : ℕ) : F (min i n) ≤ F (min (i + 1) n) := by
    rcases lt_or_ge i n with h | h
    · rw [min_eq_left h.le, min_eq_left (by omega : i + 1 ≤ n)]
      exact hle i h
    · rw [min_eq_right h, min_eq_right (by omega : n ≤ i + 1)]
  have hrank (i : ℕ) (hi : i ≤ n) : finrank (ZMod ℓ) (F i) = i := by
    rcases i with _ | i
    · rw [hF0, finrank_bot]
    · exact hdim i (by omega)
  refine ⟨fun i ↦ M.ofStableSubmodule (F (min i n)) (hB i),
    fun i ↦ M.ofStableSubmoduleInclusion (hB i) (hB (i + 1)) (hBle i), ?_, ?_,
    fun i hi ↦ ⟨?_, ?_⟩⟩
  · rw [Rep.isZero_iff]
    refine ⟨fun a b ↦ Subtype.ext ?_⟩
    have ha := a.2
    have hb := b.2
    simp only [Nat.zero_min, hF0, Submodule.mem_bot] at ha hb
    rw [ha, hb]
  · refine ⟨Rep.mkIso (Representation.Equiv.ofBijective
      (M.ofStableSubmoduleSubtype (F (min n n)) (hB n)).hom ⟨Subtype.val_injective, ?_⟩)⟩
    intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [min_self, hFn]
    exact Submodule.mem_top
  · rw [Rep.mono_iff_injective]
    exact Submodule.inclusion_injective _
  · apply nonempty_cokernel_ofStableSubmoduleInclusion_iso_trivial
    · rw [min_eq_left hi.le, min_eq_left (by omega : i + 1 ≤ n), hrank i hi.le,
        hrank (i + 1) (by omega)]
    · rw [min_eq_left hi.le, min_eq_left (by omega : i + 1 ≤ n)]
      exact hquot i hi
    · rw [finrank_ulift, finrank_self]

end Rep
