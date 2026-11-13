/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Constructible
public import Mathlib.Data.Fin.Tuple.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.Mathlib.Topology.Constructible

/-!
# Complementary stratifications of a Noetherian scheme

Source: blueprint main-20261015, `sk-lem-integral-models-operations.proof.md`, paragraph (3),
Noetherian quasi-compactness and the geometry of open and closed constructibility preservation
(blueprint: lem-sfb-noetherian-complementary-stratifications).

The output uses the recorded finite locally closed stratification interface and states
constructibility separately. Equality of scheme/morphism dependent pairs records the actual
composites and the given complementary scheme, without replacing either by isomorphic data.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem append_complementary_stratum
    {T V W : Scheme.{u}} [IsNoetherian T]
    (h : V ⟶ T) (k : W ⟶ T) [IsImmersion h] [IsImmersion k]
    (hhk : Set.range h = (Set.range k)ᶜ)
    (S : FiniteLocallyClosedStratification V) :
    ∃ (R : FiniteLocallyClosedStratification T) (e : Fin (S.n + 1) ≃ Fin R.n),
      (∀ a : Fin (S.n + 1),
        (⟨R.domain (e a), R.immersion (e a)⟩ : Σ Y : Scheme.{u}, Y ⟶ T) =
          Fin.snoc (α := fun _ : Fin (S.n + 1) ↦ Σ Y : Scheme.{u}, Y ⟶ T)
            (fun b : Fin S.n ↦
              (⟨S.domain b, S.immersion b ≫ h⟩ : Σ Y : Scheme.{u}, Y ⟶ T))
            (⟨W, k⟩ : Σ Y : Scheme.{u}, Y ⟶ T) a) ∧
      (∀ a : Fin R.n, Topology.IsConstructible (R.stratum a)) := by
  let D : Fin (S.n + 1) → Σ Y : Scheme.{u}, Y ⟶ T :=
    Fin.snoc (α := fun _ : Fin (S.n + 1) ↦ Σ Y : Scheme.{u}, Y ⟶ T)
      (fun b ↦ ⟨S.domain b, S.immersion b ≫ h⟩) ⟨W, k⟩
  have hlast : D (Fin.last S.n) = ⟨W, k⟩ := Fin.snoc_last _ _
  have hcast (b : Fin S.n) : D b.castSucc = ⟨S.domain b, S.immersion b ≫ h⟩ :=
    Fin.snoc_castSucc _ _ _
  have himm : ∀ a, IsImmersion (D a).2 := by
    intro a
    refine Fin.lastCases ?_ (fun b ↦ ?_) a
    · rw [hlast]
      exact inferInstance
    · have := S.isImmersion b
      rw [hcast]
      exact inferInstance
  have hdisj : Pairwise (Function.onFun Disjoint (fun a ↦ Set.range (D a).2)) := by
    intro a
    refine Fin.lastCases ?_ (fun a ↦ ?_) a
    · intro b
      refine Fin.lastCases ?_ (fun b ↦ ?_) b
      · intro hab
        exact (hab rfl).elim
      · intro _
        change Disjoint (Set.range (D (Fin.last S.n)).2) (Set.range (D b.castSucc).2)
        rw [hlast, hcast]
        apply Set.disjoint_left.mpr
        rintro x hx ⟨z, rfl⟩
        have hz : (S.immersion b ≫ h) z ∈ Set.range h := ⟨S.immersion b z, rfl⟩
        rw [hhk] at hz
        exact hz hx
    · intro b
      refine Fin.lastCases ?_ (fun b ↦ ?_) b
      · intro _
        change Disjoint (Set.range (D a.castSucc).2) (Set.range (D (Fin.last S.n)).2)
        rw [hcast, hlast]
        apply Set.disjoint_left.mpr
        rintro x ⟨z, rfl⟩ hx
        have hz : (S.immersion a ≫ h) z ∈ Set.range h := ⟨S.immersion a z, rfl⟩
        rw [hhk] at hz
        exact hz hx
      · intro hab
        change Disjoint (Set.range (D a.castSucc).2) (Set.range (D b.castSucc).2)
        rw [hcast, hcast]
        apply Set.disjoint_left.mpr
        rintro x ⟨z, rfl⟩ ⟨w, hw⟩
        have he := h.isEmbedding.injective hw
        exact Set.disjoint_left.mp
          (S.pairwise_disjoint_stratum (fun heq ↦ hab (congrArg Fin.castSucc heq)))
          ((S.range_immersion a) ▸ Set.mem_range_self z)
          ((S.range_immersion b) ▸ ⟨w, he⟩)
  let R : FiniteLocallyClosedStratification T :=
    { n := S.n + 1
      stratum := fun a ↦ Set.range (D a).2
      domain := fun a ↦ (D a).1
      immersion := fun a ↦ (D a).2
      isImmersion := himm
      range_immersion := fun _ ↦ rfl
      isLocallyClosed_stratum := fun a ↦ by
        have := himm a
        exact (D a).2.isLocallyClosed_range
      pairwise_disjoint_stratum := hdisj
      iUnion_stratum_eq_univ := by
        apply Set.eq_univ_of_forall
        intro x
        by_cases hx : x ∈ Set.range h
        · obtain ⟨y, rfl⟩ := hx
          have hy : y ∈ ⋃ a, S.stratum a :=
            S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ y
          obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hy
          rw [← S.range_immersion a] at ha
          obtain ⟨z, rfl⟩ := ha
          refine Set.mem_iUnion.mpr ⟨a.castSucc, ?_⟩
          rw [hcast]
          exact ⟨z, rfl⟩
        · refine Set.mem_iUnion.mpr ⟨Fin.last S.n, ?_⟩
          rw [hlast]
          simpa only [hhk, Set.mem_compl_iff, not_not] using hx }
  exact ⟨R, Equiv.refl _, fun _ ↦ rfl,
    fun a ↦ (R.isLocallyClosed_stratum a).isConstructible_of_noetherianSpace⟩

/-- Complementary open and closed immersions in a Noetherian scheme preserve finite
stratifications when the complementary scheme is adjoined as one stratum.
Source: blueprint main-20261015, `sk-lem-integral-models-operations.proof.md`, paragraph (3)
(blueprint: lem-sfb-noetherian-complementary-stratifications).

Proof, following the eight reviewed DAG steps:
1. Every open subscheme of a Noetherian scheme is Noetherian, so every open of `T` is
   quasi-compact and `U` is Noetherian (lem-weil-pbc-noetherian-open-subscheme-noetherian).
2. Given an open cover of any subset, finitely many of its ambient opens cover their union,
   by step 1, hence the subset. This proves every subset compact, including the inverse
   images of affine opens under `j`, so `j` is quasi-compact (def-weil-finite-type-morphism).
3. The closed immersion `i` is locally of finite type
   (lem-weil-pbc-immersion-base-change-lft). Thus `Z` is locally Noetherian
   (pqf-lem-locnoeth-lft); its space is homeomorphic to a compact subset of `T` by step 2.
   This proves `Z` Noetherian without changing its possibly nonreduced scheme structure.
4. Locally Noetherian schemes are quasi-separated
   (lem-weil-pbc-locally-noetherian-quasi-separated). Apply this to `T`, `U`, and `Z`;
   their Noetherianity supplies quasi-compactness as well.
5. Compose each original immersion with `j` or `i`, using immersion composition
   (lem-weil-pbc-proper-fp-permanence, clause (e)); retain every source scheme.
6. The image of a locally closed subset under an open or closed embedding is locally
   closed, by the subspace topology. Every open of `T` is retrocompact by step 2, so every
   locally closed subset is constructible (def-weil-constructible-subset, Stacks 005L).
7. For a stratification of `U`, append the given `Z` and `i`. Injectivity of `j` preserves
   pairwise disjointness, and complementarity gives disjointness from `i(Z)` and coverage
   of `T` (definition-constructible-sheaves--2). Steps 5 and 6 give all other fields.
8. For a stratification of `Z`, append the given `U` and `j`, with the same argument using
   injectivity of `i`. Neither construction changes the old domains or source maps.
   Empty strata remain; when the old index set is empty only the complementary stratum
   remains. An empty complementary scheme is retained as an empty stratum.

The equivalences below only identify the output indices with the original indices plus
one last index. `Fin.snoc` lists precisely the original composite maps followed by `i`
or `j`; equality in the dependent pair includes equality of their domain schemes. -/
theorem noetherian_complementary_stratifications
    {T U Z : Scheme.{u}} [IsLocallyNoetherian T] [CompactSpace T]
    (j : U ⟶ T) (i : Z ⟶ T) [IsOpenImmersion j] [IsClosedImmersion i]
    (hji : Set.range j = (Set.range i)ᶜ) :
    IsNoetherian T ∧ IsNoetherian U ∧ IsNoetherian Z ∧
    (CompactSpace T ∧ QuasiSeparatedSpace T) ∧
    (CompactSpace U ∧ QuasiSeparatedSpace U) ∧
    (CompactSpace Z ∧ QuasiSeparatedSpace Z) ∧
    (∀ A : Set T, IsCompact A) ∧ QuasiCompact j ∧
    (∀ S : FiniteLocallyClosedStratification U,
      ∃ (R : FiniteLocallyClosedStratification T) (e : Fin (S.n + 1) ≃ Fin R.n),
        (∀ a : Fin (S.n + 1),
          (⟨R.domain (e a), R.immersion (e a)⟩ : Σ W : Scheme.{u}, W ⟶ T) =
            Fin.snoc (α := fun _ : Fin (S.n + 1) ↦ Σ W : Scheme.{u}, W ⟶ T)
              (fun b : Fin S.n ↦
                (⟨S.domain b, S.immersion b ≫ j⟩ : Σ W : Scheme.{u}, W ⟶ T))
              (⟨Z, i⟩ : Σ W : Scheme.{u}, W ⟶ T) a) ∧
        (∀ a : Fin R.n, Topology.IsConstructible (R.stratum a))) ∧
    (∀ S : FiniteLocallyClosedStratification Z,
      ∃ (R : FiniteLocallyClosedStratification T) (e : Fin (S.n + 1) ≃ Fin R.n),
        (∀ a : Fin (S.n + 1),
          (⟨R.domain (e a), R.immersion (e a)⟩ : Σ W : Scheme.{u}, W ⟶ T) =
            Fin.snoc (α := fun _ : Fin (S.n + 1) ↦ Σ W : Scheme.{u}, W ⟶ T)
              (fun b : Fin S.n ↦
                (⟨S.domain b, S.immersion b ≫ i⟩ : Σ W : Scheme.{u}, W ⟶ T))
              (⟨U, j⟩ : Σ W : Scheme.{u}, W ⟶ T) a) ∧
        (∀ a : Fin R.n, Topology.IsConstructible (R.stratum a))) := by
  have : IsNoetherian T := ⟨⟩
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace Z := i.isClosedEmbedding.isInducing.noetherianSpace
  have : IsNoetherian U := ⟨⟩
  have : IsNoetherian Z := ⟨⟩
  refine ⟨inferInstance, inferInstance, inferInstance,
    ⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance⟩, TopologicalSpace.NoetherianSpace.isCompact, inferInstance,
    append_complementary_stratum j i hji, ?_⟩
  exact append_complementary_stratum i j (by rw [hji, compl_compl])

end AlgebraicGeometry.Scheme
