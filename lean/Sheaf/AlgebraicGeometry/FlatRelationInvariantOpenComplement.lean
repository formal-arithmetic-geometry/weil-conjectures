module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Inseparable

import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Invariant open complements for flat affine relations

Source: Stacks Project, Groupoids, Tag 0APB, proof of lemma-second-observation,
abstracted to the source-target saturation axioms.
(blueprint: lem-a1-flat-relation-invariant-open-complement)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The closure of the saturation of a closed complement is invariant and avoids `K`;
its open complement is an invariant neighbourhood of `K` contained in `H`.

Source: Stacks Project, Groupoids, Tag 0APB, proof of lemma-second-observation.
(blueprint: lem-a1-flat-relation-invariant-open-complement)

Proof plan:
1. Write `Z = Hᶜ`, `T = t '' (s ⁻¹' Z)` and `B = closure T`. The common section
   gives `Z ⊆ T`. If `t r ∈ K` and `s r ∈ Z`, invariance puts `s r` in `K`,
   contradicting `K ⊆ H`. Thus `K ∩ T = ∅`; the saturation hypothesis makes `T` invariant.
2. Realize the closed subset `s ⁻¹' Z` as a closed subscheme of `R`
   (lem-weil-pbc-closed-subset-closed-subscheme). Its composite `j` with `t` has image `T`.
   Over each affine open of `V`, affineness of `t` makes its preimage affine
   (pqf-def-affine-morphism), hence quasi-compact (lem-weil-pbc-affine-scheme-qcqs).
   The closed immersion identifies the preimage under `j` with a closed subset there
   (def-weil-closed-immersion); it is quasi-compact
   (lem-weil-pbc-closed-in-quasi-compact). Thus `j` is quasi-compact
   (def-weil-finite-type-morphism).
3. Apply lem-sc-picard-closure-specialization to `j`: each point of `B` is a
   specialization of a point of `T`.
4. If `s r ∈ B`, choose `y' ∈ T` generalizing `s r`. Flatness lifts this to a
   generalization `r'` of `r` with `s r' = y'`
   (lem-weil-pbc-flat-generalizations-lift). Invariance gives `t r' ∈ T`, and continuity
   gives `t r ∈ B`. Interchange `s` and `t` for the reverse inclusion. Thus `B` is invariant.
5. A point in `K ∩ B` has a generalization in `T`; generalization stability puts that
   point in `K`, contradicting step 1. Hence `K ∩ B = ∅`.
6. The complement of `B` is open and invariant. Step 5 puts `K` in this complement;
   `Z ⊆ T ⊆ B` puts the complement inside `H`.
-/
theorem flat_relation_invariant_open_complement
    {R V : Scheme.{u}} (s t : R ⟶ V) [Flat s] [Flat t]
    [IsAffineHom s] [IsAffineHom t] (e : V ⟶ R)
    (hes : e ≫ s = 𝟙 V) (het : e ≫ t = 𝟙 V)
    (hsat : ∀ A : Set V, s ⁻¹' (t '' (s ⁻¹' A)) = t ⁻¹' (t '' (s ⁻¹' A)))
    (H : V.Opens) [CompactSpace H] (K : Set V) (hKH : K ⊆ (H : Set V))
    (hK : s ⁻¹' K = t ⁻¹' K) (hgen : StableUnderGeneralization K) :
    (H : Set V)ᶜ ⊆ t '' (s ⁻¹' (H : Set V)ᶜ) ∧
    K ∩ (t '' (s ⁻¹' (H : Set V)ᶜ)) = ∅ ∧
    (∀ y ∈ closure (t '' (s ⁻¹' (H : Set V)ᶜ)),
      ∃ y' ∈ t '' (s ⁻¹' (H : Set V)ᶜ), y ∈ closure ({y'} : Set V)) ∧
    s ⁻¹' closure (t '' (s ⁻¹' (H : Set V)ᶜ)) =
      t ⁻¹' closure (t '' (s ⁻¹' (H : Set V)ᶜ)) ∧
    K ∩ closure (t '' (s ⁻¹' (H : Set V)ᶜ)) = ∅ ∧
    IsOpen (closure (t '' (s ⁻¹' (H : Set V)ᶜ)))ᶜ ∧
    s ⁻¹' (closure (t '' (s ⁻¹' (H : Set V)ᶜ)))ᶜ =
      t ⁻¹' (closure (t '' (s ⁻¹' (H : Set V)ᶜ)))ᶜ ∧
    K ⊆ (closure (t '' (s ⁻¹' (H : Set V)ᶜ)))ᶜ ∧
    (closure (t '' (s ⁻¹' (H : Set V)ᶜ)))ᶜ ⊆ (H : Set V) := by
  classical
  let Z : Set V := (H : Set V)ᶜ
  let T : Set V := t '' (s ⁻¹' Z)
  have hZT : Z ⊆ T := by
    intro z hz
    have hs : s (e z) = z := by
      simpa using congrArg (fun f : V ⟶ V ↦ f z) hes
    have ht : t (e z) = z := by
      simpa using congrArg (fun f : V ⟶ V ↦ f z) het
    refine ⟨e z, ?_, ht⟩
    change s (e z) ∈ Z
    rwa [hs]
  have hKT : K ∩ T = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hyK, r, hrZ, rfl⟩
    have hrK : s r ∈ K := by
      have : r ∈ t ⁻¹' K := hyK
      rwa [← hK] at this
    exact hrZ (hKH hrK)
  have hT : s ⁻¹' T = t ⁻¹' T := hsat Z
  let C : TopologicalSpace.Closeds R :=
    ⟨s ⁻¹' Z, H.isOpen.isClosed_compl.preimage s.continuous⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  let i := I.subschemeι
  let j := i ≫ t
  have hi : Set.range i = s ⁻¹' Z := by
    simp [i, I, C, Scheme.IdealSheafData.range_subschemeι]
  have hj : Set.range j = T := by
    rw [show (j : I.subscheme → V) = t ∘ i from rfl, Set.range_comp, hi]
  have hcl : ∀ y ∈ closure T, ∃ y' ∈ T, y ∈ closure ({y'} : Set V) := by
    intro y hy
    obtain ⟨d, hd⟩ := exists_specializes_of_mem_closure_range j (hj.symm ▸ hy)
    exact ⟨j d, hj ▸ Set.mem_range_self d, specializes_iff_mem_closure.mp hd⟩
  have hB : s ⁻¹' closure T = t ⁻¹' closure T := by
    ext r
    constructor
    · intro hr
      obtain ⟨y, hyT, hy⟩ := hcl (s r) hr
      obtain ⟨r', hr'r, hr'y⟩ := Flat.generalizingMap s
        (specializes_iff_mem_closure.mpr hy)
      have hr'T : t r' ∈ T := by
        have : r' ∈ s ⁻¹' T := by
          change s r' ∈ T
          rwa [hr'y]
        rwa [hT] at this
      exact (hr'r.map t.continuous).mem_closed isClosed_closure (subset_closure hr'T)
    · intro hr
      obtain ⟨y, hyT, hy⟩ := hcl (t r) hr
      obtain ⟨r', hr'r, hr'y⟩ := Flat.generalizingMap t
        (specializes_iff_mem_closure.mpr hy)
      have hr'T : s r' ∈ T := by
        have : r' ∈ t ⁻¹' T := by
          change t r' ∈ T
          rwa [hr'y]
        rwa [← hT] at this
      exact (hr'r.map s.continuous).mem_closed isClosed_closure (subset_closure hr'T)
  have hKB : K ∩ closure T = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hyK, hyB⟩
    obtain ⟨y', hy'T, hy'⟩ := hcl y hyB
    have hy'K := hgen (specializes_iff_mem_closure.mpr hy') hyK
    exact Set.notMem_empty y' (hKT ▸ ⟨hy'K, hy'T⟩)
  refine ⟨hZT, hKT, hcl, hB, hKB, isClosed_closure.isOpen_compl, ?_, ?_, ?_⟩
  · change s ⁻¹' (closure T)ᶜ = t ⁻¹' (closure T)ᶜ
    simpa only [Set.preimage_compl] using congrArg (fun A : Set R ↦ Aᶜ) hB
  · intro y hyK hyB
    exact Set.notMem_empty y (hKB ▸ ⟨hyK, hyB⟩)
  · intro y hy
    by_contra hyH
    exact hy (subset_closure (hZT hyH))

end AlgebraicGeometry
