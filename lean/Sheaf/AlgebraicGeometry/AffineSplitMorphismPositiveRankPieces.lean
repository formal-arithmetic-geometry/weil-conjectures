/-
Copyright (c) 2026 Weil SHEAF project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project contributors
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Positive affine rank pieces of a finite locally free morphism with a section

Source: Stacks Project, Tags 03BI and 03BJ, positive-degree and finite-rank reduction;
Tags 04MH, 00EE and 01I3 for rank strata and affine clopen pieces
(blueprint: lem-a1-affine-split-morphism-positive-rank-pieces).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite locally free morphism between spectra admitting a section has finitely many
nonempty positive-degree strata, all affine with affine inverse images and cut out by
idempotents. Here `f.fiberDegree y` is the dimension of global functions of the
scheme-theoretic fibre over `κ(y)`, using its canonical residue-field algebra structure.

Source: Stacks Project, Tags 03BI and 03BJ, with Tags 04MH, 00EE and 01I3
(blueprint: lem-a1-affine-split-morphism-positive-rank-pieces).

Proof plan:
1. Apply `lem-weil-pbc-finite-locally-free-degree-locally-constant`, namely
   `finiteLocallyFree_fiberDimension_isLocallyConstant`, to obtain the clopen rank strata
   and finite locally free degree-r restrictions. Different levels are disjoint.
2. Base change the section to `Spec κ(y)` using `def-pc-fibre-product`. On global functions
   it gives a retraction of the structural map from `κ(y)` (identified with the global
   functions of its spectrum by `def-weil-affine-spectrum`). Hence that map is injective,
   the fibre algebra has nonzero unit, and its finite dimension is at least one.
   Thus the degree-zero stratum is empty.
3. Apply `lem-weil-pbc-spec-clopen-idempotent` to each stratum and its continuous preimage
   in the source to obtain the two idempotents. Empty pieces allow the zero idempotent.
4. Use `lem-weil-pbc-principal-localization-open-immersion` and
   `def-weil-open-immersion` to identify each piece with the spectrum of the corresponding
   principal localization. Both open subschemes are affine, including empty pieces.
5. Use `lem-weil-pbc-affine-scheme-qcqs`: quasi-compactness gives a finite subcover by
   rank pieces, and disjointness forces every nonempty piece to occur in it. Discarding
   empty pieces gives the coproduct indexed by the finite positive-rank set. If the
   target is empty, all pieces and therefore this index set are empty.
-/
theorem affine_split_morphism_positive_rank_pieces
    (A B : CommRingCat.{u}) (f : Spec B ⟶ Spec A) [f.IsFiniteLocallyFree]
    (a : Spec A ⟶ Spec B) (ha : a ≫ f = 𝟙 (Spec A)) :
    (∀ y : Spec A, 1 ≤ f.fiberDegree y) ∧
      ∃ U : ℕ → (Spec A).Opens,
        (∀ (r : ℕ) (y : Spec A), y ∈ U r ↔ f.fiberDegree y = r) ∧
        (∀ r : ℕ, IsClopen (U r : Set (Spec A))) ∧
        Pairwise (fun r s : ℕ ↦ Disjoint (U r) (U s)) ∧
        iSup U = ⊤ ∧ U 0 = ⊥ ∧
        (∀ r : ℕ,
          IsAffineOpen (U r) ∧ IsAffineOpen (f ⁻¹ᵁ U r) ∧
          (f ∣_ U r).IsFiniteLocallyFreeOfDegree r ∧
          ∃ (b : A) (b' : B),
            b ^ 2 = b ∧ b' ^ 2 = b' ∧
            U r = PrimeSpectrum.basicOpen b ∧
            f ⁻¹ᵁ U r = PrimeSpectrum.basicOpen b') ∧
        ∃ I : Set ℕ,
          I = {r : ℕ | 1 ≤ r ∧ (U r : Set (Spec A)).Nonempty} ∧
          I.Finite ∧
          Nonempty (IsColimit (Cofan.mk (Spec A) (fun r : I ↦ (U r.val).ι))) ∧
          (IsEmpty (Spec A) → I = ∅) := by
  classical
  obtain ⟨hfinite, hlc, hcl, U, hU, hdegree⟩ :=
    finiteLocallyFree_fiberDimension_isLocallyConstant f
  change IsLocallyConstant f.fiberDegree at hlc
  change ∀ (r : ℕ) (y : Spec A), y ∈ U r ↔ f.fiberDegree y = r at hU
  have hpos (y : Spec A) : 1 ≤ f.fiberDegree y := by
    have hay : f (a y) = y := by
      simpa using
        congrArg (fun g : Spec A ⟶ Spec A ↦ g y) ha
    have : Nonempty (f.fiber y) := ⟨(f.fiberHomeo y).symm ⟨a y, hay⟩⟩
    have : Nonempty (⊤ : (f.fiber y).Opens) := ⟨⟨Classical.arbitrary _, trivial⟩⟩
    have : Module.Finite ((Spec A).residueField y) Γ(f.fiber y, ⊤) := hfinite y
    exact Module.finrank_pos
  have hclU (r : ℕ) : IsClopen (U r : Set (Spec A)) := by
    convert hcl r using 1
    ext y
    exact hU r y
  have hdisj : Pairwise (fun r s : ℕ ↦ Disjoint (U r) (U s)) := by
    intro r s hrs
    rw [← TopologicalSpace.Opens.coe_disjoint]
    exact Set.disjoint_left.mpr fun y hyr hys ↦
      hrs (((hU r y).mp hyr).symm.trans ((hU s y).mp hys))
  have hcov : iSup U = ⊤ := by
    apply top_unique
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨f.fiberDegree y, (hU _ y).mpr rfl⟩
  have hzero : U 0 = ⊥ := by
    apply bot_unique
    intro y hy
    have := hpos y
    rw [(hU 0 y).mp hy] at this
    exact (Nat.not_succ_le_zero 0 this).elim
  refine ⟨hpos, U, hU, hclU, hdisj, hcov, hzero, ?_, ?_⟩
  · intro r
    obtain ⟨b, hb, hUb⟩ :=
      PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen (hclU r)
    obtain ⟨b', hb', hUb'⟩ :=
      PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
        ((hclU r).preimage f.continuous)
    have hUb : U r = PrimeSpectrum.basicOpen b := SetLike.coe_injective hUb
    have hUb' : f ⁻¹ᵁ U r = PrimeSpectrum.basicOpen b' := SetLike.coe_injective hUb'
    refine ⟨?_, ?_, hdegree r, b, b', ?_, ?_, hUb, hUb'⟩
    · rw [hUb]
      exact IsAffineOpen.Spec_basicOpen b
    · rw [hUb']
      exact IsAffineOpen.Spec_basicOpen b'
    · simpa only [pow_two] using hb.eq
    · simpa only [pow_two] using hb'.eq
  · let I : Set ℕ := {r | 1 ≤ r ∧ (U r : Set (Spec A)).Nonempty}
    have hIfin : I.Finite := by
      apply hlc.range_finite.subset
      rintro r ⟨_, y, hy⟩
      exact ⟨y, (hU r y).mp hy⟩
    have hcovI : (⨆ r : I, U r.val) = ⊤ := by
      apply top_unique
      intro y _
      exact TopologicalSpace.Opens.mem_iSup.mpr
        ⟨⟨f.fiberDegree y, hpos y, y, (hU _ y).mpr rfl⟩, (hU _ y).mpr rfl⟩
    refine ⟨I, rfl, hIfin, ?_, ?_⟩
    · apply nonempty_isColimit_cofanMk_of
      · simpa only [Scheme.Opens.opensRange_ι] using hcovI
      · intro r s hrs
        simpa only [Scheme.Opens.opensRange_ι] using
          hdisj (fun h ↦ hrs (Subtype.ext h))
    · intro hempty
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro r ⟨_, y, _⟩
      exact hempty.false y

end AlgebraicGeometry
