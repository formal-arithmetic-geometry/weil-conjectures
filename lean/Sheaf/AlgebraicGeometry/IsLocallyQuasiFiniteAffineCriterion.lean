/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphismComparison
import WeilConjectures.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated

/-!
# Affine criterion and Zariski locality for local quasi-finiteness

Source: Stacks Project, Morphisms of Schemes, Tag 01TK, conditions (1), (2), (3)
(blueprint: lem-a1-scheme-lqf-affine-criterion).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- The Stacks local quasi-finiteness predicate is equivalent both to finite type and
quasi-finiteness at every prime on every affine pair, and to local quasi-finiteness on
an open covering of the target and open coverings of its inverse images.
Source: Stacks Project, Morphisms of Schemes, Tag 01TK, conditions (1), (2), (3)
(blueprint: lem-a1-scheme-lqf-affine-criterion).

Proof:
1. Assume local quasi-finiteness. By `lem-weil-pbc-lqf-locally-finite-type` and
   `lem-weil-pbc-lft-affine-pairs`, every affine-pair section map is of finite type.
   For each prime of the source coordinate ring, take its corresponding point.
   `pqf-def-quasifinite` and `lem-weil-pbc-quasi-finite-at-point-isolated` show that its
   fibre point is isolated. Apply
   `lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs` to the given affine pair
   to obtain quasi-finiteness at that prime. This proves (1) implies (2).
2. Given (2), choose an affine target neighbourhood of the image of each source point
   and an affine source neighbourhood inside its inverse image, using
   `lem-weil-pbc-affine-opens-basis`. Apply (2) at the prime corresponding to the point.
   These witnesses give `IsQuasiFiniteAtPoint` by `pqf-def-quasifinite`; hence (1).
3. Given (1), use singleton index types and the whole source and target as the opens.
   The union identities hold, and `lem-weil-pbc-lqf-restriction-to-opens` proves local
   quasi-finiteness of the canonical restriction.
4. Given (3), any source point lies in a covering piece over a target covering open.
   The existing `isLocallyQuasiFinite_iff` comparison gives Mathlib local quasi-finiteness
   and local finite type for this restriction. Apply Mathlib's pointwise source-and-target
   locality criterion `IsZariskiLocalAtSource.iff_exists_resLE` to each property, and use
   the comparison again to conclude (1).

No finiteness, separation, or Noetherian hypotheses are imposed. The finite-type
witness is passed explicitly to the ring predicate, using the algebra of `appLE`.
The covering indices may be empty; containment witnesses specify the canonical `resLE`.
-/
theorem isLocallyQuasiFinite_affine_criterion {X S : Scheme.{u}} (f : X ⟶ S) :
    (f.IsLocallyQuasiFinite ↔
      ∀ (A : X.Opens) (B : S.Opens), IsAffineOpen A → IsAffineOpen B →
        ∀ e : A ≤ f ⁻¹ᵁ B,
          ∃ hft : (f.appLE B A e).hom.FiniteType,
            ∀ q : PrimeSpectrum Γ(X, A),
              @Algebra.IsQuasiFiniteAtPrime Γ(S, B) Γ(X, A) _ _
                (f.appLE B A e).hom.toAlgebra hft q) ∧
    (f.IsLocallyQuasiFinite ↔
      ∃ (J : Type u) (B : J → S.Opens) (I : J → Type u)
        (A : ∀ j : J, I j → X.Opens) (e : ∀ (j : J) (i : I j), A j i ≤ f ⁻¹ᵁ B j),
        (⨆ j : J, B j) = ⊤ ∧
        (∀ j : J, (⨆ i : I j, A j i) = f ⁻¹ᵁ B j) ∧
        ∀ (j : J) (i : I j), (f.resLE (B j) (A j i) (e j i)).IsLocallyQuasiFinite) := by
  constructor
  · constructor
    · intro hf A B hA hB e
      have : LocallyOfFiniteType f := locallyOfFiniteType_of_isLocallyQuasiFinite f hf
      refine ⟨f.finiteType_appLE hB hA e, fun q ↦ ?_⟩
      let x : A := hA.isoSpec.inv q
      have hxq : hA.primeIdealOf x = q := by
        change hA.isoSpec.hom (hA.isoSpec.inv q) = q
        rw [← Scheme.Hom.comp_apply, hA.isoSpec.inv_hom_id]
        rfl
      obtain ⟨hft, hq⟩ := f.isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber x.1
        (quasiFiniteAtPoint_isolated_in_fiber f x.1 (hf x.1)).1 A B hA hB x.2 e
      simpa only [hxq] using hq
    · intro hf x
      obtain ⟨B, hB, hxB, _⟩ := exists_isAffineOpen_mem_and_subset
        (X := S) (x := f x) (U := ⊤) (by trivial)
      obtain ⟨A, hA, hxA, e⟩ := exists_isAffineOpen_mem_and_subset
        (X := X) (x := x) (U := f ⁻¹ᵁ B) hxB
      obtain ⟨hft, hq⟩ := hf A B hA hB e
      exact ⟨A, hxA, hA, B, hB, e, hft, hq (hA.primeIdealOf ⟨x, hxA⟩)⟩
  · constructor
    · intro hf
      refine ⟨PUnit, fun _ ↦ ⊤, fun _ ↦ PUnit, fun _ _ ↦ ⊤,
        fun _ _ ↦ by simp, by simp, fun _ ↦ by simp, fun _ _ ↦ ?_⟩
      exact isLocallyQuasiFinite_resLE f hf ⊤ ⊤ (by simp)
    · rintro ⟨J, B, I, A, e, hB, hA, hf⟩
      have hlocal : ∀ x : X, ∃ (U : S.Opens) (V : X.Opens) (_ : x ∈ V)
          (e : V ≤ f ⁻¹ᵁ U),
          LocallyQuasiFinite (f.resLE U V e) ∧ LocallyOfFiniteType (f.resLE U V e) := by
        intro x
        have hxB : f x ∈ ⨆ j, B j := by rw [hB]; trivial
        obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hxB
        have hxA : x ∈ ⨆ i, A j i := by rw [hA j]; exact hj
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxA
        exact ⟨B j, A j i, hi, e j i,
          (isLocallyQuasiFinite_iff (f.resLE (B j) (A j i) (e j i))).mp (hf j i)⟩
      apply (isLocallyQuasiFinite_iff f).mpr
      constructor
      · apply (IsZariskiLocalAtSource.iff_exists_resLE (P := @LocallyQuasiFinite)).mpr
        intro x
        obtain ⟨U, V, hx, e, hq, _⟩ := hlocal x
        exact ⟨U, V, hx, e, hq⟩
      · have : MorphismProperty.RespectsRight @LocallyOfFiniteType @IsOpenImmersion :=
          ⟨fun g hg f hf ↦ by
            have := hg
            have := hf
            infer_instance⟩
        apply (IsZariskiLocalAtSource.iff_exists_resLE (P := @LocallyOfFiniteType)).mpr
        intro x
        obtain ⟨U, V, hx, e, _, ht⟩ := hlocal x
        exact ⟨U, V, hx, e, ht⟩

end AlgebraicGeometry.Scheme.Hom
