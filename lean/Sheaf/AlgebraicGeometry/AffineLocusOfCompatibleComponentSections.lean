/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import all WeilConjectures.AlgebraicGeometry.AmpleIso
import Sheaf.AlgebraicGeometry.IsAffineOfFiniteClosedCover
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import WeilConjectures.AlgebraicGeometry.NonvanishingTensorPullback

/-! # Affineness of a compatible component section locus

Source: Stacks Project, Varieties Lemma 09NX, second paragraph;
Limits Lemma 09NL and Properties Section 01PR.
(blueprint: lem-sc-affine-locus-compatible-component-sections).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules


/-- A fixed global section with affine component loci has affine locus, and contains
any set whose inverse images lie in those loci.

Source: Stacks Project, Varieties Lemma 09NX, second paragraph;
Limits Lemma 09NL and Properties Section 01PR.
(blueprint: lem-sc-affine-locus-compatible-component-sections).

Proof: let W be the nonvanishing locus of t. It is open because L is invertible:
in a local frame it is the basic open of the section coefficient. At a component
point, the adjunction unit identifies the pulled-back fibre value with one tensor
the value of t. The residue-field map is injective, so extension of this rank-one
vector space preserves and reflects nonzero values. Each e a preserves nonvanishing,
and the section compatibility identifies the inverse image of W with V a.
For x in T choose a component point y over it by hcover. The containment hypothesis
makes s a nonvanishing at y, and the fibre calculation puts x in W. The restricted
closed immersions (V a).toScheme → W.toScheme form a finite closed cover. Their
sources are affine by hVaff. Apply isAffine_of_finite_closed_cover, including its
empty-cover case, to conclude that W is affine. Finally transport t along the inverse
right unitor L ≅ L.tensorPow 1; a module isomorphism preserves the maximal ideal
times each stalk and hence the nonvanishing locus. The transported section q has
locus W, giving the stated witnesses. Neither reducedness nor finiteness or closedness
of T is needed for this argument: all gluing is already supplied as input.
-/
theorem affine_locus_of_compatible_component_sections
    (X : Scheme.{u}) (r : ℕ) (C : Fin r → Scheme.{u})
    (i : ∀ a, C a ⟶ X) [∀ a, IsClosedImmersion (i a)]
    (hcover : (⋃ a, Set.range (i a)) = Set.univ) (T : Set X)
    (L : X.Modules) [L.IsInvertible] (t : Γ(L, ⊤))
    (P : ∀ a, (C a).Modules) [∀ a, (P a).IsInvertible]
    (s : ∀ a, Γ(P a, ⊤)) (V : ∀ a, (C a).Opens)
    (hTV : ∀ a, i a ⁻¹' T ⊆ nonvanishingLocus (P a) (s a))
    (hVlocus : ∀ a, (V a : Set (C a)) = nonvanishingLocus (P a) (s a))
    (hVaff : ∀ a, IsAffineOpen (V a))
    (he : ∀ a, ∃ e : (tensorPullback (i a)).obj L ≅ P a,
      e.hom.val.app (op ⊤)
        (((Classical.choose (exists_tensorPullbackAdjunction (i a))).unit.app L).val.app
          (op ⊤) t) = s a) :
    ∃ (q : (L.tensorPow 1).val.presheaf.obj (op ⊤)) (U : X.Opens),
      T ⊆ (U : Set X) ∧ IsAffineOpen U ∧
        (U : Set X) = nonvanishingLocus (L.tensorPow 1) q  := by
  classical
  obtain ⟨U, hU, _⟩ := nonvanishing_section_trivializes X L t
  have hlocus (a : Fin r) :
      nonvanishingLocus (P a) (s a) = (i a) ⁻¹' nonvanishingLocus L t := by
    obtain ⟨e, he⟩ := he a
    rw [← he]
    erw [nonvanishingLocus_iso e]
    ext x
    exact nonvanishing_tensorPullback (i a) L t x
  have hpre (a : Fin r) : (i a) ⁻¹ᵁ U = V a := by
    ext x
    change i a x ∈ (U : Set X) ↔ x ∈ (V a : Set (C a))
    rw [hU, hVlocus a, hlocus a]
    rfl
  have hT : T ⊆ (U : Set X) := by
    intro x hx
    have hxcover : x ∈ ⋃ a, Set.range (i a) := by rw [hcover]; trivial
    obtain ⟨a, y, hy⟩ := Set.mem_iUnion.mp hxcover
    rw [hU, ← hy]
    exact (hlocus a).le (hTV a (by change i a y ∈ T; rwa [hy]))
  have hAffine (a : Fin r) : IsAffine (((i a) ⁻¹ᵁ U).toScheme) := by
    rw [hpre a]
    exact hVaff a
  have hclosed (a : Fin r) : IsClosedImmersion ((i a) ∣_ U) := inferInstance
  have hcov : ∀ x : U.toScheme, ∃ a : Fin r,
      ∃ y : ((i a) ⁻¹ᵁ U).toScheme, ((i a) ∣_ U) y = x := by
    intro x
    have hxcover : x.1 ∈ ⋃ a, Set.range (i a) := by rw [hcover]; trivial
    obtain ⟨a, y, hy⟩ := Set.mem_iUnion.mp hxcover
    refine ⟨a, ⟨y, ?_⟩, ?_⟩
    · change i a y ∈ U
      rw [hy]
      exact x.property
    · apply Subtype.ext
      simpa only [morphismRestrict_base_coe] using hy
  have hAffU : IsAffine U.toScheme := isAffine_of_finite_closed_cover
    U.toScheme r (fun a ↦ ((i a) ⁻¹ᵁ U).toScheme) (fun a ↦ (i a) ∣_ U) hcov
  let e : L ≅ L.tensorPow 1 := (ρ_ L).symm
  refine ⟨e.hom.app ⊤ t, U, hT, hAffU, ?_⟩
  exact hU.trans (nonvanishingLocus_iso e t).symm

end AlgebraicGeometry.Scheme.Modules
