/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMap
import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapAwayOfPuncturedIso
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingPuncturedIso

/-! # Local torsion for the completed matching-ring kernel

Source: Stacks Project, Tags 05ER and 05EC.
(blueprint: lem-sbc-completed-matching-ring-map-kernel-local-torsion)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- Kernel elements are killed by powers of a finite set of maximal-ideal generators.
Source: Stacks Project, Tag 05ER, second paragraph (05EP and 05EQ), applied to
the affine charts in Tag 0BLH.
Proof: choose a finite generating family f of m = maximalIdeal A by Noetherianity.
Each D(f i) lies in U, and these opens cover U: a prime other than m cannot
contain every generator of m. Since q is finite, its inverse image over D(f i)
is affine, with ring B_i. Since s is finite, E is affine, with ring B'.
The overlap isomorphism over the completed base identifies B'_f_i with
C tensor_A B_i, where C is the m-adic completion. Restriction to double opens
gives the cocycle identifications. By the sheaf axiom, the matching ring B is
the compatible-families module H0 of these data, with its second projection to B'.
Completion of a Noetherian ring is flat. The H0 localization theorem identifies
B_f_i with B_i, with the prescribed chart projection. Thus localizing
C tensor_A B -> B' at f_i gives the overlap isomorphism C tensor_A B_i -> B'_f_i.
The ring pushout is C tensor_A B, and its comparison to B' is this map:
both maps send the two pushout factors to the second projection and the
completed structural map. Hence a kernel element is zero in the localization
of the pushout at the image of f_i. The equality criterion for localization
supplies e with image(f_i)^e * x = 0. No common exponent is asserted here.
If the generating family is empty, m = 0 and the conclusion on indices is
vacuous. A zero chart ring or a nilpotent generator gives a zero localization;
the same equality criterion applies.
(blueprint: lem-sbc-completed-matching-ring-map-kernel-local-torsion) -/
theorem completedRingMap_kernel_local_torsion
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    ∀ x, D.completedRingMap x = 0 →
      ∃ (t : ℕ) (f : Fin t → A),
        IsLocalRing.maximalIdeal A = Ideal.span (Set.range f) ∧
          ∀ i, ∃ e : ℕ,
            ((D.baseMap ≫ pushout.inl _ _).hom (f i)) ^ e * x = 0 := by
  intro x hx
  have : IsIso D.puncturedMap := D.puncturedMap_isIso hU
  obtain ⟨t, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal A))
  refine ⟨t, f, hf.symm, ?_⟩
  intro i
  have hfi : f i ∈ IsLocalRing.maximalIdeal A := by
    rw [← hf]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hbasic : (PrimeSpectrum.basicOpen (f i) : (Spec (.of A)).Opens) ≤ U := by
    intro p hp
    apply (hU p).2
    intro heq
    subst p
    exact hp hfi
  have hbij := D.completedRingMap_away_bijective_of_puncturedMap_isIso (f i) hbasic
  exact Localization.awayMap_injective_iff.mp hbij.1 x hx

end AlgebraicGeometry.Scheme.CompletionGluingData
