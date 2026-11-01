/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.InvertibleExponent
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Finite closed-support constructibility coordinates

The finite-ring derived comparison identifies the intrinsic bounded constructibility
predicate with bounded constructible complexes in fixed-scalar coordinates. This proof
uses no compact-support coefficient comparison or normalized coefficient system.
Source: Stacks, Tag 09AL, and the finite-domain step of the current blueprint proof
of `lem-coef-finite-closed-shriek` (blueprint: lem-coef-finite-closed-realization-domain).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end WeilConjectures

namespace WeilConjectures

private theorem finiteClosed_finite_homology_support_iff
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) :
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor C i).obj K)} ↔
      ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((DerivedCategory.homologyFunctor C i).obj K) := by
  classical
  constructor
  · intro h
    obtain ⟨a, ha⟩ := h.bddBelow
    obtain ⟨b, hb⟩ := h.bddAbove
    refine ⟨min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    by_contra hn
    rcases hi with hi | hi
    · exact (not_lt_of_ge (le_trans (min_le_left _ _) (ha hn))) hi
    · exact (not_lt_of_ge (le_trans (hb hn) (le_max_right _ _))) hi
  · rintro ⟨a, b, _, h⟩
    apply (Set.finite_Icc a b).subset
    intro i hi
    exact ⟨le_of_not_gt (fun hia ↦ hi (h i (Or.inl hia))),
      le_of_not_gt (fun hbi ↦ hi (h i (Or.inr hbi)))⟩

private theorem finiteClosed_intrinsic_bc_iff_etale_origin
    (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    (K : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n)) :
    letI := Padic.finite_coefficientExtensionRing l E n hn
    intrinsicFiniteTorsionConstructible l E n hn T K ↔
      ∃ G : Etale.DerivedCategoryModule
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T,
        Etale.DerivedCategory.isBoundedConstructible
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T G ∧
        Nonempty ((ProEtale.finiteCoefficientIntrinsicDerivedComparison T
          (Padic.coefficientExtensionRing l E n)).obj G ≅ K) := by
  have := Padic.finite_coefficientExtensionRing l E n hn
  have h := (finiteRing_constructibleDerived_origin T
    (Padic.coefficientExtensionRing l E n)).2.2.1 K
  rw [intrinsicFiniteTorsionConstructible, finiteClosed_finite_homology_support_iff]
  rw [and_comm, ← h]
  constructor
  · rintro ⟨G, ⟨e⟩⟩
    exact ⟨G.obj, G.property, ⟨e⟩⟩
  · rintro ⟨G, hG, ⟨e⟩⟩
    exact ⟨⟨G, hG⟩, ⟨e⟩⟩

private theorem finiteClosed_etale_bc_iff
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (G : Etale.DerivedCategoryModule A T) :
    Etale.DerivedCategory.isBoundedConstructible A T G ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T G := by
  constructor
  · rintro ⟨hc, a, b, _, hab⟩
    exact ⟨⟨⟨a, (DerivedCategory.isGE_iff G a).2 fun i hi ↦ hab i (Or.inl hi)⟩,
      ⟨b, (DerivedCategory.isLE_iff G b).2 fun i hi ↦ hab i (Or.inr hi)⟩⟩,
      fun i ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)⟩
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i),
      min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff G a).1 ha i (hi.trans_le (min_le_left _ _))
    · exact (DerivedCategory.isLE_iff G b).1 hb i ((le_max_right _ _).trans_lt hi)

/-- Intrinsic bounded constructibility agrees with the fixed-coefficient etale-origin
predicate under the canonical realization equivalence.
Source: Stacks, Tag 09AL, finite-ring constructible derived comparison, and current blueprint
finite closed shriek proof, finite-domain step
(blueprint: lem-coef-finite-closed-realization-domain).

Proof: finite cohomological support is equivalent to an ordered finite vanishing interval.
The finite-ring constructible derived comparison identifies intrinsic bounded constructibility
with the essential image of bounded constructible etale complexes. Its comparison functor
is the composite of fixed-coefficient inverse image and the canonical realization equivalence.
Translate the etale cohomology predicate into the existing bounded-constructible predicate,
and use full faithfulness of realization to transport the representing isomorphism in both
directions. No coefficient transition or completion is involved. -/
theorem finiteClosed_intrinsic_bc_realization_iff
    (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    (L : DerivedCategory (Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))))) :
    letI := Padic.finite_coefficientExtensionRing l E n hn
    intrinsicFiniteTorsionConstructible l E n hn T
      ((sfIntrinsicDerivedEquivalence T (Padic.coefficientExtensionRing l E n)).functor.obj L) ↔
      ProEtale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) T L := by
  have := Padic.finite_coefficientExtensionRing l E n hn
  let A := Padic.coefficientExtensionRing l E n
  let F := sfIntrinsicDerivedEquivalence T A
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T
  let r : C.mapDerivedCategory ⋙ F.functor ≅
      ProEtale.finiteCoefficientIntrinsicDerivedComparison T A :=
    (Functor.mapDerivedCategoryCompIso C (sfIntrinsicModuleEquivalence T A).functor).symm
  rw [finiteClosed_intrinsic_bc_iff_etale_origin l E n hn]
  constructor
  · rintro ⟨G, hG, ⟨e⟩⟩
    refine ⟨G, (finiteClosed_etale_bc_iff _ _ G).1 hG, ⟨?_⟩⟩
    exact F.fullyFaithfulFunctor.preimageIso ((r.app G) ≪≫ e)
  · rintro ⟨G, hG, ⟨e⟩⟩
    exact ⟨G, (finiteClosed_etale_bc_iff _ _ G).2 hG, ⟨(r.app G).symm ≪≫ F.functor.mapIso e⟩⟩

end WeilConjectures
