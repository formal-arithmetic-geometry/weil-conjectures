/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionKernel

/-! # Bijection for Veronese section fractions

The canonical map from the section-fraction presentation, sending a class
`[n, ξ]` to the homogeneous fraction `ξ / s^n`, is constructed by descending
the explicit numerator map through the section-fraction relations.
Source: Stacks Project, Properties, Tags 0B5L, 01PW, and 01Q1.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical map from section-fraction classes to homogeneous fractions.
Source: Stacks Project, Properties, Tag 0B5L and Lemma 01PW(2).
(blueprint: lem-sc-section-ring-veronese-fractions-core)
Descend the explicit direct-sum numerator map to the quotient by section-fraction
relations. The proved kernel equality makes this well-defined; constructing the
map itself does not require choosing an inverse or proving surjectivity.
-/
noncomputable def sectionRingVeroneseFractionCanonicalMap
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    SectionFractionPresentation (L.tensorPow d) (𝟙_ X.Modules) (s.val d) →+
      HomogeneousLocalization.Away (sectionRingGrade L) s.val :=
  QuotientAddGroup.lift
    (sectionFractionRelations (L.tensorPow d) (𝟙_ X.Modules) (s.val d)).toAddSubgroup
    (sectionRingVeroneseFractionMap X L d s)
    (sectionRingVeroneseFractionMap_kernel X L d s).le

/-- The canonical Veronese fraction map is bijective.
Source: Stacks Project, Properties, Tag 0B5L and Lemma 01PW(2).
(blueprint: lem-sc-section-ring-veronese-fractions-core)
The map descends the explicit numerator-to-fraction map through the section-fraction
relations. Its kernel is precisely the relation subgroup, which gives injectivity
of the descended map. Surjectivity follows from the surjectivity of the numerator
map. On a fraction generator the quotient lift evaluates to the numerator map;
its summand formula and the tensor-power cancellation identity give exactly `ξ/s^n`.
The construction and proof also apply when `d=0`, `n=0`, or `s` is zero or nilpotent.
The quotient-lift computation is retained explicitly below.
The proof uses the kernel equality directly, so no inverse choice is introduced.
-/
theorem sectionRing_veronese_fraction_core
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    Function.Bijective
      (sectionRingVeroneseFractionCanonicalMap X L d s) ∧
    ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
      sectionRingVeroneseFractionCanonicalMap X L d s
        (sectionFraction (L.tensorPow d) (𝟙_ X.Modules) (s.val d) n
          ((eqToIso (congrArg L.tensorPow (by simp [Nat.mul_comm])) ≪≫
            L.tensorPowMulIso d n ≪≫ (λ_ _).symm).hom.app ⊤ (ξ.val (n • d)))) =
      HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
        ξ.val ξ.property := by
  have hformula (n : ℕ) (ξ : sectionRingGrade L (n • d)) :
      sectionRingVeroneseFractionCanonicalMap X L d s
        (sectionFraction (L.tensorPow d) (𝟙_ X.Modules) (s.val d) n
          ((sectionRingVeroneseNumeratorIso X L d n).hom.app ⊤ (ξ.val (n • d)))) =
        HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
          ξ.val ξ.property := by
    change sectionRingVeroneseFractionMap X L d s
      (DirectSum.of
        (fun i : ℕ ↦ Γ((𝟙_ X.Modules) ⊗ (L.tensorPow d).tensorPow i, ⊤)) n
        ((sectionRingVeroneseNumeratorIso X L d n).hom.app ⊤ (ξ.val (n • d)))) = _
    simp only [sectionRingVeroneseFractionMap, DirectSum.toAddMonoid_of,
      AddMonoidHom.comp_apply]
    rw [sectionRingVeroneseNumerator_cancel X L d n ξ]
    rfl
  refine ⟨⟨?_, ?_⟩, hformula⟩
  · exact (QuotientAddGroup.injective_lift_iff _ _
      (sectionRingVeroneseFractionMap_kernel X L d s).le).2
      (sectionRingVeroneseFractionMap_kernel X L d s)
  · intro z
    obtain ⟨n, a, ha, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (sectionRingGrade L) s.property z
    exact ⟨sectionFraction (L.tensorPow d) (𝟙_ X.Modules) (s.val d) n
      ((sectionRingVeroneseNumeratorIso X L d n).hom.app ⊤ (a (n • d))),
      hformula n ⟨a, ha⟩⟩

end AlgebraicGeometry.Scheme.Modules
