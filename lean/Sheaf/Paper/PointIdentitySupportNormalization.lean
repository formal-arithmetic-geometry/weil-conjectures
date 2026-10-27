/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Paper.ExceptionalAdjointAdmissibility
public import Sheaf.AlgebraicGeometry.ClopenSectionComponent
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-!
# Identity support and its coefficient normalization

Source: blueprint `sk-thm-sf-global-duality/lem-sf-point.proof.md`, identity-adjunction
sentence, expanded in steps 1, 3--5 and 8 of `lem-sf-point-identity-admissibility`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The two clauses of the clopen-section theorem used to construct identity support.
Source: `lem-sp-clopen-section-component`, K-injective and normalized-section clauses.
(blueprint: lem-sf-point-identity-support-normalization). -/
theorem pointIdentityClopenComparison (s : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] (d : Compactification (𝟙 s)) :
    (sfIntrinsicExtensionByZero d.i A).PreservesKInjectiveComplexes ∧
      ∃ e : sfIntrinsicExtensionByZero d.i A ⋙ proEtaleConstantModuleDirectImage d.g A ≅
          𝟭 (proEtaleRingModules s (proEtaleConstantRing s A)),
        ClopenSectionComparisonOnSections d.g d.i d.comm.symm A e.hom := by
  constructor
  · exact ⟨fun I hI ↦ (clopenSectionComponent d.g d.i
      (d.isClopen_range_openImmersion inferInstance).isClosed d.comm.symm A).2.2.2.2.2.1 I hI⟩
  · have h := (clopenSectionComponent d.g d.i
      (d.isClopen_range_openImmersion inferInstance).isClosed d.comm.symm A).2.2.2.2.2.2
    exact ⟨h.choose, h.choose_spec.1⟩

/-- The support isomorphism constructed from the sectionwise clopen comparison.
The comparison chosen by `clopenSectionComponent` is determined by its equation on
sections: restriction to the section component followed by the inverse open unit.
Source: blueprint `lem-sf-point.proof.md`, identity-adjunction sentence, and
`lem-sp-clopen-section-component`, the displayed section equation.
(blueprint: lem-sf-point-identity-support-normalization). -/
@[irreducible] noncomputable def pointIdentitySupportIso (s : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] (d : Compactification (𝟙 s)) :
    sfAmbientCompactSupportCandidate A d ≅ 𝟭 _ := by
  let : (sfIntrinsicExtensionByZero d.i A).PreservesKInjectiveComplexes :=
    (pointIdentityClopenComparison s A d).1
  let e := (pointIdentityClopenComparison s A d).2.choose
  exact (Functor.mapDerivedCategoryCompRightDerivedFunctorIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso e ≪≫
    (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The constructed identity support identifications normalize the published left
coefficient comparison for every finite coefficient-ring map.

Source: blueprint `sk-thm-sf-global-duality/lem-sf-point.proof.md`, identity-adjunction
sentence; parent proof steps 1, 3--5 and the left-comparison part of step 8.
(blueprint: lem-sf-point-identity-support-normalization).

Proof: for a compactification s --j--> Z --p--> s of the identity, j is a section
of the separated map p and hence a closed immersion. Its image is also open.
The decomposition of Z into this image and its complement identifies j_! with
j_*: both send M to the pair (M,0). This functor is exact. Thus its termwise
derived functor agrees with Rj_*. Compose with Rp_* and the canonical derived
composition comparison, then use pj=id, to obtain beta_d : F_d ≅ id. Do this
using the canonical section and composition comparisons, simultaneously for all
finite coefficient rings. At the proper identity compactification both geometric
maps are identities. The restriction-of-scalars comparison defining the published
support coefficient map is the identity under these identifications, since its
sectionwise map sends each section to itself. Transposition through the actual
tensor/restriction adjunction gives the displayed equation, on K-flat resolutions
also for nonflat ring maps. Zero coefficient rings and identity ring maps use the
same construction; no faithful-flatness assumption enters. -/
theorem point_identity_support_normalization (s : Scheme.{u})
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (K : proEtaleDerivedCategory s A) :
    (exceptionalFiniteSupportExtensionMap φ (Compactification.ofIsProper (𝟙 s))).app K ≫
        (pointIdentitySupportIso s B (Compactification.ofIsProper (𝟙 s))).hom.app
          ((exceptionalCoefficientExtension φ s).obj K) =
      (exceptionalCoefficientExtension φ s).map
        ((pointIdentitySupportIso s A (Compactification.ofIsProper (𝟙 s))).hom.app K) := by
  sorry

end WeilConjectures
