/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Sheaf.Paper.ClosedTestDerivedExchangeMaps
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Paper.ClosedTestSectionLocalization
import Sheaf.Paper.ClosedTestClosedEvaluation

/-!
# Closed lifted-test exchange for a qcqs, possibly nonaffine, source

Source: Stacks Project, proetale.tex, Tags 09BK and 09BL, and
sites-cohomology.tex, Tag 0D6F; source-independent extension of the lifted-test calculation
(blueprint: lem-sfb-nonaffine-closed-test-exchange-identification).

The public affine-model module supplies canonical maps whose definitions have no
source-affineness assumption. Its already-general localization theorems are reused.
The closed-test criterion supplies covering, geometry and conservativity. The new
statements give the two normalized derived isomorphisms,
the identification with the actual ambient mate, and the compatibility clauses.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NonaffineClosedTestExchangeIdentification

open ClosedTestDerivedExchangeModel ClosedTestSectionSteps

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Reuse the canonical shift structure on the named derived direct image.
Source: derived-functor convention, Tag 0D6F
(blueprint: lem-sfb-nonaffine-closed-test-exchange-identification). -/
instance pushCommShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.moduleObjectDerivedPushforward Λ f).CommShift ℤ :=
  inferInstanceAs ((CondensedRing.lowerStar Λ f).rightDerivedFunctor.CommShift ℤ)

/-- Reuse the termwise shift structure on exact pullback.
Source: Tag 0D6F (blueprint: lem-sfb-nonaffine-closed-test-exchange-identification). -/
instance pullCommShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pull Λ f).CommShift ℤ :=
  inferInstanceAs ((CondensedRing.upperStar Λ f).mapDerivedCategory.CommShift ℤ)

/-- Reuse the composite canonical shift structure on localized derived sections.
Source: Tag 0D6F (blueprint: lem-sfb-nonaffine-closed-test-exchange-identification). -/
instance sectionsCommShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sectionsOver Λ f).CommShift ℤ :=
  inferInstanceAs ((pull Λ f ⋙
    (condensedModuleSections Λ X).rightDerivedFunctor).CommShift ℤ)

/-- The exact-pullback mate used in the section formulas is the actual ambient exchange,
transported only through the canonical exact-versus-left-derived pullback isomorphisms.
Source: Tag 09BL and the defining ambient mate
(blueprint: lem-sfb-nonaffine-closed-test-exchange-identification).
Proof (steps 6--8): the canonical comparison between total left derivation and exact
pullback preserves the adjunction unit and counit. Its compatibility with pullback
composition identifies the square comparisons. Expanding both mates as unit, square
comparison and counit then gives this equality, by uniqueness of adjoint transpose.
No invertibility of the exchange is used. -/
theorem actual_ambient_exchange (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} (f : X ⟶ Spec (.of A)) [QuasiCompact f] [QuasiSeparated f]
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ I)))
    (w : IsPullback h fZ f (closedMap A I)) :
    Functor.whiskerLeft (CondensedRing.moduleObjectDerivedPushforward Λ f)
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (closedMap A I)).inv ≫
      CondensedRing.condensedAmbientExchange Λ
        { toCommSq := w.toCommSq
          isoPullback := w.isoPullback
          hom_fst := w.isoPullback_hom_fst
          hom_snd := w.isoPullback_hom_snd } ≫
      Functor.whiskerRight (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ h).hom
        (CondensedRing.moduleObjectDerivedPushforward Λ fZ) =
      exchange Λ w.toCommSq := by
  sorry

/-- Canonical derived section isomorphisms for a qcqs source, without an affineness
hypothesis; they carry the evaluated exchange to the unit-defined derived restriction.
The normalization equations fix the isomorphisms, rather than merely asserting that the
objects happen to be isomorphic. Naturality in K is part of the natural-isomorphism type.
Source: Tags 09BK, 09BL and 0D6F
(blueprint: lem-sfb-nonaffine-closed-test-exchange-identification).

Proof: (1) Use only the source-independent paragraph of the closed-test criterion and
closed-site functor properties; fibre-product associativity gives the map between tests.
(2) The internal-module/sheaf-module equivalence preserves sections, and condensed
localization is slice restriction. (3) The actual closed adjunction-unit section map is
invertible by w-contractible evaluation, ind-etale basis comparison, specialization
counit and unit comparison, and affine_closed_inverseImage_evaluation.
(4) Resolve K by a K-injective I. The right adjoint f_* preserves K-injectives because
f^* is exact. Closed unit evaluation and (f_*I)(W)=I(X×_U W), followed by
unboundedSectionsLocalization, give the left isomorphism even when X is nonaffine.
(5) Resolve h^*I by J. The same calculation for fZ and ringed-site localization gives
the right isomorphism and identifies its target with b^*(K|T).
(6) Expand the ordinary mate. On a section over T the intermediate f-unit and
f-counit cancel, leaving the actual b-unit section. (7) Apply this degreewise and
compose with the resolution h^*I→J; the derived adjunction normalizes the counit.
(8) K-injective restriction and derived composition identify the resulting section map
with the derived b-unit followed by the canonical direct-image section comparison.
(9) K-injective Hom computation gives naturality and independence of resolutions.
Degreewise comparisons respect shifts and the connecting maps of triangles.
(10) Ringed derived slice localization preserves these units, counits and section
identities, so the construction respects restriction to an affine open target. -/
theorem nonaffine_closed_test_exchange_identification
    (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} (f : X ⟶ Spec (.of A)) [QuasiCompact f] [QuasiSeparated f]
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ I)))
    (w : IsPullback h fZ f (closedMap A I))
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤)] :
    ∃ eLeft :
        DerivedCategory.Plus.ι ⋙ CondensedRing.moduleObjectDerivedPushforward Λ f ⋙
            pull Λ (closedMap A I) ⋙ sectionsOver Λ V.hom ≅
          DerivedCategory.Plus.ι ⋙ sectionsOver Λ
            (pullback.fst f ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom),
      ∃ eRight :
        DerivedCategory.Plus.ι ⋙ pull Λ h ⋙
            CondensedRing.moduleObjectDerivedPushforward Λ fZ ⋙ sectionsOver Λ V.hom ≅
          DerivedCategory.Plus.ι ⋙ pull Λ h ⋙
            sectionsOver Λ (pullback.fst fZ V.hom),
        (∀ K : DerivedCategory.Plus
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
          IsIso ((closedComparison Λ A I V).app
            ((CondensedRing.moduleObjectDerivedPushforward Λ f).obj K.obj)) ∧
          (closedComparison Λ A I V).app
              ((CondensedRing.moduleObjectDerivedPushforward Λ f).obj K.obj) ≫
                eLeft.hom.app K =
            (sectionComparison Λ (IsPullback.of_hasPullback f
              ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom).toCommSq).app K.obj) ∧
        eRight.hom = Functor.whiskerLeft (DerivedCategory.Plus.ι ⋙ pull Λ h)
          (sectionComparison Λ (IsPullback.of_hasPullback fZ V.hom).toCommSq) ∧
        Functor.whiskerLeft DerivedCategory.Plus.ι
            (evaluatedExchange Λ A I w.toCommSq V) ≫ eRight.hom =
          eLeft.hom ≫ Functor.whiskerLeft DerivedCategory.Plus.ι
            (testRestriction Λ A I w.toCommSq V) ∧
        NatTrans.CommShift eLeft.hom ℤ ∧ NatTrans.CommShift eRight.hom ℤ ∧
        NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Plus.ι
          (evaluatedExchange Λ A I w.toCommSq V)) ℤ ∧
        IsClosedImmersion (testMap A I w.toCommSq V) := by
  sorry

/-- The normalized section comparisons and closed unit comparison respect all maps of
admissible tests. Together with the normalization equations of the main theorem, this
is precisely test naturality of both derived isomorphisms.
Source: Tags 09BL and 0D6F
(blueprint: lem-sfb-nonaffine-closed-test-exchange-identification).
Proof (step 9): unit-section comparison commutes with every affine-site map. The
presheaf restrictions I(T)→I(T') and J(T0)→J(T0') commute with those units because they
are sheaf morphisms. The section identities and resolution comparisons are natural,
so this degreewise equality descends to the indicated equality in D(Ab), without any
source-affineness assumption. -/
theorem nonaffine_test_naturality
    (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} (f : X ⟶ Spec (.of A)) [QuasiCompact f] [QuasiSeparated f]
    (fZ : XZ ⟶ Spec (.of (A ⧸ I)))
    (V V' : (Spec (.of (A ⧸ I))).AffineProEt) (r : V' ⟶ V)
    [IsWContractibleRing Γ(V.left, ⊤)] [IsWContractibleRing Γ(V'.left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V').left, ⊤)] :
    TestNaturality Λ f ((Scheme.AffineProEt.closedSiteLift A I).map r).left
        (MorphismProperty.Over.w ((Scheme.AffineProEt.closedSiteLift A I).map r)) ∧
      TestNaturality Λ fZ r.left (MorphismProperty.Over.w r) ∧
      (∀ K : DerivedCategory.Plus
          (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of A))) Ab.{u + 1})
            (condensedRingObj Λ (Spec (.of A)))),
        (closedComparison Λ A I V).app K.obj ≫
            (sectionsArrow Λ r.left (MorphismProperty.Over.w r)).app
              ((pull Λ (closedMap A I)).obj K.obj) =
          (sectionsArrow Λ ((Scheme.AffineProEt.closedSiteLift A I).map r).left
              (MorphismProperty.Over.w ((Scheme.AffineProEt.closedSiteLift A I).map r))).app
                K.obj ≫ (closedComparison Λ A I V').app K.obj) := by
  have hw (T : (Spec (.of (A ⧸ I))).AffineProEt) : WeaklyEtale T.hom :=
    proAffineEtale_le_weaklyEtale _ T.prop
  have hwLift (T : (Spec (.of (A ⧸ I))).AffineProEt) :
      WeaklyEtale ((Scheme.AffineProEt.closedSiteLift A I).obj T).hom :=
    proAffineEtale_le_weaklyEtale _ ((Scheme.AffineProEt.closedSiteLift A I).obj T).prop
  have := hw V
  have := hw V'
  have := hwLift V
  have := hwLift V'
  refine ⟨?_, ?_, ?_⟩
  · exact (proetale_section_localization Λ f
      ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom)
        ((Scheme.AffineProEt.closedSiteLift A I).obj V').hom
        ((Scheme.AffineProEt.closedSiteLift A I).map r).left
        (MorphismProperty.Over.w ((Scheme.AffineProEt.closedSiteLift A I).map r))
  · exact (proetale_section_localization Λ fZ V.hom) V'.hom r.left
      (MorphismProperty.Over.w r)
  · intro K
    exact (closed_derived_evaluation Λ A I V) V' r K.obj



end AlgebraicGeometry.ProEtale.NonaffineClosedTestExchangeIdentification
