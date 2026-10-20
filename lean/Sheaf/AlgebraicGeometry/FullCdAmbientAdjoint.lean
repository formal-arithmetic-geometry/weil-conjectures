/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

import Sheaf.AlgebraicGeometry.ProEtaleGrothendieckSectionCoproducts
import Sheaf.CategoryTheory.FiniteCohomologicalDimensionInjectiveCoproducts
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import Sheaf.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.AlgebraicGeometry.ProperOpenSection
import Sheaf.AlgebraicGeometry.ClopenSectionComponent
import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
import Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
import WeilConjectures.Compactification.Cofiltered

/-! # Full cohomological dimension and the ambient exceptional adjoint

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-existence`, clause (b)
(blueprint: lem-sp-fullcd-ambient-adjoint).

This is the conditional statement on the ordinary unbounded small pro-etale derived
categories. It asserts no FullCD bound for a general proper morphism.
-/

@[expose] public section

set_option autoImplicit false

universe w u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem fixed_directImage_coproducts_of_fullCD
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (A : Type u) [CommRing A] [Finite A] (c : ℕ)
    (hcd : sfFullCohomologicalDimension p A c) (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor := by
  let F := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p
  let eX := sfIntrinsicModuleEquivalence X A
  let eY := sfIntrinsicModuleEquivalence Y A
  have hvan (M) (q : ℕ) (hq : c < q) : IsZero ((F.rightDerived q).obj M) := by
    apply F.isZero_rightDerived_of_isZero_homology
    apply eY.functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    let K := (DerivedCategory.singleFunctor _ 0).obj M
    let e : eY.functor.mapDerivedCategory.obj (F.rightDerivedFunctor.obj K) ≅
        (proEtaleConstantDerivedDirectImage p A).obj
          ((DerivedCategory.singleFunctor _ 0).obj (eX.functor.obj M)) :=
      ((sfIntrinsicDerivedDirectImageComparison p A).app K).symm ≪≫
        (proEtaleConstantDerivedDirectImage p A).mapIso
          ((eX.functor.mapDerivedCategorySingleFunctor 0).app M)
    exact (hcd.1 (eX.functor.obj M) q (by exact_mod_cast hq)).of_iso
      ((DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso e)
  obtain ⟨hpres, hacyclic⟩ := ProEt.lowerStar_coproducts_and_injectiveSum_acyclic
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p I
  let := hpres
  exact F.preservesColimitsOfShape_rightDerivedFunctor_of_injectiveCoproducts
    I c hvan hacyclic

private theorem candidate_isLeftAdjoint_of_fullCD
    {X Y : Scheme.{u}} {f : X ⟶ Y} (d : Compactification f)
    (A : Type u) [CommRing A] [Finite A] (c : ℕ)
    (hcd : sfFullCohomologicalDimension d.g A c) :
    (sfAmbientCompactSupportCandidate A d).IsLeftAdjoint := by
  let F := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) d.g
  let : F.rightDerivedFunctor.IsLeftAdjoint :=
    grothendieckDerived_hasRightAdjoint.{u + 1} F.rightDerivedFunctor
      (fixed_directImage_coproducts_of_fullCD d.g A c hcd)
  let e := sfIntrinsicDerivedEquivalence d.Z A
  let t := (e.invFunIdAssoc (proEtaleConstantDerivedDirectImage d.g A)).symm ≪≫
    Functor.isoWhiskerLeft e.inverse (sfIntrinsicDerivedDirectImageComparison d.g A)
  let : (proEtaleConstantDerivedDirectImage d.g A).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso t.symm
  let := (exceptionalOpenAdjunction d.i A).isLeftAdjoint
  change ((sfIntrinsicDerivedOpen A d.i) ⋙
    proEtaleConstantDerivedDirectImage d.g A).IsLeftAdjoint
  infer_instance

private noncomputable def intrinsic_open_exchange
    (A : Type u) [CommRing A] [Finite A]
    {U' U T' T : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] [IsOpenImmersion j']
    (hsq : IsPullback gU j' j g) :
    sfIntrinsicDerivedOpen A j ⋙ sfIntrinsicDerivedPullback A g ≅
      sfIntrinsicDerivedPullback A gU ⋙ sfIntrinsicDerivedOpen A j' := by
  let C := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let e := ((conjugateIsoEquiv
    ((ProEtale.openImmersionLowerShriekUpperStarAdjunction C j).comp
      (ProEtale.upperStarLowerStarAdjunction C g))
    ((ProEtale.upperStarLowerStarAdjunction C gU).comp
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction C j'))).symm
      (@asIso _ _ _ _ (ProEtale.baseChangeMap C hsq.toCommSq)
        (ProEtale.isIso_baseChangeMap_of_isPullback C hsq))).symm
  let t : sfIntrinsicExtensionByZero j A ⋙ sfIntrinsicPullback A g ≅
      sfIntrinsicPullback A gU ⋙ sfIntrinsicExtensionByZero j' A :=
    (sfIntrinsicTransportComp A _ _).symm ≪≫ sfIntrinsicTransportIso A e ≪≫
      sfIntrinsicTransportComp A _ _
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso t ≪≫ Functor.mapDerivedCategoryCompIso _ _

private theorem clopen_derived_section
    {X V : Scheme.{u}} (q : V ⟶ X) (s : X ⟶ V) [IsOpenImmersion s]
    (hclosed : IsClosed (Set.range s.base)) (hsection : s ≫ q = 𝟙 X)
    (A : Type u) [CommRing A] [Finite A] :
    Nonempty (sfIntrinsicDerivedOpen A s ⋙ proEtaleConstantDerivedDirectImage q A ≅ 𝟭 _) := by
  have h := clopenSectionComponent q s hclosed hsection A
  let : (sfIntrinsicExtensionByZero s A).PreservesKInjectiveComplexes :=
    ⟨fun I _ ↦ h.2.2.2.2.2.1 I inferInstance⟩
  obtain ⟨e, -⟩ := h.2.2.2.2.2.2
  exact ⟨(Functor.mapDerivedCategoryCompRightDerivedFunctorIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso e ≪≫
    (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _⟩

private theorem proper_open_comparison
    {X T₁ T₂ : Scheme.{u}} (p : T₁ ⟶ T₂) [IsProper p]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    [QuasiCompact j₁] [QuasiCompact j₂] (h : j₁ ≫ p = j₂)
    (A : Type u) [CommRing A] [Finite A] :
    Nonempty (sfIntrinsicDerivedOpen A j₂ ≅
      sfIntrinsicDerivedOpen A j₁ ⋙ proEtaleConstantDerivedDirectImage p A) := by
  let b := pullback.fst p j₂
  let q := pullback.snd p j₂
  let s := Etale.properOpenSection p j₁ j₂ h
  have geom := Etale.properOpenSectionGeometry p j₁ j₂ h
  let : IsOpenImmersion s := geom.1
  let r := conjugateIsoEquiv
    ((exceptionalOpenAdjunction j₂ A).comp
      (sfIntrinsicConstantModuleAdjunction p A).mapDerivedCategoryRightDerivedAdjunction)
    (((sfIntrinsicConstantModuleAdjunction q A).mapDerivedCategoryRightDerivedAdjunction).comp
      (exceptionalOpenAdjunction b A))
    (intrinsic_open_exchange A q b j₂ p (IsPullback.of_hasPullback p j₂).flip).symm
  let e := intrinsic_open_exchange A (𝟙 X) s j₁ b geom.2.2 ≪≫
    Functor.isoWhiskerRight (sfIntrinsicDerivedPullbackId A X) _ ≪≫ Functor.leftUnitor _
  obtain ⟨z⟩ := clopen_derived_section q s geom.2.1
    (pullback.lift_snd _ _ _) A
  let M := sfIntrinsicDerivedOpen A j₁ ⋙ proEtaleConstantDerivedDirectImage p A
  let lam : M ⋙ sfIntrinsicDerivedPullback A j₂ ≅ 𝟭 _ :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ r ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e _ ≪≫ z
  let eps := Functor.whiskerLeft M (exceptionalOpenAdjunction j₂ A).counit
  let : ∀ K, IsIso (eps.app K) :=
    fun K ↦ isIso_proper_open_derived_support p j₁ j₂ h A K
  have : IsIso eps := NatIso.isIso_of_isIso_app eps
  exact ⟨(Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight lam.symm _ ≪≫
    Functor.associator _ _ _ ≪≫ asIso eps⟩

private noncomputable def derived_push_comp
    {X Y Z : Scheme.{u}} (p : X ⟶ Y) (g : Y ⟶ Z)
    (A : Type u) [CommRing A] [Finite A] :
    proEtaleConstantDerivedDirectImage p A ⋙ proEtaleConstantDerivedDirectImage g A ≅
      proEtaleConstantDerivedDirectImage (p ≫ g) A :=
  ((((sfIntrinsicConstantModuleAdjunction g A).mapDerivedCategoryRightDerivedAdjunction).comp
    (sfIntrinsicConstantModuleAdjunction p A).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoLeft
      (sfIntrinsicDerivedPullbackComp A p g).symm).rightAdjointUniq
        (sfIntrinsicConstantModuleAdjunction (p ≫ g) A).mapDerivedCategoryRightDerivedAdjunction

private theorem candidate_refinement_iso
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {d e : Compactification f} (v : d ⟶ e)
    (A : Type u) [CommRing A] [Finite A] :
    Nonempty (sfAmbientCompactSupportCandidate A d ≅ sfAmbientCompactSupportCandidate A e) := by
  let : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  let : QuasiCompact e.i := e.quasiCompact_openImmersion inferInstance
  obtain ⟨a⟩ := proper_open_comparison v.hom d.i e.i v.i_hom A
  exact ⟨Functor.isoWhiskerLeft _
      (eqToIso (congrArg (fun t ↦ proEtaleConstantDerivedDirectImage t A) v.hom_g.symm)) ≪≫
    Functor.isoWhiskerLeft _ (derived_push_comp v.hom e.g A).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight a.symm _⟩

private theorem candidate_comparison_iso
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (d e : Compactification f) (A : Type u) [CommRing A] [Finite A] :
    Nonempty (sfAmbientCompactSupportCandidate A d ≅ sfAmbientCompactSupportCandidate A e) := by
  obtain ⟨r, ⟨a⟩, ⟨b⟩⟩ := Compactification.exists_common_refinement d e
  obtain ⟨t⟩ := candidate_refinement_iso a A
  obtain ⟨s⟩ := candidate_refinement_iso b A
  exact ⟨t.symm ≪≫ s⟩

private theorem ambient_datum_of_comparisons
    {X Y : Scheme.{u}} {f : X ⟶ Y} (d : Compactification f)
    (A : Type u) [CommRing A] [Finite A] (c : ℕ)
    (hcd : sfFullCohomologicalDimension d.g A c)
    [(sfAmbientCompactSupportCandidate A d).IsLeftAdjoint]
    (ht : ∀ e : Compactification f,
      Nonempty (sfAmbientCompactSupportCandidate A e ≅ sfAmbientCompactSupportCandidate A d)) :
    Nonempty (SfAmbientExceptionalRightAdjointDatum A f d) := by
  classical
  -- The comparisons are constructed above; this choice is among proved isomorphisms.
  let t := fun e ↦ Classical.choice (ht e)
  let a := Adjunction.ofIsLeftAdjoint (sfAmbientCompactSupportCandidate A d)
  refine ⟨{
    fullCD := ⟨c, hcd⟩
    rightAdjoint := fun _ ↦ _
    adjunction := fun e ↦ a.ofNatIsoLeft (t e).symm
    theta := fun {e h} _ ↦ t e ≪≫ (t h).symm
    rho := fun _ ↦ Iso.refl _
    unit_compatibility := ?_
    counit_compatibility := ?_
    theta_id := ?_
    rho_id := ?_
    theta_comp := ?_
    rho_comp := ?_
  }⟩
  · intro e h v K
    simp [a, Adjunction.ofNatIsoLeft, ← Functor.map_comp, Category.assoc]
  · intro e h v L
    simp [a, Adjunction.ofNatIsoLeft, Category.assoc]
  · intro e
    simp
  · intro e
    rfl
  · intro e h k v w
    simp
  · intro e h k v w
    simp

/-- A FullCD bound for the chosen proper part makes its compact-support candidate preserve
set-indexed coproducts and gives the coherent ambient exceptional right adjoint datum.
The datum supplies an adjunction at every compactification, including the distinguished
one, and natural refinement comparisons satisfying the unit, counit and cocycle equations.
The finite coefficient instance is supplied by the recorded positive-level finiteness
statement, without adding a hypothesis or choosing another coefficient ring.

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-existence`, clause (b);
Stacks Project, Tag 0F5Y, for the Brown representability step only
(blueprint: lem-sp-fullcd-ambient-adjoint).

Proof in words:
1. Transport the FullCD vanishing to fixed-scalar module sheaves. The qcqs direct-image
   coproduct and injective-sum acyclicity theorem, followed by the general finite-CD
   derived-coproduct theorem, gives coproduct preservation for the fixed-scalar total
   direct image. Apply Grothendieck-derived Brown representability there, where the site,
   Hom and indexing universes agree. Transport its adjunction through the canonical
   intrinsic realization equivalences, and compose with the exact open adjunction.
   The resulting left adjoint preserves coproducts in every indexing universe.
2. For a proper map identifying two opens, form the pullback of the target open. The
   section supplied by the source open is clopen. Transport ordinary open-extension
   base change through the coefficient equivalences. Its adjoint mate gives derived
   direct-image/open-restriction base change. Extension base change, the identity
   pullback, and the clopen-section theorem therefore identify the restriction of
   the direct image of extension by zero with the original complex. Here the clopen
   insertion preserves K-injectives, so the exact-precomposition derived-functor
   comparison applies on the entire unbounded category.
3. The proper-support theorem makes the actual open counit invertible on these direct
   images. Combining it with the restriction isomorphism gives an isomorphism from
   target extension by zero to the direct image of source extension by zero. Derived
   pushforward composition is obtained by uniqueness of right adjoints to the recorded
   exact pullback-composition isomorphism. Thus each refinement gives an isomorphism of
   compact-support candidates, and a common refinement gives one between any two.
4. Fix for each compactification e an isomorphism t_e from its candidate to the
   distinguished candidate. The datum asks for coherent comparisons, without prescribing
   them to be the individual geometric refinement maps. Set theta(v) = t_e followed by
   the inverse of t_h for v : e → h. Transport the distinguished adjunction along t_e,
   use its same right adjoint everywhere, and set every rho to the identity. Cancellation
   proves both cocycle equations; the explicit unit and counit formulas for adjunction
   transport prove their compatibility. This constructs the stated datum without needing
   coherence or uniqueness of the individual geometric comparisons. -/
theorem sfAmbientCompactSupport_preservesCoproducts_and_hasAmbientDatum_of_fullCD
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x))
    [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
    (f : X ⟶ Y) [f.IsOver S] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (d : Compactification f) (c : ℕ)
    (hcd : sfFullCohomologicalDimension d.g (Padic.coefficientExtensionRing l E n) c) :
    (∀ I : Type w, PreservesColimitsOfShape (Discrete I)
      (@sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E n) _
        (Padic.finite_coefficientExtensionRing l E n hn) X Y f d)) ∧
      HasAmbientExceptionalRightAdjointDatum l E n hn S X Y hS f d := by
  let := Padic.finite_coefficientExtensionRing l E n hn
  let := candidate_isLeftAdjoint_of_fullCD d (Padic.coefficientExtensionRing l E n) c hcd
  constructor
  · intro I
    infer_instance
  · exact ambient_datum_of_comparisons d (Padic.coefficientExtensionRing l E n) c hcd
      (fun e ↦ candidate_comparison_iso e d (Padic.coefficientExtensionRing l E n))

end AlgebraicGeometry.Scheme
