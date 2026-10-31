/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteCompactSupportExact
public import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules

public import WeilConjectures.AlgebraicGeometry.EtaleSumRightAdjointCoherenceSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSupportMapCompatibility
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.LowerShriek.BaseChange

import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange

/-! # Refinement and open coherence of normalized etale tensor families

Source: blueprint sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-etale-locality.proof.md, Step 1; Stacks Tags 03S6 and 0GKF
(blueprint: lem-pur-etale-normalization-comparison-coherence).

All arrows below are built from the specified graph comparison, proper/open compositor,
exact inverse-image compositor, and adjunction conjugacy. Right adjoints are arbitrary
chosen right adjoints equipped with their adjunctions.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Transporting the right adjoint and then using uniqueness gives the inverse mate.
Expand the inverse-mate component formula and the transported adjunction's unit. -/
private theorem uniq_eq_conjugate
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (i : R₁ ≅ R₂) :
    ((a.ofNatIsoRight i).leftAdjointUniq b).inv =
      (conjugateEquiv a b).symm i.hom := by
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateIsoEquiv, conjugateEquiv_symm_apply_app]

/-- Rho for an arbitrary chosen compactification, conjugating the inverse graph comparison.
Source: blueprint Step 1 (blueprint: lem-pur-etale-normalization-comparison-coherence). -/
noncomputable def etaleNormalizationRho
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G) :
    G ≅ (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory :=
  conjugateIsoEquiv adj
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
    (canonicalEtaleCompactSupportComparison A e c).symm

/-- Eta is rho at the constant coefficient object followed by the fixed pullback unit.
Source: blueprint Step 1 (blueprint: lem-pur-etale-normalization-comparison-coherence). -/
noncomputable def etaleNormalizationEta
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G) :
    G.obj (constantComplex A X) ≅ constantComplex A U :=
  (etaleNormalizationRho A e c G adj).app (constantComplex A X) ≪≫
    etaleSumPullbackUnitIso A e

/-- The refinement r is the conjugate of the inverse canonical common-refinement t.
Source: Stacks Tag 0F7I (blueprint: lem-pur-etale-normalization-comparison-coherence). -/
noncomputable def etaleNormalizationRefinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} {e : U ⟶ X} [QuasiCompact e] (c d : Compactification e)
    (G H : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ H) : G ≅ H :=
  conjugateIsoEquiv adj adj' (rightDerivedLowerShriekOfCompactificationIso A c d).symm

/-- The actual compactification projection, transported from left-derived to exact pullback.
Source: support-map compatibility (2), Stacks Tag 0GKF
(blueprint: lem-pur-etale-normalization-comparison-coherence). -/
noncomputable def etaleNormalizationProjection
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (e : U ⟶ X)
    (c : Compactification e) (M : DerivedCategoryModule A U) (K : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M)).obj K ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        (((derivedTensor (ModuleCat.{u + 1} A) U).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) :=
  ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (((derivedTensor (ModuleCat.{u + 1} A) U).obj M).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).hom.app K))

/-- Canonical beta for the square, using the exact pullback compositors of the dependency.
Source: blueprint Step 1 (blueprint: lem-pur-etale-normalization-comparison-coherence). -/
noncomputable def etaleNormalizationBeta
    (A : Type (u + 1)) [CommRing A] {U U' X X' : Scheme.{u}}
    {e : U ⟶ X} {e' : U' ⟶ X'} {g : X' ⟶ X} {h : U' ⟶ U}
    (sq : IsPullback h e' e g) :
    (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory :=
  (unboundedEtaleUpperStarCompIso A h e).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) e' g (h ≫ e) sq.w) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The specified composition comparison with the open supports identified by their d maps.
The middle arrows are the actual proper/open compact-support compositors, not a comparison
chosen by its endpoints or defined by rho.
Source: Stacks Tags 0F7J and 0F7K; blueprint Step 1
(blueprint: lem-pur-etale-normalization-comparison-coherence). -/
noncomputable def etaleNormalizationOpenLeft
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {g : X' ⟶ X} {h : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e'] [IsOpenImmersion g] [IsOpenImmersion h]
    (sq : IsPullback h e' e g) (c : Compactification e) (d : Compactification e') :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⋙
        (etaleLowerShriek (ModuleCat.{u + 1} A) g inferInstance).mapDerivedCategory ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) h inferInstance).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  Functor.isoWhiskerRight (rightDerivedLowerShriekIso A d) _ ≪≫
    Functor.isoWhiskerLeft _ (etaleSumSupportIso A g).symm ≪≫
    unboundedEtaleLowerShriekCompIso A e' g ≪≫
    unboundedEtaleLowerShriekCongr A sq.w.symm ≪≫
    (unboundedEtaleLowerShriekCompIso A h e).symm ≪≫
    Functor.isoWhiskerRight (etaleSumSupportIso A h) _ ≪≫
    Functor.isoWhiskerLeft _ (rightDerivedLowerShriekIso A c).symm

/-- Chi is the conjugate of the specified compact-support composition comparison.
Source: blueprint Step 1 (blueprint: lem-pur-etale-normalization-comparison-coherence). -/
noncomputable def etaleNormalizationChi
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {g : X' ⟶ X} {h : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e'] [IsOpenImmersion g] [IsOpenImmersion h]
    (sq : IsPullback h e' e g) (c : Compactification e) (d : Compactification e')
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (H : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ H) :
    G ⋙ (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙ H :=
  conjugateIsoEquiv
    ((derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) h inferInstance).comp adj)
    (adj'.comp (derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) g inferInstance))
    (etaleNormalizationOpenLeft A sq c d)

/-- Xi is chi at A_X followed by G' of the coefficient pullback unit.
Source: blueprint Step 1 (blueprint: lem-pur-etale-normalization-comparison-coherence). -/
noncomputable def etaleNormalizationXi
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {g : X' ⟶ X} {h : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e'] [IsOpenImmersion g] [IsOpenImmersion h]
    (sq : IsPullback h e' e g) (c : Compactification e) (d : Compactification e')
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (H : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ H) :
    (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj
        (G.obj (constantComplex A X)) ≅ H.obj (constantComplex A X') :=
  (etaleNormalizationChi A sq c d G H adj adj').app (constantComplex A X) ≪≫
    H.mapIso (etaleSumPullbackUnitIso A g)

/-- Refinement preserves d, rho, eta, and the specified compactification projection.
Source: blueprint Step 1; Stacks Tags 0F7I and 0GKF
(blueprint: lem-pur-etale-normalization-comparison-coherence).

Proof: use the existing right-adjoint refinement equation for rho. Injectivity of
adjunction conjugacy recovers the inverse left comparison equation; invert it to obtain
d' t = d. Evaluate the rho equation at A_X and postcompose with u_e for eta.
The upstream compactification comparison intertwines the specified projections with
left-derived pullback. Postcompose with the tensor of the exact-pullback comparison;
naturality of t gives the claimed equation for the transported projections. -/
theorem etaleNormalizationComparison_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c d : Compactification e)
    (G H : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ H) :
    (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
        (canonicalEtaleCompactSupportComparison A e d).hom =
      (canonicalEtaleCompactSupportComparison A e c).hom ∧
    etaleNormalizationRefinement A c d G H adj adj' ≪≫
        etaleNormalizationRho A e d H adj' = etaleNormalizationRho A e c G adj ∧
    (etaleNormalizationRefinement A c d G H adj adj').app (constantComplex A X) ≪≫
        etaleNormalizationEta A e d H adj' = etaleNormalizationEta A e c G adj ∧
    ∀ (M : DerivedCategoryModule A U) (K : DerivedCategoryModule A X),
      etaleNormalizationProjection A e c M K ≫
          (rightDerivedLowerShriekOfCompactificationIso A c d).hom.app
            (((derivedTensor (ModuleCat.{u + 1} A) U).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) =
        derivedTensorHom (ModuleCat.{u + 1} A)
            ((rightDerivedLowerShriekOfCompactificationIso A c d).hom.app M) (𝟙 K) ≫
          etaleNormalizationProjection A e d M K := by
  have hr := etaleSumRightAdjoint_refinement A e c d G H adj adj'
  have hrho : etaleNormalizationRefinement A c d G H adj adj' ≪≫
      etaleNormalizationRho A e d H adj' = etaleNormalizationRho A e c G adj := by
    simpa only [etaleNormalizationRefinement, etaleNormalizationRho] using hr.symm
  have hc : (canonicalEtaleCompactSupportComparison A e d).symm ≪≫
      (rightDerivedLowerShriekOfCompactificationIso A c d).symm =
      (canonicalEtaleCompactSupportComparison A e c).symm := by
    apply (conjugateIsoEquiv adj
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
        inferInstance)).injective
    rw [conjugateIsoEquiv_trans]
    exact hr.symm
  have heta : (etaleNormalizationRefinement A c d G H adj adj').app
      (constantComplex A X) ≪≫ etaleNormalizationEta A e d H adj' =
      etaleNormalizationEta A e c G adj := by
    apply Iso.ext
    simp only [etaleNormalizationEta, Iso.trans_hom, Iso.app_hom]
    have hh := NatTrans.congr_app (congrArg Iso.hom hrho) (constantComplex A X)
    simp only [Iso.trans_hom, NatTrans.comp_app] at hh
    simpa only [Category.assoc] using congrArg
      (fun z ↦ z ≫ (etaleSumPullbackUnitIso A e).hom) hh
  refine ⟨?_, hrho, heta, ?_⟩
  · simpa only [Iso.trans_inv, Iso.symm_inv] using congrArg Iso.inv hc
  · intro M K
    have hp := projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso
      A c d M K
    simp only [etaleNormalizationProjection, Category.assoc]
    rw [(rightDerivedLowerShriekOfCompactificationIso A c d).hom.naturality]
    erw [← Category.assoc, hp]
    simp only [derivedTensorHom, CategoryTheory.Functor.map_id, Category.comp_id,
      Category.assoc]

/-- Canonical sum base change on an arbitrary Cartesian square, descended termwise.
Source: Stacks Tag 03S6 (blueprint: lem-pur-etale-normalization-comparison-coherence). -/
noncomputable def etaleNormalizationSumExchange
    (A : Type (u + 1)) [CommRing A] {U U' X X' : Scheme.{u}}
    {e : U ⟶ X} {e' : U' ⟶ X'} {g : X' ⟶ X} {h : U' ⟶ U}
    [Etale e] [Etale e'] (sq : IsPullback h e' e g) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory ⋙
        (etaleLowerShriek (ModuleCat.{u + 1} A) e' inferInstance).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (etaleLowerShriekBaseChangeIso A sq.flip) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The specified proper/open exchange, followed by the canonical comparison to c'.
Source: Stacks Tag 0F7L (blueprint: lem-pur-etale-normalization-comparison-coherence). -/
noncomputable def etaleNormalizationExchange
    (A : Type (u + 1)) [CommRing A] [Finite A] {U U' X X' : Scheme.{u}}
    {e : U ⟶ X} {e' : U' ⟶ X'} {g : X' ⟶ X} {h : U' ⟶ U}
    [QuasiCompact e'] (sq : IsPullback h e' e g)
    (c : Compactification e) (d : Compactification e') :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d :=
  unboundedEtaleCompactSupportExchange A sq c ≫
    Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory
      (rightDerivedLowerShriekOfCompactificationIso A (c.ofIsPullback sq) d).hom

set_option linter.unusedVariables false in
/-- Identity, composition and common-refinement independence for the specified comparisons.
Source: Stacks Tag 0F7I (blueprint: lem-pur-etale-normalization-comparison-coherence).

Proof: use the identity and cocycle laws of unbounded compact-support comparisons.
Conjugacy reverses composition, and sends the identity to the identity. The cocycle
law identifies any route through a third compactification with the direct comparison,
so a common refinement gives the same map regardless of its choice. -/
theorem etaleNormalizationComparison_refinement_laws
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (G : ∀ c : Compactification e, DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : ∀ c : Compactification e,
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G c) :
    (∀ c : Compactification e,
      rightDerivedLowerShriekOfCompactificationIso A c c = Iso.refl _ ∧
      etaleNormalizationRefinement A c c (G c) (G c) (adj c) (adj c) = Iso.refl _) ∧
    (∀ c d f : Compactification e,
      rightDerivedLowerShriekOfCompactificationIso A c d ≪≫
          rightDerivedLowerShriekOfCompactificationIso A d f =
        rightDerivedLowerShriekOfCompactificationIso A c f ∧
      etaleNormalizationRefinement A c d (G c) (G d) (adj c) (adj d) ≪≫
          etaleNormalizationRefinement A d f (G d) (G f) (adj d) (adj f) =
        etaleNormalizationRefinement A c f (G c) (G f) (adj c) (adj f)) := by
  obtain ⟨hid, hcomp⟩ := unboundedEtaleCompactSupport_comparison_coherence A e
  constructor
  · intro c
    refine ⟨hid c, ?_⟩
    unfold etaleNormalizationRefinement
    rw [hid c]
    apply Iso.ext
    simp only [conjugateIsoEquiv_apply_hom]
    exact conjugateEquiv_id _
  · intro c d f
    refine ⟨hcomp c d f, ?_⟩
    unfold etaleNormalizationRefinement
    have h := hcomp c d f
    apply Iso.ext
    rw [← conjugateIsoEquiv_trans (adj c) (adj d) (adj f)
      (rightDerivedLowerShriekOfCompactificationIso A c d).symm
      (rightDerivedLowerShriekOfCompactificationIso A d f).symm]
    have ht : (rightDerivedLowerShriekOfCompactificationIso A d f).symm ≪≫
        (rightDerivedLowerShriekOfCompactificationIso A c d).symm =
        (rightDerivedLowerShriekOfCompactificationIso A c f).symm := by
      apply Iso.ext
      have hi := congrArg Iso.inv h
      simpa only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
        Category.assoc] using hi
    rw [ht]

/-- The open composition conjugate has the stated rho formula and preserves eta.
Source: blueprint Step 1; Stacks Tags 03S6 and 0F7J
(blueprint: lem-pur-etale-normalization-comparison-coherence).

Proof: on a nested sum, the composite-adjunction unit inserts two identity lifts.
Flattening the nested support gives the single identity lift, so the sum compositor's
conjugate is the specified pullback compositor beta. The proper-support composition
normalization identifies the actual open-left comparison with this sum compositor,
conjugated by d and d'. Mate pasting gives rho' chi = beta h^*rho. Cancel rho'.
At A_X, naturality of rho' at u_g and coefficient-unit composition give
eta' xi = u_h h^*eta. These are the fixed units, rather than arbitrary isomorphisms. -/
theorem etaleNormalizationComparison_open
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {g : X' ⟶ X} {h : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e'] [IsOpenImmersion g] [IsOpenImmersion h]
    (sq : IsPullback h e' e g) (c : Compactification e) (d : Compactification e')
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (H : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ H) :
    (∀ K : DerivedCategoryModule A X,
      (etaleNormalizationChi A sq c d G H adj adj').hom.app K =
        (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.map
            ((etaleNormalizationRho A e c G adj).hom.app K) ≫
          (etaleNormalizationBeta A sq).hom.app K ≫
          (etaleNormalizationRho A e' d H adj').inv.app
            ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K)) ∧
    (etaleNormalizationXi A sq c d G H adj adj').hom ≫
        (etaleNormalizationEta A e' d H adj').hom =
      (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.map
          (etaleNormalizationEta A e c G adj).hom ≫
        (etaleSumPullbackUnitIso A h).hom := by
  sorry

/-- Restriction of d under the actual support exchange is d' under sum base change.
Source: support-map compatibility (1); Stacks Tag 03S6
(blueprint: lem-pur-etale-normalization-comparison-coherence).

Proof: for the pulled-back compactification use support-map compatibility (1).
For an arbitrary compactification compose with its common-refinement comparison;
compactification independence and refinement naturality give the same square. -/
theorem etaleNormalizationComparison_open_support
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {g : X' ⟶ X} {h : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e'] [IsOpenImmersion g] [IsOpenImmersion h]
    (sq : IsPullback h e' e g) (c : Compactification e) (d : Compactification e') :
    IsIso (etaleNormalizationExchange A sq c d) ∧
    etaleNormalizationExchange A sq c d ≫
        Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory
          (canonicalEtaleCompactSupportComparison A e' d).hom =
      Functor.whiskerRight (canonicalEtaleCompactSupportComparison A e c).hom
          (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≫
        (etaleNormalizationSumExchange A sq).hom := by
  sorry

/-- The sum evaluation counit restricts to the sum evaluation counit, at every input.
Source: Stacks Tag 03S6 (blueprint: lem-pur-etale-normalization-comparison-coherence).

Proof: expand sum base change as the mate of ordinary exchange. The twofold mate-pasting
law, counit naturality and the triangle identities give this equality on sheaves.
Descend the degreewise equality through homotopy localization to all unbounded inputs. -/
theorem etaleNormalizationComparison_open_counit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {g : X' ⟶ X} {h : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e'] [IsOpenImmersion g] [IsOpenImmersion h]
    (sq : IsPullback h e' e g) (K : DerivedCategoryModule A X) :
    (etaleNormalizationSumExchange A sq).inv.app
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.map
        ((derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e inferInstance).counit.app K) =
    (etaleLowerShriek (ModuleCat.{u + 1} A) e' inferInstance).mapDerivedCategory.map
        ((etaleNormalizationBeta A sq).hom.app K) ≫
      (derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) e' inferInstance).counit.app
          ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K) := by
  sorry

/-- The specified sum projection from support-map compatibility (2). Its inverse is fixed
there to be etaleSupportSumProjectionReverse, so the witness determines this isomorphism
uniquely; no arbitrary tensor comparison is selected.
Source: Stacks Tag 0GKF (blueprint: lem-pur-etale-normalization-comparison-coherence). -/
noncomputable def etaleNormalizationSumProjection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (M : DerivedCategoryModule A U) (K : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj M)).obj
      K ≅
    (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj
      (((derivedTensor (ModuleCat.{u + 1} A) U).obj M).obj
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) :=
  ((Classical.choose (Classical.choose_spec
    (Classical.choose_spec (etaleSupportMapCompatibility A))) e).app M).app K

/-- Restriction of the specified lift-generator projection is the specified projection.
Source: Stacks Tags 03S6 and 0GKF
(blueprint: lem-pur-etale-normalization-comparison-coherence).

Proof: on an etale test object, a lift to U' is a lift to U together with its given map
to X'. Both routes send (s,m) tensor k to (s,m tensor s^*k). This respects restriction,
linearity and balancing, hence gives equal sheaf maps. Use flat-term K-flat representatives
in both variables. Sum extension and pullback preserve these representatives. In each
bidegree both totalized maps preserve the lift and tensor value, without interchanging
factors and hence without an extra sign. Descend their equality through K-flat localization.
This applies to every unbounded input, with no Tor-amplitude or constructibility condition. -/
theorem etaleNormalizationComparison_open_sum_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {g : X' ⟶ X} {h : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e'] [IsOpenImmersion g] [IsOpenImmersion h]
    (sq : IsPullback h e' e g)
    (M : DerivedCategoryModule A U) (K : DerivedCategoryModule A X) :
    ((etaleSupportExactUpperTensorIso A g).hom.app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj M)).app
          K ≫
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.map
        (etaleNormalizationSumProjection A e M K).hom ≫
      (etaleNormalizationSumExchange A sq).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) U).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) ≫
      (etaleLowerShriek (ModuleCat.{u + 1} A) e' inferInstance).mapDerivedCategory.map
        (((etaleSupportExactUpperTensorIso A h).inv.app M).app
            ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫
          derivedTensorHom (ModuleCat.{u + 1} A)
            (𝟙 ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M))
            ((etaleNormalizationBeta A sq).hom.app K)) =
    derivedTensorHom (ModuleCat.{u + 1} A)
        ((etaleNormalizationSumExchange A sq).hom.app M)
        (𝟙 ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K)) ≫
      (etaleNormalizationSumProjection A e'
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M)
        ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K)).hom := by
  sorry

/-- Restriction preserves the actual proper/open projection under the specified exchanges.
Source: support-map compatibility (1),(2); Stacks Tags 03S6 and 0GKF
(blueprint: lem-pur-etale-normalization-comparison-coherence).

Proof: postcompose both restriction routes with d' at their common target. The exchange
square for d and dP = pSigma(d tensor 1) turn the first route into restriction of the
specified sum projection. They turn the second route into pSigma for e'. The preceding
lift-generator calculation identifies the two. Cancel d'. Canonical tensor pullback is
inserted on both sides. This proves equality of the specified transformations, not only
invertibility of their sources and targets. -/
theorem etaleNormalizationComparison_open_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {g : X' ⟶ X} {h : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e'] [IsOpenImmersion g] [IsOpenImmersion h]
    (sq : IsPullback h e' e g) (c : Compactification e) (d : Compactification e')
    (M : DerivedCategoryModule A U) (K : DerivedCategoryModule A X) :
    ((etaleSupportExactUpperTensorIso A g).hom.app
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M)).app K ≫
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.map
        (etaleNormalizationProjection A e c M K) ≫
      (etaleNormalizationExchange A sq c d).app
        (((derivedTensor (ModuleCat.{u + 1} A) U).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
        (((etaleSupportExactUpperTensorIso A h).inv.app M).app
            ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫
          derivedTensorHom (ModuleCat.{u + 1} A)
            (𝟙 ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M))
            ((etaleNormalizationBeta A sq).hom.app K)) =
    derivedTensorHom (ModuleCat.{u + 1} A)
        ((etaleNormalizationExchange A sq c d).app M)
        (𝟙 ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K)) ≫
      etaleNormalizationProjection A e' d
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M)
        ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K) := by
  sorry

/-- An arbitrary normalized tensor family respects compactification comparisons.
Source: blueprint Step 1 (blueprint: lem-pur-etale-normalization-comparison-coherence).

Proof: postcompose both sides with rho' at K. Normalization turns the first into the
right unitor after 1 tensor eta. The second becomes the right unitor after
1 tensor (eta' r_A), equal to the first by refinement normalization. Cancel rho'.
Only the assumed normalization and naturality are used, without a projection transpose
or any purity theorem. -/
theorem etaleNormalizationComparison_tensor_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c d : Compactification e)
    (G H : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ H)
    (v : (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory ⋙
      derivedTensorRight (ModuleCat.{u + 1} A) U (G.obj (constantComplex A X)) ⟶ G)
    (v' : (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory ⋙
      derivedTensorRight (ModuleCat.{u + 1} A) U (H.obj (constantComplex A X)) ⟶ H)
    (hv : ∀ K : DerivedCategoryModule A X,
      v.app K ≫ (etaleNormalizationRho A e c G adj).hom.app K =
        derivedTensorHom (ModuleCat.{u + 1} A)
            (𝟙 ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K))
            (etaleNormalizationEta A e c G adj).hom ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) U
            ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).hom)
    (hv' : ∀ K : DerivedCategoryModule A X,
      v'.app K ≫ (etaleNormalizationRho A e d H adj').hom.app K =
        derivedTensorHom (ModuleCat.{u + 1} A)
            (𝟙 ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K))
            (etaleNormalizationEta A e d H adj').hom ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) U
            ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).hom)
    (K : DerivedCategoryModule A X) :
    v.app K ≫ (etaleNormalizationRefinement A c d G H adj adj').hom.app K =
      derivedTensorHom (ModuleCat.{u + 1} A)
          (𝟙 ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K))
          ((etaleNormalizationRefinement A c d G H adj adj').hom.app (constantComplex A X)) ≫
        v'.app K := by
  obtain ⟨_, hr, hη, _⟩ :=
    etaleNormalizationComparison_refinement A e c d G H adj adj'
  have hrK := NatTrans.congr_app (congrArg Iso.hom hr) K
  have hη' := congrArg Iso.hom hη
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.app_hom] at hrK hη'
  apply (cancel_mono ((etaleNormalizationRho A e d H adj').hom.app K)).1
  rw [Category.assoc, hrK, hv K, Category.assoc, hv' K]
  rw [← Category.assoc, derivedTensorHom_comp]
  rw [Category.id_comp, hη']

/-- An arbitrary normalized tensor family respects Cartesian open restriction.
Source: blueprint Step 1 (blueprint: lem-pur-etale-normalization-comparison-coherence).

Proof: postcompose with rho' at g^*K. The chi formula makes the first route beta after
the pullback of rho v. Normalize v and use pullback/right-unitor compatibility and
unitor naturality to obtain the right unitor after beta tensor (u_h h^*eta).
Normalize v' on the second route; it gives the right unitor after beta tensor (eta' xi).
Unit normalization identifies these coefficient maps. Cancel rho'. No transposition
property of v or purity theorem is used. -/
theorem etaleNormalizationComparison_tensor_open
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {g : X' ⟶ X} {h : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e'] [IsOpenImmersion g] [IsOpenImmersion h]
    (sq : IsPullback h e' e g) (c : Compactification e) (d : Compactification e')
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (H : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ H)
    (v : (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory ⋙
      derivedTensorRight (ModuleCat.{u + 1} A) U (G.obj (constantComplex A X)) ⟶ G)
    (v' : (upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory ⋙
      derivedTensorRight (ModuleCat.{u + 1} A) U' (H.obj (constantComplex A X')) ⟶ H)
    (hv : ∀ K : DerivedCategoryModule A X,
      v.app K ≫ (etaleNormalizationRho A e c G adj).hom.app K =
        derivedTensorHom (ModuleCat.{u + 1} A)
            (𝟙 ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K))
            (etaleNormalizationEta A e c G adj).hom ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) U
            ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).hom)
    (hv' : ∀ K : DerivedCategoryModule A X',
      v'.app K ≫ (etaleNormalizationRho A e' d H adj').hom.app K =
        derivedTensorHom (ModuleCat.{u + 1} A)
            (𝟙 ((upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory.obj K))
            (etaleNormalizationEta A e' d H adj').hom ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) U'
            ((upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory.obj K)).hom)
    (K : DerivedCategoryModule A X) :
    ((etaleSupportExactUpperTensorIso A h).hom.app
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).app
          (G.obj (constantComplex A X)) ≫
      (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.map (v.app K) ≫
      (etaleNormalizationChi A sq c d G H adj adj').hom.app K =
    derivedTensorHom (ModuleCat.{u + 1} A)
        ((etaleNormalizationBeta A sq).hom.app K)
        (etaleNormalizationXi A sq c d G H adj adj').hom ≫
      v'.app ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K) := by
  sorry

/-- Open restriction and compactification comparison commute for chi, xi and support exchange.
Source: blueprint Step 1 (blueprint: lem-pur-etale-normalization-comparison-coherence).

Proof: write chi using rho and beta, and r using rho and rho' inverse. Naturality cancels
the intermediate rho factors in the two routes. At the coefficient unit, naturality at
u_g gives the xi equality. The actual support exchange has the same refinement
naturality by unbounded compact-support comparisons. The d and projection equations
therefore give the same mixed coherence for d and P; the normalized-family equations
give it for v. All comparisons are the specified transformations. -/
theorem etaleNormalizationComparison_open_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {g : X' ⟶ X} {h : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e'] [IsOpenImmersion g] [IsOpenImmersion h]
    (sq : IsPullback h e' e g)
    (c c₁ : Compactification e) (d d₁ : Compactification e')
    (G G₁ : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (H H₁ : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj₁ : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c₁ ⊣ G₁)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ H)
    (adj₁' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d₁ ⊣ H₁) :
    (∀ K : DerivedCategoryModule A X,
      (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.map
          ((etaleNormalizationRefinement A c c₁ G G₁ adj adj₁).hom.app K) ≫
        (etaleNormalizationChi A sq c₁ d₁ G₁ H₁ adj₁ adj₁').hom.app K =
      (etaleNormalizationChi A sq c d G H adj adj').hom.app K ≫
        (etaleNormalizationRefinement A d d₁ H H₁ adj' adj₁').hom.app
          ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K)) ∧
    ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.map
        ((etaleNormalizationRefinement A c c₁ G G₁ adj adj₁).hom.app (constantComplex A X)) ≫
      (etaleNormalizationXi A sq c₁ d₁ G₁ H₁ adj₁ adj₁').hom =
    (etaleNormalizationXi A sq c d G H adj adj').hom ≫
      (etaleNormalizationRefinement A d d₁ H H₁ adj' adj₁').hom.app (constantComplex A X')) ∧
    (∀ M : DerivedCategoryModule A U,
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.map
          ((rightDerivedLowerShriekOfCompactificationIso A c c₁).hom.app M) ≫
        (etaleNormalizationExchange A sq c₁ d₁).app M =
      (etaleNormalizationExchange A sq c d).app M ≫
        (rightDerivedLowerShriekOfCompactificationIso A d d₁).hom.app
          ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M)) := by
  sorry

/-- Further open restrictions compose, with the fixed pullback compositors inserted.
Source: blueprint Step 1; Stacks Tags 03S6 and 0F7L
(blueprint: lem-pur-etale-normalization-comparison-coherence).

Proof: substitute the formula for chi. Naturality cancels the intermediate rho and its
inverse. Associativity of exact pullback composition identifies the remaining beta maps
with beta for the pasted square. The coefficient-unit composition law gives the same
calculation for xi. Actual support exchanges paste by unbounded compact-support
comparisons, and common-refinement factors cancel. On sums the exchange pasting is
restriction to the composite test object, keeping the same lift. The counit and generator
projection equations are thus preserved by a second restriction; d and P inherit this
from their normalization squares. For v, postcompose either iterated transport with the
final rho. Both become the same normalized map, so cancellation proves coherence. -/
theorem etaleNormalizationComparison_open_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' U'' X X' X'' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian U'']
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    {e : U ⟶ X} {e' : U' ⟶ X'} {e'' : U'' ⟶ X''}
    {g : X' ⟶ X} {k : X'' ⟶ X'} {h : U' ⟶ U} {l : U'' ⟶ U'}
    [Etale e] [Etale e'] [Etale e'']
    [IsSeparated e] [IsSeparated e'] [IsSeparated e'']
    [QuasiCompact e] [QuasiCompact e'] [QuasiCompact e'']
    [IsOpenImmersion g] [IsOpenImmersion k] [IsOpenImmersion h] [IsOpenImmersion l]
    (sq₁ : IsPullback h e' e g) (sq₂ : IsPullback l e'' e' k)
    (c : Compactification e) (d : Compactification e') (f : Compactification e'')
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (H : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (J : DerivedCategoryModule A X'' ⥤ DerivedCategoryModule A U'')
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ H)
    (adj'' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) f ⊣ J) :
    (∀ K : DerivedCategoryModule A X,
      (upperStar (ModuleCat.{u + 1} A) l).mapDerivedCategory.map
          ((etaleNormalizationChi A sq₁ c d G H adj adj').hom.app K) ≫
        (etaleNormalizationChi A sq₂ d f H J adj' adj'').hom.app
          ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K) =
      (unboundedEtaleUpperStarCompIso A l h).inv.app (G.obj K) ≫
        (etaleNormalizationChi A (sq₂.paste_horiz sq₁) c f G J adj adj'').hom.app K ≫
        J.map ((unboundedEtaleUpperStarCompIso A k g).hom.app K)) ∧
    ((upperStar (ModuleCat.{u + 1} A) l).mapDerivedCategory.map
        (etaleNormalizationXi A sq₁ c d G H adj adj').hom ≫
      (etaleNormalizationXi A sq₂ d f H J adj' adj'').hom =
    (unboundedEtaleUpperStarCompIso A l h).inv.app (G.obj (constantComplex A X)) ≫
      (etaleNormalizationXi A (sq₂.paste_horiz sq₁) c f G J adj adj'').hom) ∧
    (∀ M : DerivedCategoryModule A U,
      (upperStar (ModuleCat.{u + 1} A) k).mapDerivedCategory.map
          ((etaleNormalizationExchange A sq₁ c d).app M) ≫
        (etaleNormalizationExchange A sq₂ d f).app
          ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M) =
      (unboundedEtaleUpperStarCompIso A k g).inv.app
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ≫
        (etaleNormalizationExchange A (sq₂.paste_horiz sq₁) c f).app M ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) f).map
          ((unboundedEtaleUpperStarCompIso A l h).hom.app M)) ∧
    (∀ M : DerivedCategoryModule A U,
      (upperStar (ModuleCat.{u + 1} A) k).mapDerivedCategory.map
          ((etaleNormalizationSumExchange A sq₁).hom.app M) ≫
        (etaleNormalizationSumExchange A sq₂).hom.app
          ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M) =
      (unboundedEtaleUpperStarCompIso A k g).inv.app
          ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj M) ≫
        (etaleNormalizationSumExchange A (sq₂.paste_horiz sq₁)).hom.app M ≫
        (etaleLowerShriek (ModuleCat.{u + 1} A) e'' inferInstance).mapDerivedCategory.map
          ((unboundedEtaleUpperStarCompIso A l h).hom.app M)) := by
  sorry

/-- On the chosen fibre product the generalized sum comparison is exactly the named
specified sum-exchange map of the dependency.
Source: Stacks Tag 03S6 (blueprint: lem-pur-etale-normalization-comparison-coherence).

Proof: expand the base-change isomorphism as the unique left-adjoint comparison under
ordinary exchange. The inverse-conjugate construction of the named base-change map is
that same unique comparison. Descend this equality termwise and insert the identical
exact-derived composition comparisons. -/
theorem etaleNormalizationComparison_sum_exchange_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X X' : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian X']
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (g : X' ⟶ X) [IsOpenImmersion g] :
    etaleNormalizationSumExchange A (IsPullback.of_hasPullback g e).flip =
      exactEtaleSumExchange A e g := by
  let sq := IsPullback.of_hasPullback g e
  let m := etaleLowerShriekBaseChangeMap A g e
  let : IsIso m := isIso_etaleLowerShriekBaseChangeMap A g e
  have hm : etaleLowerShriekBaseChangeIso A sq = (asIso m).symm := by
    apply Iso.ext_inv
    exact uniq_eq_conjugate _ _ _
  simp only [etaleNormalizationSumExchange, exactEtaleSumExchange]
  rw [hm]

end AlgebraicGeometry.Etale
