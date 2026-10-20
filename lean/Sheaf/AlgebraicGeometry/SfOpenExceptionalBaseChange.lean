/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.SfFiniteOpenExtensionBaseChange
public import Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint
import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
-- Retained as a step of the comparison unit used by the coefficient realization.
import Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections
import Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange

/-!
# Exceptional base change along an arbitrary open immersion

Source: Weil blueprint, order 1815, sk-prop-sf-existence
(blueprint: cor-exc-base-change-open-immersion-general).
The ambient assertion and the independent coefficient-class assertion are separate.
The former uses the given ordinary unbounded adjunctions. The latter uses only the
specified transported etale exceptional functor. No quasi-compactness of the open
immersion is imposed in the ambient assertion.

## Main statements

- `sfAmbientExceptionalOpenBaseChange`: the ordinary ambient comparison and restricted
  FullCD bound, using the supplied adjunction and the base-changed compactification.
- `sfFiniteExceptionalOpenBaseChange`: the independent comparison for degree-zero
  etale-origin sheaves and bounded constructible complexes.

The support and realization comparisons below specify the canonical maps in these statements.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
open Scheme

/-- The exact open extension-by-zero comparison in the two recorded presentations.
It cancels the unit of the specified realization equivalence.
Source: blueprint order 1815 (blueprint: cor-exc-base-change-open-immersion-general). -/
noncomputable def sfIntrinsicOpenExtensionComparison (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (sfIntrinsicModuleEquivalence U A).functor ⋙ sfIntrinsicExtensionByZero j A ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        (sfIntrinsicModuleEquivalence X A).functor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence U A).unitIso.symm _ ≪≫
    Functor.leftUnitor _

/-- Canonical realization of the compact-support candidate, fixed on constant sections
and on K-injective representatives by sfIntrinsicDerivedDirectImageComparison.
Source: blueprint order 1815 (blueprint: cor-exc-base-change-open-immersion-general). -/
noncomputable def sfIntrinsicCompactSupportComparison (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfAmbientCompactSupportCandidate A c ≅
      sfFixedCompactSupport A c ⋙ (sfIntrinsicDerivedEquivalence Y A).functor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (sfIntrinsicOpenExtensionComparison A c.i) ≪≫
        Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sfIntrinsicDerivedDirectImageComparison c.g A) ≪≫
    (Functor.associator _ _ _).symm

/-- The given ambient right adjoint in the canonically equivalent fixed-scalar category.
Source: blueprint order 1815 (blueprint: cor-exc-base-change-open-immersion-general). -/
noncomputable def sfFixedAmbientRightAdjoint (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (D : SfAmbientExceptionalRightAdjointDatum A f c) (d : Compactification f) :=
  (sfIntrinsicDerivedEquivalence Y A).functor ⋙ D.rightAdjoint d ⋙
    (sfIntrinsicDerivedEquivalence X A).inverse

/-- Transport of the actual supplied adjunction, with its units and counits.
Source: blueprint order 1815 (blueprint: cor-exc-base-change-open-immersion-general). -/
noncomputable def sfFixedAmbientAdjunction (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (D : SfAmbientExceptionalRightAdjointDatum A f c) (d : Compactification f) :
    sfFixedCompactSupport A d ⊣ sfFixedAmbientRightAdjoint A D d :=
  (((sfIntrinsicDerivedEquivalence X A).toAdjunction.comp (D.adjunction d)).comp
    (sfIntrinsicDerivedEquivalence Y A).symm.toAdjunction).ofNatIsoLeft
      (Functor.isoWhiskerRight (sfIntrinsicCompactSupportComparison A d) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (sfIntrinsicDerivedEquivalence Y A).unitIso.symm ≪≫
        Functor.rightUnitor _)

/-- The specified compactification support exchange. The first arrow is the proper
ordinary derived direct-image mate, and the second is the inverse extension-by-zero
mate, applied degreewise. This defines a map even before its invertibility is proved.
Source: blueprint order 1815, proof Steps 1-4; Stacks Tags 0F7B and 0F7C
(blueprint: cor-exc-base-change-open-immersion-general). -/
noncomputable def sfFixedCompactSupportExchange (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    sfFixedCompactSupport A c ⋙ sfFixedDerivedPullback A g ⟶
      sfFixedDerivedPullback A g' ⋙ sfFixedCompactSupport A (c.ofIsPullback sq) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (sfFixedDerivedBaseChange A (c.isPullback_g_ofIsPullback sq).flip.toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (sfFixedDerivedOpenExtensionBaseChangeIso A (c.isPullback_i_ofIsPullback sq)).hom _ ≫
    (Functor.associator _ _ _).hom

/-- The actual exceptional comparison: the mate of the inverse specified support
exchange under the transported supplied ambient adjunctions. Its proof parameter only
certifies invertibility of the already defined support exchange; it supplies no map.
Source: blueprint order 1815, proof Step 4
(blueprint: cor-exc-base-change-open-immersion-general). -/
noncomputable def sfAmbientExceptionalOpenComparison (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f)
    (D : SfAmbientExceptionalRightAdjointDatum A f c)
    (D' : SfAmbientExceptionalRightAdjointDatum A f' (c.ofIsPullback sq))
    [hEx : IsIso (sfFixedCompactSupportExchange A sq c)] :
    sfFixedAmbientRightAdjoint A D c ⋙ sfFixedDerivedPullback A g' ⟶
      sfFixedDerivedPullback A g ⋙ sfFixedAmbientRightAdjoint A D' (c.ofIsPullback sq) :=
  mateEquiv (sfFixedAmbientAdjunction A D c)
    (sfFixedAmbientAdjunction A D' (c.ofIsPullback sq))
    (inv (sfFixedCompactSupportExchange A sq c))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem inverseMateIso
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {G : C' ⥤ C} {U : C ⥤ C'} {H : D' ⥤ D} {V : D ⥤ D'}
    {L : C ⥤ D} {L' : C' ⥤ D'}
    (a : G ⊣ U) (b : H ⊣ V) [IsIso a.unit] [IsIso b.unit]
    (δ : TwoSquare U L L' V) [IsIso δ.natTrans] (e : L' ⋙ H ≅ G ⋙ L) :
    IsIso ((mateEquiv a b).symm δ).natTrans := by
  have : H.Full := b.fullyFaithfulLOfIsIsoUnit.full
  have : H.Faithful := b.fullyFaithfulLOfIsIsoUnit.faithful
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have : IsIso (b.counit.app (L.obj (G.obj M))) :=
    b.isIso_counit_app_of_iso (e.app M).symm
  have : IsIso (H.map (L'.map (a.unit.app M))) := inferInstance
  have : IsIso (H.map (δ.natTrans.app (G.obj M))) := inferInstance
  dsimp only [mateEquiv, Equiv.symm, Equiv.coe_fn_mk, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj,
    Functor.comp_map, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  have : IsIso (H.map (𝟙 (L'.obj (U.obj (G.obj M))))) := inferInstance
  have : IsIso (H.map (𝟙 (V.obj (L.obj (G.obj M)))) ) := inferInstance
  have : IsIso (𝟙 (L.obj (G.obj M))) := inferInstance
  infer_instance

private theorem mateIso
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {G : C' ⥤ C} {U : C ⥤ C'} {H : D' ⥤ D} {V : D ⥤ D'}
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : G ⊣ U) (b : H ⊣ V) [IsIso a.unit] [IsIso b.unit]
    (c : L ⊣ R) (d : L' ⊣ R')
    (δ : TwoSquare U L L' V) [IsIso δ.natTrans] (e : L' ⋙ H ≅ G ⋙ L) :
    IsIso (mateEquiv c d δ).natTrans := by
  let γ := (mateEquiv a b).symm δ
  have : IsIso γ.natTrans := inverseMateIso a b δ e
  have he := iterated_mateEquiv_conjugateEquiv a b d c γ
  rw [Equiv.apply_symm_apply] at he
  change (mateEquiv c d δ).natTrans = _ at he
  rw [he]
  infer_instance

private noncomputable def fixedOpenAdj (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⊣
      sfFixedDerivedPullback A j :=
  (openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategoryAdjunction

private theorem fixedOpenUnit (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (fixedOpenAdj A j).unit := by
  exact Adjunction.isIso_mapDerivedCategoryAdjunction_unit _

private theorem fixedBaseChangeIso (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) [IsOpenImmersion g] :
    IsIso (sfFixedDerivedBaseChange A sq.toCommSq) := by
  have : IsOpenImmersion g' := MorphismProperty.of_isPullback sq.flip inferInstance
  have := fixedOpenUnit A g
  have := fixedOpenUnit A g'
  exact mateIso (fixedOpenAdj A g) (fixedOpenAdj A g')
    (upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f').mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (sfFixedPullbackSquareIso A sq.toCommSq).hom)
    (sfFixedDerivedOpenExtensionBaseChangeIso A sq.flip).symm

private noncomputable def derivedOpenComparison (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (sfIntrinsicDerivedEquivalence U A).functor ⋙ sfIntrinsicDerivedOpen A j ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence X A).functor :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (sfIntrinsicOpenExtensionComparison A j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

private noncomputable def realizeSupportIso (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [IsOpenImmersion g'] [IsOpenImmersion g]
    (c : Compactification f) (c' : Compactification f')
    (e : sfIntrinsicDerivedOpen A g' ⋙ sfAmbientCompactSupportCandidate A c ≅
      sfAmbientCompactSupportCandidate A c' ⋙ sfIntrinsicDerivedOpen A g) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g').mapDerivedCategory ⋙
        sfFixedCompactSupport A c ≅
      sfFixedCompactSupport A c' ⋙
        (openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).mapDerivedCategory := by
  let e₁ := Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sfIntrinsicCompactSupportComparison A c).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedOpenComparison A g').symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ e ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sfIntrinsicCompactSupportComparison A c') _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (derivedOpenComparison A g) ≪≫
    (Functor.associator _ _ _).symm
  exact ((Functor.FullyFaithful.ofFullyFaithful
    (sfIntrinsicDerivedEquivalence Y A).functor).whiskeringRight _).preimageIso e₁

private theorem openFullCDFirst (A : Type u) [CommRing A] [Finite A] {X Y U : Scheme.{u}}
    (p : X ⟶ Y) (g : U ⟶ Y) [IsOpenImmersion g] (c : ℕ)
    (hcd : sfFullCohomologicalDimension p A c)
    (F : proEtaleRingModules (pullback p g) (proEtaleConstantRing (pullback p g) A))
    (r : ℤ) (hr : (c : ℤ) < r) :
    IsZero ((DerivedCategory.homologyFunctor _ r).obj
      ((proEtaleConstantDerivedDirectImage (pullback.snd p g) A).obj
        ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  let k := pullback.fst p g
  have : (sfIntrinsicExtensionByZero k A).Full := by
    dsimp only [sfIntrinsicExtensionByZero]
    infer_instance
  have : (sfIntrinsicExtensionByZero k A).Faithful := by
    dsimp only [sfIntrinsicExtensionByZero]
    infer_instance
  let adj := sfIntrinsicOpenAdjunction A k
  let e : proEtaleConstantModulePullback k A
      ((sfIntrinsicExtensionByZero k A).obj F) ≅ F :=
    (openSquarePullbackModel A k).app _ ≪≫ (asIso (adj.unit.app F)).symm
  exact (hcd.2 (ProEt.mk g) ((sfIntrinsicExtensionByZero k A).obj F) r hr).of_iso
    ((DerivedCategory.homologyFunctor _ r).mapIso
      ((proEtaleConstantDerivedDirectImage (pullback.snd p g) A).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso e.symm)))

private noncomputable def directImageIsoSource (A : Type u) [CommRing A] [Finite A]
    {R T V : Scheme.{u}}
    (q : R ⟶ V) (t : T ⟶ V) (e : R ≅ T) (he : e.hom ≫ t = q)
    (F : proEtaleRingModules T (proEtaleConstantRing T A)) :
    (proEtaleConstantDerivedDirectImage q A).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((sfIntrinsicPullback A e.hom).obj F)) ≅
      (proEtaleConstantDerivedDirectImage t A).obj
        ((DerivedCategory.singleFunctor _ 0).obj F) := by
  have sq : IsPullback q e.hom (𝟙 V) t :=
    IsPullback.of_vert_isIso ⟨by simpa using he.symm⟩
  exact ((proEtaleConstantDerivedDirectImage q A).mapIso
      (((sfIntrinsicPullback A e.hom).mapDerivedCategorySingleFunctor 0).symm.app F)) ≪≫
    (sfProperOpenDerivedRestriction A q e.hom (𝟙 V) t sq).symm.app _ ≪≫
    (sfIntrinsicDerivedPullbackId A V).app _

private noncomputable def pullbackExtensionSquare (A : Type u) [CommRing A] [Finite A]
    {R T P X : Scheme.{u}}
    (b : R ⟶ P) (a : T ⟶ X) (k : P ⟶ X) [IsOpenImmersion k]
    (e : R ≅ T) (he : b ≫ k = e.hom ≫ a)
    (F : proEtaleRingModules P (proEtaleConstantRing P A)) :
    (sfIntrinsicPullback A e.hom).obj (proEtaleConstantModulePullback a A
        ((sfIntrinsicExtensionByZero k A).obj F)) ≅
      proEtaleConstantModulePullback b A F := by
  have : (sfIntrinsicExtensionByZero k A).Full := by
    dsimp only [sfIntrinsicExtensionByZero]
    infer_instance
  have : (sfIntrinsicExtensionByZero k A).Faithful := by
    dsimp only [sfIntrinsicExtensionByZero]
    infer_instance
  exact (sfIntrinsicPullback A e.hom).mapIso ((openSquarePullbackModel A a).app _) ≪≫
    (sfIntrinsicSquarePullback A b e.hom k a he).symm.app _ ≪≫
    (sfIntrinsicPullback A b).mapIso
      (asIso ((sfIntrinsicOpenAdjunction A k).unit.app F)).symm ≪≫
    (openSquarePullbackModel A b).symm.app F

private theorem openFullCD (A : Type u) [CommRing A] [Finite A] {X Y U : Scheme.{u}}
    (p : X ⟶ Y) (g : U ⟶ Y) [IsOpenImmersion g] (c : ℕ)
    (hcd : sfFullCohomologicalDimension p A c) :
    sfFullCohomologicalDimension (pullback.snd p g) A c := by
  refine ⟨openFullCDFirst A p g c hcd, ?_⟩
  intro V F r hr
  let p' := pullback.snd p g
  let k := pullback.fst p g
  let b := pullback.fst p' V.hom
  let q := pullback.snd p' V.hom
  let outer := (IsPullback.of_hasPullback p' V.hom).paste_horiz
    (IsPullback.of_hasPullback p g)
  let e := outer.isoPullback
  let a := pullback.fst p (V.hom ≫ g)
  let t := pullback.snd p (V.hom ≫ g)
  let F₀ := (sfIntrinsicExtensionByZero k A).obj F
  let F₁ := proEtaleConstantModulePullback a A F₀
  have hz := hcd.2 (ProEt.mk (V.hom ≫ g)) F₀ r hr
  let z : (proEtaleConstantDerivedDirectImage q A).obj
        ((DerivedCategory.singleFunctor _ 0).obj (proEtaleConstantModulePullback b A F)) ≅
      (proEtaleConstantDerivedDirectImage t A).obj
        ((DerivedCategory.singleFunctor _ 0).obj F₁) :=
    (proEtaleConstantDerivedDirectImage q A).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso
          (pullbackExtensionSquare A b a k e outer.isoPullback_hom_fst.symm F).symm) ≪≫
      directImageIsoSource A q t e outer.isoPullback_hom_snd F₁
  exact hz.of_iso ((DerivedCategory.homologyFunctor _ r).mapIso z)

private theorem unitOnSource (l : ℕ) {T S : Scheme.{u}} (t : T ⟶ S)
    (h : ∀ x : S, IsUnit (l : S.presheaf.stalk x)) :
    ∀ x : T, IsUnit (l : T.presheaf.stalk x) := by
  intro x
  simpa using (h (t x)).map (t.stalkMap x).hom

private theorem intrinsicSupportIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x))
    [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
    (f : X ⟶ Y) [f.IsOver S] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification f)
    (D : SfAmbientExceptionalRightAdjointDatum (Padic.coefficientExtensionRing l E (n + 1)) f c)
    {Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsOpenImmersion g] :
    Nonempty
      (sfIntrinsicDerivedOpen (Padic.coefficientExtensionRing l E (n + 1)) (pullback.fst f g) ⋙
          sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c ≅
        sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1))
          (c.ofIsPullback (IsPullback.of_hasPullback f g)) ⋙
          sfIntrinsicDerivedOpen (Padic.coefficientExtensionRing l E (n + 1)) g) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  obtain ⟨b, hb⟩ := D.fullCD
  let : c.Z.Over Y := ⟨c.g⟩
  have hz : (c.Z ↘ Y) = c.g := rfl
  have : LocallyOfFiniteType (c.Z ↘ Y) := by rw [hz]; infer_instance
  have : QuasiCompact (c.Z ↘ Y) := by rw [hz]; infer_instance
  have : c.g.IsOver Y := by constructor; simp [hz]
  let hY := unitOnSource l (Y ↘ S) hS
  obtain ⟨Dp⟩ :=
    (sfAmbientCompactSupport_preservesCoproducts_and_hasAmbientDatum_of_fullCD.{u, u}
      l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y c.Z Y hY c.g
      (Compactification.ofIsProper c.g) b hb).2
  have hΓ := (sfProperExceptionalOpenBaseChange l E n Y c.Z Y hY c.g
    (Compactification.ofIsProper c.g) Dp g).1
  let Γ := asIso (sfProperOpenDerivedComparison A (pullback.snd c.g g)
    (pullback.fst c.g g) g c.g (IsPullback.of_hasPullback c.g g).flip)
  let c' := c.ofIsPullback (IsPullback.of_hasPullback f g)
  let h := (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f g)).w
  exact ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((sfIntrinsicDerivedOpenComp A (pullback.fst f g) c.i).symm ≪≫
        eqToIso (by congr 1) ≪≫
        sfIntrinsicDerivedOpenComp A c'.i (pullback.fst c.g g)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicDerivedOpen A c'.i) Γ.symm ≪≫
    (Functor.associator _ _ _).symm⟩

/-- Exceptional base change on the whole ordinary derived categories, conditional on
exactly the supplied ambient datum. The existential bound is the same before and after
base change, and the new datum uses the base-changed compactification.
Source: blueprint order 1815, first clause and proof Steps 1-4
(blueprint: cor-exc-base-change-open-immersion-general).
Proof: use the compactification already in D, not Nagata over the arbitrary base S.
The proper part is finite type over S, so lem-sp-fullcd-ambient-adjoint applies to its
identity-open compactification. Pull back the compactification; properness, separatedness
and finite type are stable under base change, with no quasi-compactness requirement on g.
Extend every sheaf on the new proper source by zero. The two clauses of the original
FullCD bound, evaluated on the open base and on each of its weakly-etale objects, give
the identical bound for the new proper part. Apply lem-sp-fullcd-ambient-adjoint there.
Give the closed complement its reduced induced structure and apply the conditional
proper comparison prop-exc-base-change-proper. Finally
cor-exc-base-change-reduces-to-proper identifies its open paste with the displayed mate
and proves that mate invertible. An affine open is an instance of the same open g. -/
theorem sfAmbientExceptionalOpenBaseChange
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (_hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x))
    [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
    (f : X ⟶ Y) [f.IsOver S] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification f)
    (D : SfAmbientExceptionalRightAdjointDatum (Padic.coefficientExtensionRing l E (n + 1)) f c)
    {Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsOpenImmersion g] :
    ∃ c_cd : ℕ,
      sfFullCohomologicalDimension c.g (Padic.coefficientExtensionRing l E (n + 1)) c_cd ∧
      sfFullCohomologicalDimension
        (c.ofIsPullback (IsPullback.of_hasPullback f g)).g
        (Padic.coefficientExtensionRing l E (n + 1)) c_cd ∧
      ∃ D' : SfAmbientExceptionalRightAdjointDatum
          (Padic.coefficientExtensionRing l E (n + 1)) (pullback.snd f g)
          (c.ofIsPullback (IsPullback.of_hasPullback f g)),
        ∃ hEx : IsIso (sfFixedCompactSupportExchange
            (Padic.coefficientExtensionRing l E (n + 1)) (IsPullback.of_hasPullback f g) c),
          IsIso (sfAmbientExceptionalOpenComparison
            (Padic.coefficientExtensionRing l E (n + 1)) (IsPullback.of_hasPullback f g)
            c D D' (hEx := hEx)) := by
  obtain ⟨b, hb⟩ := D.fullCD
  have hb' := openFullCD _ c.g g b hb
  have datum : Nonempty (SfAmbientExceptionalRightAdjointDatum
      (Padic.coefficientExtensionRing l E (n + 1)) (pullback.snd f g)
      (c.ofIsPullback (IsPullback.of_hasPullback f g))) := by
    let f' := pullback.snd f g
    let : (pullback f g).Over Y' := ⟨f'⟩
    have hf' : (pullback f g ↘ Y') = f' := rfl
    have : LocallyOfFiniteType (pullback f g ↘ Y') := by rw [hf']; infer_instance
    have : QuasiCompact (pullback f g ↘ Y') := by rw [hf']; infer_instance
    have : f'.IsOver Y' := by constructor; simp [hf', f']
    exact (sfAmbientCompactSupport_preservesCoproducts_and_hasAmbientDatum_of_fullCD.{u, u}
      l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y' (pullback f g) Y'
      (unitOnSource l (g ≫ (Y ↘ S)) _hS) f'
      (c.ofIsPullback (IsPullback.of_hasPullback f g)) b hb').2
  obtain ⟨D'⟩ := datum
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let sq := IsPullback.of_hasPullback f g
  have : IsIso (sfFixedDerivedBaseChange A (c.isPullback_g_ofIsPullback sq).flip.toCommSq) :=
    fixedBaseChangeIso A (c.isPullback_g_ofIsPullback sq).flip
  have hEx : IsIso (sfFixedCompactSupportExchange A sq c) := by
    unfold sfFixedCompactSupportExchange
    infer_instance
  refine ⟨b, hb, hb', D', hEx, ?_⟩
  obtain ⟨e⟩ := intrinsicSupportIso l E n S X Y _hS f c D g
  have := fixedOpenUnit A g
  have := fixedOpenUnit A (pullback.fst f g)
  exact mateIso (fixedOpenAdj A (pullback.fst f g)) (fixedOpenAdj A g)
    (sfFixedAmbientAdjunction A D c) (sfFixedAmbientAdjunction A D' (c.ofIsPullback sq))
    (TwoSquare.mk _ _ _ _ (inv (sfFixedCompactSupportExchange A sq c)))
    (realizeSupportIso A c (c.ofIsPullback sq) e).symm

/-- The independent finite-coefficient comparison on the two stated input classes.
In particular a degree-zero sheaf need not be finite or constructible. There is no
ambient datum in this assertion. The compactification is arbitrary; its base change
is used on the right, as in the defining finite-level construction.
Source: blueprint order 1815, second clause and proof Steps 5-7
(blueprint: cor-exc-base-change-open-immersion-general).
Proof: finite-type schemes over the algebraic closure of a finite field are Noetherian.
Their open subschemes and the compactification are again finite type, and a finite
bound on the dimension exists. Thus thm-sf-ambient-adjoint-class supplies the relative
Hom bijections on bounded-below etale-origin complexes, independently of any ambient
adjunction. Transport the etale proper/open interchange through the specified proper
comparison and extension-by-zero comparison; its five arrows are all invertible.
Full faithfulness of comparison on D⁺ makes this independent of the etale witness.
Paste the open extensions using the unique comparison of their adjunctions. This gives
the canonical support interchange Θ. For every test M in the full etale-origin class,
transpose successively through g'_! ⊣ g'^*, the relative f adjunction, Θ, g_! ⊣ g^*,
and the relative f' adjunction. This gives a natural bijection
Hom(M,g'^*Rf!K) ≃ Hom(M,Rf'!g^*K). Its action is postcomposition with the displayed
comparison: expand the units and counits to identify it with the mate of the reverse
support exchange. Both endpoints are in this full class. Surjectivity on Hom from the
right endpoint and injectivity on Hom from the left give a two-sided inverse. This
argument applies to every degree-zero etale-origin sheaf and to every bounded
constructible K, which has an etale-origin witness. It uses the entire bounded-below
complex, so no sheaf-only extension or truncation argument is assumed. -/
theorem sfFiniteExceptionalOpenBaseChange
    (Dk : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ Dk.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    (X Y : Scheme.{u}) [X.Over (Spec (CommRingCat.of Dk.k))]
    [Y.Over (Spec (CommRingCat.of Dk.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of Dk.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of Dk.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of Dk.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of Dk.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of Dk.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) {Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsOpenImmersion g]
    (K : DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))))
    (_hK :
      (∃ F : Sheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))),
        (comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
          Y).essImage F ∧
        Nonempty ((DerivedCategory.singleFunctor _ 0).obj F ≅ K)) ∨
      intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y
        ((sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (n + 1))).functor.obj
          K)) :
    IsIso (sfFiniteExceptionalOpenComparison (Padic.coefficientExtensionRing l E (n + 1))
      (IsPullback.of_hasPullback f g) c K) := by
  let := c.hasCompactification
  let := (c.ofIsPullback (IsPullback.of_hasPullback f g)).hasCompactification
  let := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
    (IsPullback.of_hasPullback f g)
  unfold sfFiniteExceptionalOpenComparison
  infer_instance

end AlgebraicGeometry.ProEtale
