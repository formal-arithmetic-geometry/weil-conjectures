/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.AlgebraicGeometry.LerayDegenerateSections
import WeilConjectures.AlgebraicGeometry.RestrictedResolutionCohomology
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.LerayWholeOpenClass

/-! # The cocycle Leray edge on a restricted resolution

Source: Stacks Project, cohomology.tex, Tags 01E4, 01F4 and 01FB.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives
attribute [local irreducible] moduleCohomologyFMap sectionCohomologyTheta
  resolutionSectionClass

set_option backward.defeqAttrib.useBackward true in
private theorem sectionClass_restriction {Y : Scheme.{u}}
    (L : CochainComplex Y.Modules ℕ) (V : Y.Opens) (p : ℕ) :
    let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj
    let A := ((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj L
    let ev := CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}
    let r := (NatTrans.mapHomologicalComplex
      (Functor.whiskerLeft (SheafOfModules.forget Y.ringCatSheaf ⋙ E)
        (ev.map (homOfLE (show V ≤ ⊤ from le_top)).op))
      (ComplexShape.up ℕ)).app L
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map r ≫
      ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op V))).hom ≫
      (E.map (sectionCohomologyTheta L p)).app (op V) =
    ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op ⊤))).hom ≫
      (E.map (sectionCohomologyTheta L p)).app (op ⊤) ≫
      (L.homology p).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op := by
  dsimp only
  let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj
  let A := ((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj L
  let ev := CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}
  let τ := Functor.whiskerLeft E (ev.map (homOfLE (show V ≤ ⊤ from le_top)).op)
  have ht := NatTrans.app_homology τ (A.sc p)
  have hn := (E.map (sectionCohomologyTheta L p)).naturality
    (homOfLE (show V ≤ ⊤ from le_top)).op
  let r := (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft (SheafOfModules.forget Y.ringCatSheaf ⋙ E)
      (ev.map (homOfLE (show V ≤ ⊤ from le_top)).op))
    (ComplexShape.up ℕ)).app L
  have hc :
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map r ≫
        ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op V))).hom =
      ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op ⊤))).hom ≫
        (E.obj (A.homology p)).map (homOfLE (show V ≤ ⊤ from le_top)).op := by
    rw [← cancel_epi ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op ⊤))).inv]
    simp only [Iso.inv_hom_id_assoc]
    have hr : (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u}
        (ComplexShape.up ℕ) p).map r = (A.sc p).mapNatTrans τ := by
      ext <;> rfl
    change _ ≫ ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u}
        (ComplexShape.up ℕ) p).map r) ≫ _ = _
    rw [hr]
    exact ht.symm
  rw [← Category.assoc, hc, Category.assoc]
  exact congrArg
    (fun t ↦ ((A.sc p).mapHomologyIso (E ⋙ ev.obj (op ⊤))).hom ≫ t) hn

set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 800000 in
-- Comparing section complexes unfolds both the scheme and ringed-space interfaces.
private theorem restrictedResolution_sectionClass {Z Y : Scheme.{u}}
    (h : Z ⟶ Y) {G : Z.Modules} (I : InjectiveResolution G)
    (V : Y.Opens) (U : Z.Opens) (e : U = h ⁻¹ᵁ V)
    (R : RestrictedResolutionSections I U) (p : ℕ) :
    let L := ((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    resolutionSectionClass I L ⊤ (Iso.refl _) p ≫
      (L.homology p).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op =
    moduleCohomologyRestriction U G p ≫
      resolutionSectionClass R.resolution L V
        (R.sections ≪≫ eqToIso (congrArg (fun T ↦
          ((RingedSpace.openModuleSections Z.toRingedSpace T).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex) e)) p := by
  subst U
  let L := ((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have hr := restrictedResolution_cohomology I (h ⁻¹ᵁ V) R p
  have hn := sectionClass_restriction L V p
  dsimp only at hn
  unfold resolutionSectionClass
  dsimp only
  simp only [Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.assoc]
  erw [Category.id_comp]
  rw [← hn]
  have hrmap :
      ((NatTrans.mapHomologicalComplex
        (Functor.whiskerLeft (SheafOfModules.forget Z.ringCatSheaf ⋙
          PresheafOfModules.toPresheaf Z.ringCatSheaf.obj)
          ((CategoryTheory.evaluation Z.Opensᵒᵖ AddCommGrpCat.{u}).map
            (homOfLE (show h ⁻¹ᵁ V ≤ ⊤ from le_top)).op))
        (ComplexShape.up ℕ)).app I.cocomplex) =
      ((NatTrans.mapHomologicalComplex
        (Functor.whiskerLeft (SheafOfModules.forget Y.ringCatSheaf ⋙
          PresheafOfModules.toPresheaf Y.ringCatSheaf.obj)
          ((CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).map
            (homOfLE (show V ≤ ⊤ from le_top)).op))
        (ComplexShape.up ℕ)).app L) := by
    ext n
    rfl
  rw [hrmap] at hr
  have hr' := congrArg (fun q ↦ q ≫
    (((((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj L).sc p).mapHomologyIso
        (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
          (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V))).hom ≫
    ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
      (sectionCohomologyTheta L p)).app (op V)) hr
  simpa only [Category.assoc] using hr'.symm

set_option maxHeartbeats 500000 in
-- The naturality square compares the scheme and ringed-space section interfaces.
/-- Restricting a global class and applying the restricted-resolution class map
computes the restriction of its classical Leray edge. This concerns a single morphism,
with no square, derived pullback, top-degree bound or derived adjunction.
Source: Stacks Project, cohomology.tex, Tag 01E4, lemma-describe-higher-direct-images;
Tag 01F4(2), and Tag 01FB, remark-explain-arrow.
(blueprint: lem-weil-pbc-leray-edge-restricted-resolution).

Proof: Compute restriction on cohomology by restrictedResolution_cohomology.
The augmentation equation and the pinned components of R.sections identify its map
on a fixed resolution with ordinary restriction of sections. Naturality of the
homology/evaluation comparison and of sectionCohomologyTheta therefore identifies
the left side with the restriction to V of resolutionSectionClass I at the whole
open, followed by the inverse right-derived resolution comparison.
It remains to identify this whole-open class map with the chosen Leray edge.
Represent any cohomology class by a cycle of the global-sections complex of I.
The adjunction defining sectionCohomologyTheta sends the cycle to its image under
the quotient from cycles to cohomology sheaf: this follows by applying the exact
sheafification functor to the short complex of boundaries and cycles and using
its counit. Global sections preserve the kernel defining cycles, so the section
of the cycle sheaf with the specified image under iCycles is unique. It is therefore
the section z in the cocycle characterization of exists_lerayEdge_isIso_of_vanishing.
The two maps agree on the homology class of every cycle. Homology projection is
surjective, and the resolution comparisons are isomorphisms, so they agree on every
class. Finally naturality of I.isoRightDerivedObj inverse carries restriction through
the comparison. Degree zero, empty opens and zero coefficients use the same argument.
-/
theorem lerayEdge_restrictedResolution {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (I : InjectiveResolution F) (n : ℕ) (V : S.Opens)
    (U : X.Opens) (hU : U = f ⁻¹ᵁ V) (R : RestrictedResolutionSections I U) :
    moduleCohomologyRestriction U F n ≫
      resolutionSectionClass R.resolution
        (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
        V (R.sections ≪≫ eqToIso (congrArg (fun W : X.Opens ↦
          ((RingedSpace.openModuleSections X.toRingedSpace W).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex) hU)) n ≫
      Hom.app (I.isoRightDerivedObj (pushforward f) n).inv V =
    ((Classical.choose (exists_lerayEdge_isIso_of_vanishing f)) n).app F ≫
      ((((pushforward f).rightDerived n).obj F).presheaf.map
        (homOfLE (show V ≤ ⊤ from le_top)).op) := by
  let K : CochainComplex S.Modules ℕ :=
    ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have hr := restrictedResolution_sectionClass f I V U hU R n
  dsimp only at hr
  rw [← Category.assoc, ← hr]
  have hn := (Hom.mapPresheaf (I.isoRightDerivedObj (pushforward f) n).inv).naturality
    (homOfLE (show V ≤ ⊤ from le_top)).op
  change (K.homology n).presheaf.map _ ≫
    Hom.app (I.isoRightDerivedObj (pushforward f) n).inv V =
    Hom.app (I.isoRightDerivedObj (pushforward f) n).inv ⊤ ≫
      ((((pushforward f).rightDerived n).obj F).presheaf.map _) at hn
  rw [Category.assoc, hn, ← Category.assoc, whole_open_leray_edge]

end AlgebraicGeometry.Scheme.Modules
