/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
import Sheaf.Paper.CartesianCoefficientTwists

/-!
# Mixed factorization comparison for condensed coefficient modules

Transport the normalized locally closed extension comparison through the fixed
internal-module/section-module equivalences. The coefficient identifications agree
with composition because their direct-image adjuncts agree on every section.

Source: blueprint main-20261015, sk-lem-coefficient-heart-filtration, second paragraph
(blueprint: new-det-lem-coefficient-heart-filtration-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj

-- Fix the value universe of the ring sheafification instance before elaborating
-- inverse-image adjunctions; the global instance has an extra maximum universe.
private instance coefficientRingSheafify (X : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, u + 1} X

private theorem compositeAdjunct {A B C : Type (u + 2)}
    [Category.{u + 1} A] [Category.{u + 1} B] [Category.{u + 1} C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : B ⥤ C} {R' : C ⥤ B}
    {L'' : A ⥤ C} {R'' : C ⥤ A}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (adj'' : L'' ⊣ R'')
    (e : R' ⋙ R ≅ R'') (M : A) (N : B) (P : C)
    (c : L.obj M ⟶ N) (d : L'.obj N ⟶ P) :
    adj''.homEquiv M P
        ((((conjugateIsoEquiv (adj.comp adj') adj'').symm e).hom.app M) ≫
          L'.map c ≫ d) =
      adj.homEquiv M N c ≫ R.map (adj'.homEquiv N P d) ≫ e.hom.app P := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have hu := unit_conjugateEquiv_symm (adj.comp adj') adj'' e.hom M
  change _ = adj''.unit.app M ≫ R''.map
    (((conjugateIsoEquiv (adj.comp adj') adj'').symm e).hom.app M) at hu
  rw [← Category.assoc, ← Category.assoc, ← hu]
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← e.hom.naturality]
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp, Category.assoc]
  have hn := congrArg R.map (adj'.unit.naturality c)
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp] at hn
  rw [← Category.assoc (R.map (adj'.unit.app _)) (R.map (R'.map (L'.map c))), ← hn]
  simp only [Category.assoc]
namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
private abbrev coeff (X : Scheme.{u}) :=
  sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) (condensedRingObj Λ X)
private theorem coefficientMap_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    InternalModuleOperations.coefficientMap Λ f =
      (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (Scheme.proEtaleRingDirectImageMap.{u} f (coeff Λ Y) (coeff Λ X)
            (spCoefficientIso.{u} f Λ)) := by
  apply (InternalModuleOperations.coefficientMap_existsUnique Λ f).unique
  · exact (InternalModuleOperations.coefficientMap_existsUnique Λ f).exists.choose_spec
  · intro V r
    have h₂ := (Classical.choose_spec (spCoefficientIso_existsUnique.{u} f Λ)).1 V r
    change ((Scheme.proEtaleRingDirectImageMap f (coeff Λ Y) (coeff Λ X)
      (spCoefficientIso.{u} f Λ)).hom.app V).hom r =
        ((condensedPushforwardHom Λ f).hom.app V).hom r
    exact h₂
private theorem lowerStar_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    InternalModuleOperations.lowerStar Λ f =
      Scheme.proEtaleRingModuleDirectImage f (coeff Λ Y) (coeff Λ X)
        (spCoefficientIso.{u} f Λ) := by
  unfold InternalModuleOperations.lowerStar Scheme.proEtaleRingModuleDirectImage
  congr 1
  exact coefficientMap_eq Λ f
private def coeffScheme (X : Scheme.{u}) [IsNoetherian X] :
    Scheme.LocallyClosedCoefficients.{u} where
  scheme := X
  locallyNoetherian := inferInstance
  compact := inferInstance
  ring := coeff Λ X
private def coeffImmersion {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsImmersion f] :
    Scheme.LocallyClosedCoefficientImmersion (coeffScheme Λ X) (coeffScheme Λ Y) where
  hom := f
  immersion := inferInstance
  coefficient := spCoefficientIso.{u} f Λ
private def ringPullComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    InternalModuleOperations.upperStar Λ f ≅
      Scheme.proEtaleRingModulePullback f (coeff Λ Y) (coeff Λ X)
        (spCoefficientIso.{u} f Λ) :=
  ((InternalModuleOperations.adjunction Λ f).ofNatIsoRight
    (eqToIso (lowerStar_eq Λ f))).leftAdjointUniq
      (Scheme.proEtaleRingModuleAdjunction f _ _ _)
private def ringOpenComparison (E : Scheme.LocallyClosedExtensionData.{u})
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsOpenImmersion f] :
    InternalModuleOperations.extension Λ f ≅ E.extension (coeffImmersion Λ f) :=
  ((InternalModuleOperations.openAdjunction Λ f).ofNatIsoRight
    (ringPullComparison Λ f)).leftAdjointUniq
      (E.openAdjunction (coeffImmersion Λ f) (inferInstance : IsOpenImmersion f))
private theorem sectionRingMap_apply (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {V W : X.ProEtᵒᵖ} (h : V ⟶ W)
    (r : (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R).obj.obj V) :
    (((sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R).obj.map h).hom r) =
      (R.obj.map h).hom r := by
  rfl

private def ringPushComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Scheme.proEtaleSheafDirectImage.{u, u + 2} f CommRingCat.{u + 1} ⋙
      Scheme.proEtaleSheafDirectImage.{u, u + 2} g CommRingCat.{u + 1} ≅
        Scheme.proEtaleSheafDirectImage.{u, u + 2} (f ≫ g) CommRingCat.{u + 1} :=
  Functor.sheafPushforwardContinuousComp'
    (F := Scheme.proEtaleBaseChange g) (G := Scheme.proEtaleBaseChange f)
    (FG := Scheme.proEtaleBaseChange (f ≫ g))
    (eFG := (MorphismProperty.Over.pullbackComp
      (P := @WeaklyEtale) (Q := ⊤) f g).symm) CommRingCat.{u + 1}
      (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

-- Normalize the composite coefficient map before specializing to reconstructed rings.
private theorem compositeRingAdjunct {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (RZ : Sheaf (Scheme.ProEt.topology Z) CommRingCat.{u + 1})
    (RY : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (cg : (Scheme.proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RZ ≅ RY)
    (cf : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX) :
    Scheme.proEtaleRingDirectImageMap (f ≫ g) RZ RX
      (Scheme.proEtaleRingCompositeCoefficients f g RZ RY RX cg cf) =
    Scheme.proEtaleRingDirectImageMap g RZ RY cg ≫
      (Scheme.proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
        (Scheme.proEtaleRingDirectImageMap f RY RX cf) ≫
      (ringPushComp f g).hom.app RX := by
  exact compositeAdjunct.{u}
    (Scheme.proEtaleSheafAdjunction g CommRingCat.{u + 1})
    (Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1})
    (Scheme.proEtaleSheafAdjunction (f ≫ g) CommRingCat.{u + 1})
    (ringPushComp f g) RZ RY RX cg.hom cf.hom

private theorem coeffMap_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.ProEtᵒᵖ) (r : (condensedRingObj Λ Y).obj.obj V) :
    ((Scheme.proEtaleRingDirectImageMap f (coeff Λ Y) (coeff Λ X)
      (spCoefficientIso.{u} f Λ)).hom.app V).hom r =
        ((condensedPushforwardHom Λ f).hom.app V).hom r :=
  (Classical.choose_spec (spCoefficientIso_existsUnique.{u} f Λ)).1 V r

private theorem ringPushComp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) (V : Z.ProEtᵒᵖ) :
    ((ringPushComp f g).hom.app R).hom.app V =
      R.obj.map ((MorphismProperty.Over.pullbackComp f g).hom.app V.unop).op := by
  simp only [ringPushComp, Functor.sheafPushforwardContinuousComp']
  exact Category.id_comp _

-- Keep the section calculation abstract to avoid unfolding reconstructed coefficients.
private theorem pushComposite_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (RX : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (RY : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (RZ : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
    (cf : RY ⟶ (lowerStar Ab.{u + 1} f).obj RX)
    (cg : RZ ⟶ (lowerStar Ab.{u + 1} g).obj RY)
    (V : Z.ProEtᵒᵖ) (r : RZ.obj.obj V) :
    (((cg ≫ (lowerStar Ab.{u + 1} g).map cf ≫
      (lowerStarComp Ab.{u + 1} f g).hom.app RX).hom.app V).hom r) =
    (RX.obj.map ((MorphismProperty.Over.pullbackComp f g).hom.app V.unop).op).hom
      ((cf.hom.app ((Scheme.proEtaleBaseChange g).op.obj V)).hom
        ((cg.hom.app V).hom r)) := by
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStarComp_hom_app_hom_app, lowerStar_map_hom_app', AddCommGrpCat.comp_apply]
  rfl

omit [MonObj Λ] [IsCommMonObj Λ] in
private theorem condensed_comp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (V : Z.ProEtᵒᵖ) (r : (condensedRingObj Λ Z).obj.obj V) :
    ((condensedRingObj Λ X).obj.map
      ((MorphismProperty.Over.pullbackComp f g).hom.app V.unop).op).hom
        (((condensedPushforwardHom Λ f).hom.app
          ((Scheme.proEtaleBaseChange g).op.obj V)).hom
            (((condensedPushforwardHom Λ g).hom.app V).hom r)) =
      ((condensedPushforwardHom Λ (f ≫ g)).hom.app V).hom r := by
  have h := congrArg (fun t : condensedRingObj Λ Z ⟶
      (lowerStar Ab.{u + 1} (f ≫ g)).obj (condensedRingObj Λ X) ↦
        (t.hom.app V).hom r) (condensedPushforwardHom_comp Λ f g)
  exact (h.trans (pushComposite_apply f g (condensedRingObj Λ X)
    (condensedRingObj Λ Y) (condensedRingObj Λ Z)
    (condensedPushforwardHom Λ f) (condensedPushforwardHom Λ g) V r)).symm


private theorem compositeCoeffMap_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (V : Z.ProEtᵒᵖ) (r : (condensedRingObj Λ Z).obj.obj V) :
    ((Scheme.proEtaleRingDirectImageMap (f ≫ g) (coeff Λ Z) (coeff Λ X)
      (Scheme.proEtaleRingCompositeCoefficients f g (coeff Λ Z) (coeff Λ Y) (coeff Λ X)
        (spCoefficientIso.{u} g Λ) (spCoefficientIso.{u} f Λ))).hom.app V).hom r =
      ((condensedPushforwardHom Λ (f ≫ g)).hom.app V).hom r := by
  rw [compositeRingAdjunct]
  change (((ringPushComp f g).hom.app (coeff Λ X)).hom.app V).hom
    (((Scheme.proEtaleRingDirectImageMap f (coeff Λ Y) (coeff Λ X)
      (spCoefficientIso.{u} f Λ)).hom.app ((Scheme.proEtaleBaseChange g).op.obj V)).hom
        (((Scheme.proEtaleRingDirectImageMap g (coeff Λ Z) (coeff Λ Y)
          (spCoefficientIso.{u} g Λ)).hom.app V).hom r)) = _
  rw [coeffMap_apply, coeffMap_apply, ringPushComp_apply]
  exact (sectionRingMap_apply X (condensedRingObj Λ X) _ _).trans
    (condensed_comp_apply Λ f g V r)

private theorem coeff_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Scheme.proEtaleRingCompositeCoefficients.{u} f g (coeff Λ Z) (coeff Λ Y) (coeff Λ X)
      (spCoefficientIso.{u} g Λ) (spCoefficientIso.{u} f Λ) =
        spCoefficientIso.{u} (f ≫ g) Λ := by
  apply (spCoefficientIso_existsUnique.{u} (f ≫ g) Λ).unique
  · exact compositeCoeffMap_apply Λ f g
  · exact (Classical.choose_spec (spCoefficientIso_existsUnique.{u} (f ≫ g) Λ)).1

private theorem noetherianSource {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [IsImmersion f] : IsNoetherian X := by
  have : TopologicalSpace.NoetherianSpace X := f.isEmbedding.isInducing.noetherianSpace
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact {}

private theorem coeffImmersion_congr {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (f g : X ⟶ Y)
    [IsImmersion f] [IsImmersion g] (h : f = g) :
    coeffImmersion Λ f = coeffImmersion Λ g := by
  subst g
  rfl

private theorem coeffImmersion_comp {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion f] [IsImmersion g] :
    (coeffImmersion Λ g).comp (coeffImmersion Λ f) = coeffImmersion Λ (f ≫ g) := by
  unfold coeffImmersion Scheme.LocallyClosedCoefficientImmersion.comp
  congr 1
  exact coeff_comp Λ f g

private def ringLowerComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.lowerStar Λ f ⋙ (InternalModuleOperations.equivalence Λ Y).functor ≅
      (InternalModuleOperations.equivalence Λ X).functor ⋙
        Scheme.proEtaleRingModuleDirectImage f (coeff Λ Y) (coeff Λ X)
          (spCoefficientIso.{u} f Λ) :=
  InternalModuleOperations.lowerComparison Λ f ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (lowerStar_eq Λ f))

private def internalOpenComparison (E : Scheme.LocallyClosedExtensionData.{u})
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsOpenImmersion f] :
    CondensedRing.openImmersionLowerShriek Λ f ⋙
        (InternalModuleOperations.equivalence Λ Y).functor ≅
      (InternalModuleOperations.equivalence Λ X).functor ⋙
        E.extension (coeffImmersion Λ f) :=
  InternalModuleOperations.openComparison Λ f ≪≫
    Functor.isoWhiskerLeft _ (ringOpenComparison Λ E f)

private theorem ringFactorization (E : Scheme.LocallyClosedExtensionData.{u})
    {X : Scheme.{u}} [IsNoetherian X] {S T : Scheme.{u}}
    [IsNoetherian S] [IsNoetherian T]
    (i : S ⟶ T) [IsClosedImmersion i] (v : T ⟶ X) [IsOpenImmersion v]
    (a : S ⟶ X) [IsImmersion a] (hfac : i ≫ v = a) :
    letI : IsNoetherian a.image := noetherianSource a.imageι
    Nonempty ((coeffImmersion Λ i).push ⋙ E.extension (coeffImmersion Λ v) ≅
      E.extension (coeffImmersion Λ a.toImage) ⋙ (coeffImmersion Λ a.imageι).push) := by
  have : IsNoetherian a.image := noetherianSource a.imageι
  let e₁ := (E.closedOpenFactorization (coeffImmersion Λ v) (coeffImmersion Λ i)
    (inferInstance : IsClosedImmersion i) (inferInstance : IsOpenImmersion v)).symm
  let e₂ := E.openClosedFactorization (coeffImmersion Λ a.imageι)
    (coeffImmersion Λ a.toImage)
    (inferInstance : IsClosedImmersion a.imageι) (inferInstance : IsOpenImmersion a.toImage)
  have hh : (coeffImmersion Λ v).comp (coeffImmersion Λ i) =
      (coeffImmersion Λ a.imageι).comp (coeffImmersion Λ a.toImage) := by
    rw [coeffImmersion_comp, coeffImmersion_comp]
    exact coeffImmersion_congr Λ _ _ (hfac.trans a.toImage_imageι.symm)
  exact ⟨e₁ ≪≫ eqToIso (congrArg E.extension hh) ≪≫ e₂⟩
private def internalClosedOpenComparison (E : Scheme.LocallyClosedExtensionData.{u})
    {X : Scheme.{u}} [IsNoetherian X] {S T : Scheme.{u}}
    [IsNoetherian S] [IsNoetherian T]
    (i : S ⟶ T) [IsClosedImmersion i] (v : T ⟶ X) [IsOpenImmersion v] :
    (CondensedRing.lowerStar Λ i ⋙ CondensedRing.openImmersionLowerShriek Λ v) ⋙
        (InternalModuleOperations.equivalence Λ X).functor ≅
      (InternalModuleOperations.equivalence Λ S).functor ⋙
        ((coeffImmersion Λ i).push ⋙ E.extension (coeffImmersion Λ v)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (internalOpenComparison Λ E v) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ringLowerComparison Λ i) _ ≪≫
    Functor.associator _ _ _

private def internalOpenClosedComparison (E : Scheme.LocallyClosedExtensionData.{u})
    {X : Scheme.{u}} [IsNoetherian X] {S T : Scheme.{u}}
    [IsNoetherian S] [IsNoetherian T]
    (j : S ⟶ T) [IsOpenImmersion j] (c : T ⟶ X) [IsClosedImmersion c] :
    (CondensedRing.openImmersionLowerShriek Λ j ⋙ CondensedRing.lowerStar Λ c) ⋙
        (InternalModuleOperations.equivalence Λ X).functor ≅
      (InternalModuleOperations.equivalence Λ S).functor ⋙
        (E.extension (coeffImmersion Λ j) ⋙ (coeffImmersion Λ c).push) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ringLowerComparison Λ c) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (internalOpenComparison Λ E j) _ ≪≫
    Functor.associator _ _ _

/-- Mixed open-closed factorization comparison for condensed modules.

Source: the localization paragraph of `sk-lem-coefficient-heart-filtration`, via
`locallyClosedExtensionCoherence` and the internal/section-module operation comparisons.
Compose the normalized ringed-site factorization isomorphisms, identify coefficient
composites by uniqueness of their direct-image adjuncts, then transport through the
section-module equivalences and cancel the fully faithful target equivalence.
Noetherianity supplies quasi-compactness for the image factorization; empty sources
and zero modules require no additional hypotheses.
(blueprint: new-det-lem-coefficient-heart-filtration-core) -/
theorem coefficientHeart_filtration_core {X : Scheme.{u}} [IsNoetherian X] {S T : Scheme.{u}}
    (i : S ⟶ T) [IsClosedImmersion i] (v : T ⟶ X) [IsOpenImmersion v]
    (a : S ⟶ X) (ha : IsImmersion a) (hfac : i ≫ v = a) :
    letI : IsImmersion a := ha
    letI : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
    Nonempty (CondensedRing.lowerStar Λ i ⋙ CondensedRing.openImmersionLowerShriek Λ v ≅
      CondensedRing.openImmersionLowerShriek Λ a.toImage ⋙
        CondensedRing.lowerStar Λ a.imageι) := by
  have : IsImmersion a := ha
  have : IsNoetherian T := noetherianSource v
  have : IsNoetherian S := noetherianSource a
  have : IsNoetherian a.image := noetherianSource a.imageι
  obtain ⟨E, _, _⟩ := Scheme.locallyClosedExtensionCoherence.{u}
  obtain ⟨e⟩ := ringFactorization Λ E i v a hfac
  exact ⟨Functor.fullyFaithfulCancelRight
    (InternalModuleOperations.equivalence Λ X).functor
    (internalClosedOpenComparison Λ E i v ≪≫ Functor.isoWhiskerLeft _ e ≪≫
      (internalOpenClosedComparison Λ E a.toImage a.imageι).symm)⟩

end AlgebraicGeometry.ProEtale
