/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionTriangleAssembly.CartesianCandidateCompositor
public import WeilConjectures.AlgebraicGeometry.CartesianTower.CartesianTowerRestriction
import all WeilConjectures.AlgebraicGeometry.Compact.CompactSupportSiteCoherence
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteSiteTower.FiniteSiteTowerPaste
import all WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSiteCoherence

/-! # The canonical candidate-compositor site square on a Cartesian tower

Source: Stacks Project, Tags 0F7B and 0F7J
(blueprint: lem-sf-cartesian-candidate-site-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.CompactCompositionProjection
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  ProjectionTriangleAssembly.candidateCompositor
open WeilConjectures.CompactSupportFiniteProjection

set_option maxRecDepth 2048
set_option cleanup.letToHave false
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
attribute [local implicit_reducible] coherenceEtaleFunctor coherenceProEtaleFunctor
  coherenceBoundedSiteFunctor coherenceSiteFunctor

private theorem preimageIso_reverse
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B}
    (hF : F.FullyFaithful) {a b : A} (e : F.obj a ≅ F.obj b) :
    (hF.preimageIso e).symm = hF.preimageIso e.symm := rfl

attribute [local irreducible] towerCandidateComparison compactSupportSiteComparison

private theorem candidateComparison_reverse
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) :
    (towerCandidateComparison A c d).symm = towerCandidateComparison A d c := by
  have he : (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c d).symm =
      Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A d c := by
    simp only [Etale.rightDerivedLowerShriekOfCompactificationPlusιIso, Iso.trans_symm,
      Iso.symm_symm_eq, Functor.isoWhiskerRight_symm,
      Etale.rightDerivedLowerShriekOfCompactificationPlusIso_symm, Iso.trans_assoc]
  unfold towerCandidateComparison
  dsimp only
  rw [preimageIso_reverse]
  congr 1
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Functor.isoWhiskerRight_symm,
    he, Iso.trans_assoc]

private theorem candidateCompositor_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (O : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory) :
    letI := cf.hasCompactification
    letI := cg.hasCompactification
    letI := cfg.hasCompactification
    ProjectionTriangleAssembly.candidateCompositor A (f := f) (g := g) cf cg cfg O =
      (finiteSupportCandidateComposition A f g cf cg cfg).hom.app O := by
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  have h := candidateComparison_reverse A
    (HasCompactification.compactification (f ≫ g)) cfg
  unfold ProjectionTriangleAssembly.candidateCompositor finiteSupportCandidateComposition
  exact congrArg
    (fun δ ↦ (finiteSupportCandidateCompositionCore
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y).ι
      (originCompactSupport A f)
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf)
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg)
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cfg)
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
      (towerCandidateComparison A cf (HasCompactification.compactification f))
      (towerCandidateComparison A cg (HasCompactification.compactification g))
      (originCompositionAmbient A f g) δ).hom.app O) h

attribute [local irreducible] coherenceBoundaryComponent coherenceCompositionSource
  coherenceProEtaleCompositor coherenceEtaleCompositorComponent

private theorem boundary_plus (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (E : FiniteSiteTower.DE A X) :
    (coherenceBoundaryComponent A c E).hom =
      DerivedCategory.Plus.ι.map ((compactSupportSiteComparisonPlus A c).hom.app E) ≫
        (rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) c).hom.app ((FiniteSiteTower.N A X).obj E) := by
  simp only [coherenceBoundaryComponent, coherenceEvaluateSquare, coherenceBoundaryIso,
    compactExchangeTransportComparison, compactSupportSiteComparison,
    Functor.mapDerivedCategoryPlusCompatibility,
    Iso.app_hom, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp, Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]

private theorem composition_boundary_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (cf : Compactification f) (cg : Compactification g) (E : FiniteSiteTower.DE A X) :
    (coherenceCompositionSource A cf cg E).hom =
      DerivedCategory.Plus.ι.map
        ((compactSupportSiteComparisonPlus A cg).hom.app
          ((Etale.rightDerivedLowerShriekOfCompactificationPlus
            (ModuleCat.{u + 1} A) cf).obj E) ≫
        (rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} A) cg).map
            ((compactSupportSiteComparisonPlus A cf).hom.app E)) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) cg).hom.app
          ((rightDerivedLowerShriekOfCompactificationPlus
            (ModuleCat.{u + 1} A) cf).obj ((FiniteSiteTower.N A X).obj E)) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
        ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) cf).hom.app ((FiniteSiteTower.N A X).obj E)) := by
  simp only [coherenceCompositionSource, Iso.trans_hom, Functor.mapIso_hom,
    boundary_plus, Functor.map_comp, Category.assoc]
  have hn := (rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) cg).hom.naturality
      ((compactSupportSiteComparisonPlus A cf).hom.app E)
  dsimp only [Functor.comp_map] at hn
  dsimp only [coherenceProEtaleFunctor, coherenceEtaleFunctor] at ⊢
  erw [← reassoc_of% hn]
  rfl

private theorem paste_naturality {D : Type*} [Category D]
    {x y z t z' t' : D} (a : x ⟶ y) (b : y ⟶ t) (c : x ⟶ z)
    (d : z ⟶ t) (k : z ⟶ z') (l : t ⟶ t') (d' : z' ⟶ t')
    (h : a ≫ b = c ≫ d) (hn : k ≫ d' = d ≫ l) :
    a ≫ b ≫ l = c ≫ k ≫ d' := by
  rw [← Category.assoc, h, Category.assoc, ← hn]

private theorem etale_change_refl
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f) :
    coherenceEtaleChangeIso A c c = Iso.refl (coherenceEtaleFunctor A c) := by
  exact Etale.rightDerivedLowerShriekOfCompactificationPlusIso_refl A c

private theorem etale_triangle (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (T : Compactification.Triangle f g) (E : FiniteSiteTower.DE A X) :
    (coherenceEtaleCompositorComponent A T.cf T.cg T.cfg E).hom =
      (towerEtaleIso A T).hom.app E := by
  have h := etale_compositor_tower A T.cf T.cg T.cfg T E
  simp only [etale_change_refl, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at h
  have hc : (coherenceEtaleCompositorComponent A T.cf T.cg T.cfg E).hom =
      (coherenceEtaleCompositor A T.cf T.cg T.cfg).hom.app E := by
    simp only [coherenceEtaleCompositorComponent, coherenceCompositionData,
      coherenceCompositionDataOfChoice, CoherencePastingData.etaleIso,
      coherenceChosenEtaleCompositorComponent, coherenceEvaluateCompositor,
      coherenceEtaleCompositor, coherenceCompositorOfChanges,
      coherenceIsoFour, coherenceFourMap, Functor.mapIso_hom, Iso.app_hom]
    rfl
  exact hc.trans h

private theorem tower_etale_triangle (A : Type (u + 1)) [CommRing A] [Finite A]
    {X V W Y B Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian V] [IsNoetherian W]
    [IsNoetherian Y] [IsNoetherian B] [IsNoetherian Z]
    (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion i]
    [IsProper q] [IsProper p] [IsProper s]
    (sq : IsPullback b q p i) (E : FiniteSiteTower.DE A X) :
    FiniteSiteTower.AE A j b p s i q sq E =
      (Etale.native_bounded_triangle_iso (ModuleCat.{u + 1} A)
        (FiniteSiteTower.towerTriangle j b p s i q sq)).hom.app E := by
  exact tower_etale_normalization A j b p s i q sq E

/-- The site square for the canonical compositor evaluated on a Cartesian tower.
The chosen origin witness is retained on both boundary maps.
The pro-etale arrow is built solely from canonical candidate comparisons and origin
composition; the etale arrow is the independent normalized tower AE. There is no raw
clopen mate or raw triangle alpha in this statement.
Source: Stacks 0F7J--0F7K, compactification independence and compatible triangle
(blueprint: lem-sf-cartesian-candidate-site-square).

Proof: On the three factor compactifications the etale tower normalization identifies
AE with the bounded-below restriction of the unbounded etale compact-support compositor.
Indeed etale_compositor_normalization inserts the two proper/open inclusion
compatibilities, and the canonical etale candidate comparisons identify its source and
target with the chosen compactifications. Expand originCompositionModel and evaluate
originCompositionAmbient along comparisonUpperStarPlusEtaleOrigin using the fully
faithful preimage equation. Evaluate each towerCandidateComparison by the same preimage
equation: it is the canonical etale candidate change conjugated by compactSupportSiteComparison.
Naturality moves the inner candidate change through the outer site boundary; the common
refinement cocycle identifies the two candidate-change paths. Adjacent site comparisons
cancel. The remaining boundary is B for the output and D for the input, followed by the
canonical D+ inclusion comparisons targetInclusion and sourceInclusion. This proves the
square on the comparison image. Paste the naturality squares for the inner candidate
comparison, outer candidate comparison, originCompositionAmbient, and final comparison
along the specified isomorphism e. This moves its source-functor image to the input
boundary and its output-functor image to the output boundary, giving the displayed
square for K. Only the proper factors and the individual factored maps are separated;
no separated structure map or coefficient-ring presentation is needed. Empty opens give
the same zero-object square, and identity factors give the unit normalizations. -/
theorem cartesianCandidateSiteSquare
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X V W Y B Z : Spaces F}
    (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion ((geometry F).map j)] [IsOpenImmersion ((geometry F).map b)]
    [IsOpenImmersion ((geometry F).map i)] [QuasiCompact ((geometry F).map b)]
    [QuasiCompact ((geometry F).map i)]
    [IsProper ((geometry F).map q)] [IsProper ((geometry F).map p)]
    [IsProper ((geometry F).map s)]
    (hb : b ≫ p = q ≫ i)
    (sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left)
    (E : FiniteSiteTower.DE A X.obj.left)
    (K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A)
      X.obj.left).FullSubcategory)
    (e : (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X.obj.left).obj E ≅ K) :
    letI : IsOpenImmersion j.hom.left := ‹IsOpenImmersion ((geometry F).map j)›
    letI : IsOpenImmersion b.hom.left := ‹IsOpenImmersion ((geometry F).map b)›
    letI : IsOpenImmersion i.hom.left := ‹IsOpenImmersion ((geometry F).map i)›
    letI : QuasiCompact b.hom.left := ‹QuasiCompact ((geometry F).map b)›
    letI : QuasiCompact i.hom.left := ‹QuasiCompact ((geometry F).map i)›
    letI : IsProper q.hom.left := ‹IsProper ((geometry F).map q)›
    letI : IsProper p.hom.left := ‹IsProper ((geometry F).map p)›
    letI : IsProper s.hom.left := ‹IsProper ((geometry F).map s)›
    letI : IsOpenImmersion (j ≫ b).hom.left :=
      mappedCompositeOpen (geo := geometry F) j b
    letI : IsProper (p ≫ s).hom.left := mappedCompositeProper (geo := geometry F) p s
    let cf := WeilConjectures.sixFunctorFactorCompactification j q
      ‹IsOpenImmersion ((geometry F).map j)› ‹IsProper ((geometry F).map q)›
      (j ≫ q) rfl
    let cg := WeilConjectures.sixFunctorFactorCompactification i s
      ‹IsOpenImmersion ((geometry F).map i)› ‹IsProper ((geometry F).map s)›
      (i ≫ s) rfl
    let cfg := WeilConjectures.sixFunctorFactorCompactification (j ≫ b) (p ≫ s)
      (mappedCompositeOpen (geo := geometry F) j b)
      (mappedCompositeProper (geo := geometry F) p s) ((j ≫ q) ≫ (i ≫ s)) (by
        simp only [Category.assoc]
        rw [← Category.assoc q i s, ← hb]
        simp only [Category.assoc])
    let C := ProjectionTriangleAssembly.candidateCompositor A cf cg cfg K
    DerivedCategory.Plus.ι.map
        ((FiniteSiteTower.N A Z.obj.left).map
          (FiniteSiteTower.AE A j.hom.left b.hom.left p.hom.left s.hom.left i.hom.left
            q.hom.left sq E)) ≫
      DerivedCategory.Plus.ι.map
        (FiniteSiteTower.B A (j ≫ b).hom.left (p ≫ s).hom.left E) ≫
      (CartesianTower.targetInclusion A (j ≫ b).hom.left (p ≫ s).hom.left
        ((FiniteSiteTower.N A X.obj.left).obj E)).hom ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cfg).map e.hom.hom =
    DerivedCategory.Plus.ι.map
        (FiniteSiteTower.D A j.hom.left s.hom.left i.hom.left q.hom.left E) ≫
      (CartesianTower.sourceInclusion A j.hom.left q.hom.left i.hom.left s.hom.left
        ((FiniteSiteTower.N A X.obj.left).obj E)).hom ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).map
          e.hom.hom) ≫ C := by
  intro cf cg cfg C
  let : IsOpenImmersion j.hom.left := ‹IsOpenImmersion ((geometry F).map j)›
  let : IsOpenImmersion b.hom.left := ‹IsOpenImmersion ((geometry F).map b)›
  let : IsOpenImmersion i.hom.left := ‹IsOpenImmersion ((geometry F).map i)›
  let : QuasiCompact b.hom.left := ‹QuasiCompact ((geometry F).map b)›
  let : QuasiCompact i.hom.left := ‹QuasiCompact ((geometry F).map i)›
  let : IsProper q.hom.left := ‹IsProper ((geometry F).map q)›
  let : IsProper p.hom.left := ‹IsProper ((geometry F).map p)›
  let : IsProper s.hom.left := ‹IsProper ((geometry F).map s)›
  let : IsOpenImmersion (j ≫ b).hom.left :=
    mappedCompositeOpen (geo := geometry F) j b
  let : IsProper (p ≫ s).hom.left := mappedCompositeProper (geo := geometry F) p s
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  let f := (j ≫ q).hom.left
  let g := (i ≫ s).hom.left
  let τ := finiteSupportCandidateComposition A f g cf cg cfg
  have hEval := finiteSupportCandidateComposition_etale A f g cf cg cfg E
  have hcoh := composition_site_square A cf cg cfg E
  have hAE := tower_etale_triangle A j.hom.left b.hom.left q.hom.left p.hom.left
    i.hom.left s.hom.left sq E
  have hEc := etale_triangle A
    (FiniteSiteTower.towerTriangle j.hom.left b.hom.left p.hom.left s.hom.left
      i.hom.left q.hom.left sq) E
  have hAEE : FiniteSiteTower.AE A j.hom.left b.hom.left p.hom.left s.hom.left
      i.hom.left q.hom.left sq E =
      (coherenceEtaleCompositorComponent A cf cg cfg E).hom := hAE.trans hEc.symm
  rw [← hAEE, ← hEval] at hcoh
  rw [boundary_plus] at hcoh
  have hout : DerivedCategory.Plus.ι.map
      ((compactSupportSiteComparisonPlus A cfg).hom.app E) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) cfg).hom.app ((FiniteSiteTower.N A X.obj.left).obj E) =
      DerivedCategory.Plus.ι.map
        (FiniteSiteTower.B A (j ≫ b).hom.left (p ≫ s).hom.left E) ≫
      (CartesianTower.targetInclusion A (j ≫ b).hom.left (p ≫ s).hom.left
        ((FiniteSiteTower.N A X.obj.left).obj E)).hom := by
    simp only [compactSupportSiteComparisonPlus,
      rightDerivedLowerShriekOfCompactificationPlusCompatibility,
      CartesianTower.targetInclusion, Iso.app_hom, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, asIso_hom, FiniteSiteTower.B]
    rfl
  have hin : (coherenceCompositionSource A cf cg E).hom =
      DerivedCategory.Plus.ι.map
        (FiniteSiteTower.D A j.hom.left s.hom.left i.hom.left q.hom.left E) ≫
      (CartesianTower.sourceInclusion A j.hom.left q.hom.left i.hom.left s.hom.left
        ((FiniteSiteTower.N A X.obj.left).obj E)).hom := by
    rw [composition_boundary_plus]
    simp only [compactSupportSiteComparisonPlus,
      rightDerivedLowerShriekOfCompactificationPlusCompatibility,
      CartesianTower.sourceInclusion, Iso.app_hom, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, asIso_hom, FiniteSiteTower.D, FiniteSiteTower.B,
      Functor.map_comp, Category.assoc, Functor.comp_map]
    rfl
  rw [hin] at hcoh
  have hn := τ.hom.naturality e.hom
  have hc := candidateCompositor_eq A f g cf cg cfg K
  change C = τ.hom.app K at hc
  change _ ≫ τ.hom.app K = τ.hom.app _ ≫ _ at hn
  dsimp only [coherenceBoundedSiteFunctor, coherenceSiteFunctor] at hcoh
  change DerivedCategory.Plus.ι.map ((FiniteSiteTower.N A Z.obj.left).map
    (FiniteSiteTower.AE A j.hom.left b.hom.left p.hom.left s.hom.left
      i.hom.left q.hom.left sq E)) ≫ _ = _ at hcoh
  have hcoh' : DerivedCategory.Plus.ι.map ((FiniteSiteTower.N A Z.obj.left).map
      (FiniteSiteTower.AE A j.hom.left b.hom.left p.hom.left s.hom.left
        i.hom.left q.hom.left sq E)) ≫
      (DerivedCategory.Plus.ι.map
        (FiniteSiteTower.B A (j ≫ b).hom.left (p ≫ s).hom.left E) ≫
        (CartesianTower.targetInclusion A (j ≫ b).hom.left (p ≫ s).hom.left
          ((FiniteSiteTower.N A X.obj.left).obj E)).hom) =
      (DerivedCategory.Plus.ι.map
        (FiniteSiteTower.D A j.hom.left s.hom.left i.hom.left q.hom.left E) ≫
        (CartesianTower.sourceInclusion A j.hom.left q.hom.left i.hom.left s.hom.left
          ((FiniteSiteTower.N A X.obj.left).obj E)).hom) ≫
        τ.hom.app ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A)
          X.obj.left).obj E) := by
    exact (congrArg (fun z ↦ DerivedCategory.Plus.ι.map
      ((FiniteSiteTower.N A Z.obj.left).map
        (FiniteSiteTower.AE A j.hom.left b.hom.left p.hom.left s.hom.left
          i.hom.left q.hom.left sq E)) ≫ z) hout.symm).trans hcoh
  have hn' : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).map
        e.hom.hom) ≫ τ.hom.app K =
      τ.hom.app ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A)
        X.obj.left).obj E) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cfg).map
        e.hom.hom := hn
  rw [hc]
  have hp := paste_naturality _ _ _ _ _ _ _ hcoh' hn'
  simpa only [Category.assoc] using hp

end AlgebraicGeometry.ProEtale
