/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.SecSmoothPurity.ReductionDirectImage
public import Sheaf.Paper.ComparisonPullbackExact
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.Paper.EtaleProEtaleAdjunctionTransfer
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.Paper.ProperOpenCoefficientRefinement
import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.Paper.EtaleCompactScalarCoherence
public import Sheaf.Paper.EtaleProEtaleCoefficientTransport

/-! # Etale/pro-etale coefficient compatibility

Source: Stacks Project, Tags 0GL6 and 0F7J; the Charts and Locality paragraphs of
main-20261015 `det-sp-reduction-exceptional`
(blueprint: lem-sp-et-proet-coefficient-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility


/-- The etale coefficient map is the proper counit mate followed by the canonical
open tensor identification. Source: Stacks 0GL6 and blueprint Charts paragraph
(blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def etaleCoefficientMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : Etale.DerivedCategoryModule A X) :
    (Etale.scalarExtension φ Y).obj
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K) ⟶
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((Etale.scalarExtension φ X).obj K) :=
  (Etale.scalarMate φ c.g).app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K) ≫
    (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} B) c.g).map
      (Etale.properOpenCoefficientOpenIso φ c.i K).hom

/-- The pro-etale coefficient arrow is the genuine fixed-module transport of the
recorded intrinsic reductionDirectImageComparison, using its normalized realization,
scalar and compact-support presentation comparisons.
Source: Stacks 0GL6 and blueprint Charts paragraph
(blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def proEtaleCoefficientMap
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c ⋙ liftedScalarExtension φ Y ⟶
      liftedScalarExtension φ X ⋙ rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c :=
  transportedRecordedReductionDirectImageComparison φ c
    (reductionDirectImageComparison φ c.i c.g)

/-- Summandwise coefficient extension for the exact etale sum functor. It is the
left-adjoint comparison whose right-adjoint comparison is restriction of scalars
commuting with inverse image. On K-flat representatives it preserves each sheet summand.
Source: Stacks 03S6 and 0GL6; blueprint Charts paragraph
(blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def sumCoefficientIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (e : X ⟶ Y) [Etale e] :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        Etale.scalarExtension φ Y ≅
      Etale.scalarExtension φ X ⋙
        (Etale.etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory :=
  ((conjugateIsoEquiv
    ((Etale.etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryAdjunction.comp
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars.{u} Y.smallEtaleTopology φ)))
    ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars.{u} X.smallEtaleTopology φ)).comp
      (Etale.etaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategoryAdjunction)).symm
    (Functor.mapDerivedCategorySquareIso
      (Etale.upperStarRestrictScalarsIsoSheaf φ e))).symm


/-- The canonical compactification change on an etale-origin pro-etale input, using
exactly the specified compact-support site comparison on its two boundaries.
Source: Stacks 0F7I; blueprint normalized site/refinement square
(blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def siteRefinement (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (compactSupportSiteComparison A c).app L ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.mapIso
      ((Etale.rightDerivedLowerShriekOfCompactificationIso A c d).app L.obj) ≪≫
    ((compactSupportSiteComparison A d).app L).symm

/-- The etale compositor on precisely the three supplied compactifications. The factors
are the existing canonical compactification changes and the proper/open compositor.
Source: Stacks 0F7J; blueprint composition square
(blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def etaleCompositor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g)) :=
  letI := c.hasCompactification
  letI := d.hasCompactification
  letI := e.hasCompactification
  Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekIso A c)
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d) ≪≫
    Functor.isoWhiskerLeft (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
      (Etale.rightDerivedLowerShriekIso A d) ≪≫
    Etale.unboundedEtaleLowerShriekCompIso A f g ≪≫
    (Etale.rightDerivedLowerShriekIso A e).symm

/-- The source boundary for composition: apply the two actual site comparisons,
inserting the canonical bounded-below inclusion comparison at the intermediate object.
Source: Stacks 0F7J and 099R; blueprint site/composition square
(blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def compositionSiteBoundary (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (c : Compactification f) (d : Compactification g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).mapIso
      ((compactSupportSiteComparison A c).app L) ≪≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).mapIso
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.mapIso
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) c).app L).symm) ≪≫
    (compactSupportSiteComparison A d).app
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj L) ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.mapIso
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).mapIso
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) c).app L))

/-- The pro-etale compositor on etale-origin inputs, transported through the specified
site comparisons. Source: Stacks 0F7J; blueprint site/composition square
(blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def siteCompositor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  compositionSiteBoundary A c d L ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.mapIso
      ((etaleCompositor A c d e).app L.obj) ≪≫
    ((compactSupportSiteComparison A e).app L).symm


attribute [local irreducible] etaleCoefficientMap etaleCompositor
  siteRefinement siteCompositor compositionSiteBoundary proEtaleCoefficientMap
  scalarPresentation supportPresentation transportedRecordedReductionDirectImageComparison
  compactSupportSiteComparison pbcComparisonReduction pbcFixedScalarExtension

/-- The canonical site/coefficient square, including the invertibility of its two
coefficient arrows. The existential is only a lower-bound proof for the actual scalar
extension; it does not choose a complex or a comparison map.
Source: Stacks 0GL6, 099R; blueprint Charts/Locality, Steps 1--4
(blueprint: lem-sp-et-proet-coefficient-compatibility).

Proof: Step 1 represents L by a bounded flat constructible complex. Its finite stupid
filtration proves K-flatness; coefficient extension and exact site comparison are computed
termwise without a Tor-dimension assumption on B/A. Step 2 identifies open extension tensor
and site comparisons on each summand. Step 3 uses the normalized proper counit transposes
and lem-weil-pbc-mate-pasting to identify the two proper scalar/site pastings. In Step 4
paste the proper and open squares to obtain precisely the displayed equality. Apply
det-sp-reduction-direct-image to the etale-origin pro-etale input; both endpoints remain
bounded constructible of finite Tor amplitude. Its coefficient arrow is invertible.
The finite-ring origin theorem and bounded-below full faithfulness of
thm-weil-pbc-site-comparison reflect invertibility of the etale coefficient arrow.
The bounded flat representative proves the required lower bound on the actual L_B. -/
theorem etaleProEtaleCoefficientCompatibility
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (_hL : AdjunctionTransfer.etaleProperty (ULift.{u + 1, u} A) X L.obj) :
    ∃ hLB : DerivedCategory.TStructure.t.plus ((Etale.scalarExtension (uliftRingHom φ) X).obj
      L.obj),
      IsIso (etaleCoefficientMap (uliftRingHom φ) c L.obj) ∧
      IsIso ((proEtaleCoefficientMap φ c).app
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj
          L.obj)) ∧
      (@pbcFixedScalarExtension.{u} Y.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology Y)
          (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance (uliftRingHom
            φ)).map
          ((compactSupportSiteComparison (ULift.{u + 1, u} A) c).inv.app L) ≫
        (proEtaleCoefficientMap φ c).app
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            X).mapDerivedCategory.obj L.obj) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).map
          ((pbcComparisonReduction.{u} X (uliftRingHom φ)).hom.app L.obj) =
      (pbcComparisonReduction.{u} Y (uliftRingHom φ)).hom.app
          ((Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) Y).mapDerivedCategory.map
          (etaleCoefficientMap (uliftRingHom φ) c L.obj) ≫
        (compactSupportSiteComparison (ULift.{u + 1, u} B) c).inv.app
          ⟨(Etale.scalarExtension (uliftRingHom φ) X).obj L.obj, hLB⟩ := by
  sorry

set_option backward.isDefEq.respectTransparency false in
private theorem etaleCoefficientMap_eq_compactScalarMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : Etale.DerivedCategoryModule A X) :
    etaleCoefficientMap φ c L = (Etale.compactScalarMap φ c).app L := by
  have hi : ((Etale.ExceptionalCoefficients.openIso φ c.i).app L).inv =
      (Etale.properOpenCoefficientOpenIso φ c.i L).inv :=
    Etale.compactScalarOpen_normalization φ c.i L
  have he := Iso.ext_inv hi
  unfold etaleCoefficientMap Etale.compactScalarMap Etale.ExceptionalCoefficients.compactSupportMap
  rw [← he]
  rfl

private theorem coefficientRefinementTransport
    {C : Type*} [Category C] {Uc Vc Ud Vd Wc Wd Pc Pd Qc Qd : C}
    (ec : Uc ≅ Vc) (ed : Ud ≅ Vd) (cc : Wc ≅ Qc) (cd : Wd ≅ Qd)
    {rc : Vc ⟶ Wc} {rd : Vd ⟶ Wd} {δc : Uc ⟶ Pc} {δd : Ud ⟶ Pd}
    {βc : Pc ⟶ Qc} {βd : Pd ⟶ Qd} {t : Uc ⟶ Ud} {t' : Pc ⟶ Pd} {s : Qc ⟶ Qd}
    (hc : ec.hom ≫ rc = δc ≫ βc ≫ cc.inv)
    (hd : ed.hom ≫ rd = δd ≫ βd ≫ cd.inv)
    (hn : t ≫ δd = δc ≫ t') (hb : t' ≫ βd = βc ≫ s) :
    (ec.inv ≫ t ≫ ed.hom) ≫ rd = rc ≫ cc.hom ≫ s ≫ cd.inv := by
  apply (cancel_epi ec.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hd, reassoc_of% hc, reassoc_of% hn, reassoc_of% hb]
  simp only [Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Coefficients commute with the canonical compactification change, including a change
through any common refinement, on both sites. The final delta factors express the
pro-etale identity at the retained etale origin of the actual scalar-extended object.
Source: Stacks 0F7I and 0GL6; blueprint Steps 5--7
(blueprint: lem-sp-et-proet-coefficient-compatibility).

Proof: Step 5 pastes the proper counit mates and open tensor units under composition.
Step 6 uses lem-sp-refinement-coefficient-mate for the noncartesian refinement arrow;
its three-constituent theta is the specified canonical refinement. Step 7 applies proper
pushforward and its compositor, then cancels the inverse comparison to give either
orientation. For any common refinement substitute its two squares and cancel their
invertible factors. The canonical cocycle of lem-amb-etale-compact-comparisons proves
independence of that choice. Apply the same site-mate pasting to obtain the pro-etale
square through the specified c; delta only changes the retained scalar-extension origin. -/
theorem etaleProEtaleCoefficientCompatibility_refinement
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (_hL : AdjunctionTransfer.etaleProperty (ULift.{u + 1, u} A) X L.obj) :
    ∃ hLB : DerivedCategory.TStructure.t.plus ((Etale.scalarExtension (uliftRingHom φ) X).obj
      L.obj),
      ((Etale.scalarExtension (uliftRingHom φ) Y).map
          ((Etale.rightDerivedLowerShriekOfCompactificationIso (ULift.{u + 1, u} A) c d).hom.app
            L.obj) ≫
        etaleCoefficientMap (uliftRingHom φ) d L.obj =
      etaleCoefficientMap (uliftRingHom φ) c L.obj ≫
        (Etale.rightDerivedLowerShriekOfCompactificationIso (ULift.{u + 1, u} B) c d).hom.app
          ((Etale.scalarExtension (uliftRingHom φ) X).obj L.obj)) ∧
      ((@pbcFixedScalarExtension.{u} Y.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology Y)
          (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance (uliftRingHom
            φ)).map
          (siteRefinement (ULift.{u + 1, u} A) c d L).hom ≫
        (proEtaleCoefficientMap φ d).app
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            X).mapDerivedCategory.obj L.obj) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) d).map
          ((pbcComparisonReduction.{u} X (uliftRingHom φ)).hom.app L.obj) =
      (proEtaleCoefficientMap φ c).app
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            X).mapDerivedCategory.obj L.obj) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).map
          ((pbcComparisonReduction.{u} X (uliftRingHom φ)).hom.app L.obj) ≫
        (siteRefinement (ULift.{u + 1, u} B) c d ⟨(Etale.scalarExtension (uliftRingHom φ) X).obj
          L.obj, hLB⟩).hom)  := by
  obtain ⟨hLB, _, _, hc⟩ := etaleProEtaleCoefficientCompatibility
    ell p _hp _hEll k _hA _hB φ f c L _hL
  obtain ⟨_, _, _, hd⟩ := etaleProEtaleCoefficientCompatibility
    ell p _hp _hEll k _hA _hB φ f d L _hL
  let LB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :=
    ⟨(Etale.scalarExtension (uliftRingHom φ) X).obj L.obj, hLB⟩
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  let : IsNoetherian Y := ⟨⟩
  have he := (Etale.etaleCompactScalarCoherence (uliftRingHom φ) f c).2.2 d L
    ⟨LB, rfl⟩
  simp only [← etaleCoefficientMap_eq_compactScalarMap] at he
  refine ⟨hLB, he, ?_⟩
  have hn := (pbcComparisonReduction.{u} Y (uliftRingHom φ)).hom.naturality
    ((Etale.rightDerivedLowerShriekOfCompactificationIso (ULift.{u + 1, u} A) c d).hom.app
      L.obj)
  dsimp only [Functor.comp_map] at hn
  have hb := congrArg
    ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) Y).mapDerivedCategory.map) he
  simp only [Functor.map_comp] at hb
  have ht := coefficientRefinementTransport
    ((liftedScalarExtension φ Y).mapIso
      ((compactSupportSiteComparison (ULift.{u + 1, u} A) c).app L).symm)
    ((liftedScalarExtension φ Y).mapIso
      ((compactSupportSiteComparison (ULift.{u + 1, u} A) d).app L).symm)
    ((compactSupportSiteComparison (ULift.{u + 1, u} B) c).app LB)
    ((compactSupportSiteComparison (ULift.{u + 1, u} B) d).app LB) hc hd hn hb
  simp only [siteRefinement, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc] at ht ⊢
  convert ht using 1 <;> rfl


set_option backward.isDefEq.respectTransparency false in
private theorem etaleProperty_iff_constructibleFiniteTor
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (L : Etale.DerivedCategoryModule A X) :
    AdjunctionTransfer.etaleProperty A X L ↔
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X L := by
  constructor
  · rintro ⟨⟨hc, a, b, hab, hv⟩, ht⟩
    refine ⟨⟨?_, ?_⟩, ht⟩
    · exact ⟨⟨a, (DerivedCategory.isGE_iff L a).2
          (fun i hi ↦ hv i (Or.inl hi))⟩,
        ⟨b, (DerivedCategory.isLE_iff L b).2 (fun i hi ↦ hv i (Or.inr hi))⟩⟩
    · exact fun i ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)
  · rintro ⟨⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩, ht⟩
    refine ⟨⟨?_, min a b, max a b, min_le_max, ?_⟩, ht⟩
    · exact fun i ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i)
    · intro i hi
      rcases hi with hi | hi
      · exact (DerivedCategory.isGE_iff L a).1 ha i (lt_of_lt_of_le hi (min_le_left _ _))
      · exact (DerivedCategory.isLE_iff L b).1 hb i (lt_of_le_of_lt (le_max_right _ _) hi)
set_option backward.isDefEq.respectTransparency false in
private theorem compactSupport_preserves_etaleProperty
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent A Y]
    {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f)
    (L : Etale.DerivedCategoryModule A X) (hL : AdjunctionTransfer.etaleProperty A X L) :
    AdjunctionTransfer.etaleProperty A Y
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj L) := by
  let := c.hasCompactification
  apply (etaleProperty_iff_constructibleFiniteTor A Y _).2
  have h := Etale.constructibleFiniteTor_rightDerivedLowerShriek A aY f
    ((etaleProperty_iff_constructibleFiniteTor A X L).1 hL)
  let e := ((Etale.rightDerivedLowerShriekIso A c).app L).symm
  exact ⟨(Etale.DerivedCategory.boundedConstructible
    (ModuleCat.{u + 1} A) Y).prop_of_iso e h.1,
    (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e h.2⟩
set_option backward.isDefEq.respectTransparency false in
private theorem coefficient_hasInvertibleExponent
    (A : Type (u + 1)) [CommRing A]
    (ell p : ℕ) [Fact ell.Prime] (hne : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    {T : Scheme.{u}} (a : T ⟶ Spec (.of k)) : HasInvertibleExponent A T := by
  obtain ⟨n, hn⟩ := hA
  have hzero : ((ell ^ n : ℕ) : A) = 0 := by
    simpa only [nsmul_eq_mul, mul_one] using hn 1
  have hu : IsUnit (ell : k) :=
    (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ell.Prime) hne).isUnit
  have hv : IsUnit (((ell ^ n : ℕ) : Γ(Spec (.of k), ⊤))) := by
    simpa only [Nat.cast_pow, map_pow, map_natCast] using
      (hu.pow n).map (Scheme.ΓSpecIso (.of k)).inv.hom
  let : HasInvertibleExponent A (Spec (.of k)) :=
    ⟨ell ^ n, pow_pos (Fact.out : ell.Prime).pos n, hzero, hv⟩
  exact HasInvertibleExponent.of_hom a


private theorem siteCompositionTransport
    {YA YB ZA ZB YPA YPB ZPA ZPB : Type*}
    [Category YA] [Category YB] [Category ZA] [Category ZB]
    [Category YPA] [Category YPB] [Category ZPA] [Category ZPB]
    {QY : YA ⥤ YB} {QZ : ZA ⥤ ZB} {PY : YPA ⥤ YPB} {PZ : ZPA ⥤ ZPB}
    {NYA : YA ⥤ YPA} {NYB : YB ⥤ YPB} {NZA : ZA ⥤ ZPA} {NZB : ZB ⥤ ZPB}
    {Fd : YA ⥤ ZA} {FdB : YB ⥤ ZB} {Pd : YPA ⥤ ZPA} {PdB : YPB ⥤ ZPB}
    (δY : NYA ⋙ PY ≅ QY ⋙ NYB) (δZ : NZA ⋙ PZ ≅ QZ ⋙ NZB)
    (bd : Fd ⋙ QZ ⟶ QY ⋙ FdB) (bpd : Pd ⋙ PZ ⟶ PY ⋙ PdB)
    {M : YA} {MB : YB} {V : YPA} {VB : YPB} {W : ZA} {WB : ZB}
    {WE : ZPA} {WEB : ZPB}
    (cA : V ≅ NYA.obj M) (cB : VB ≅ NYB.obj MB)
    (dA : Pd.obj (NYA.obj M) ≅ NZA.obj (Fd.obj M))
    (dQ : PdB.obj (NYB.obj (QY.obj M)) ≅ NZB.obj (FdB.obj (QY.obj M)))
    (dB : PdB.obj (NYB.obj MB) ≅ NZB.obj (FdB.obj MB))
    (eA : WE ≅ NZA.obj W) (eB : WEB ≅ NZB.obj WB)
    (tA : Fd.obj M ≅ W) (tB : FdB.obj MB ≅ WB)
    (βc : QY.obj M ⟶ MB) (βe : QZ.obj W ⟶ WB)
    (bc : PY.obj V ⟶ VB) (be : PZ.obj WE ⟶ WEB)
    (hc : PY.map cA.inv ≫ bc = δY.hom.app M ≫ NYB.map βc ≫ cB.inv)
    (hd : PZ.map dA.inv ≫ bpd.app (NYA.obj M) ≫ PdB.map (δY.hom.app M) =
      δZ.hom.app (Fd.obj M) ≫ NZB.map (bd.app M) ≫ dQ.inv)
    (he : PZ.map eA.inv ≫ be = δZ.hom.app W ≫ NZB.map βe ≫ eB.inv)
    (hn : PdB.map (NYB.map βc) ≫ dB.hom = dQ.hom ≫ NZB.map (FdB.map βc))
    (hcomp : QZ.map tA.hom ≫ βe = bd.app M ≫ FdB.map βc ≫ tB.hom) :
    PZ.map (Pd.map cA.hom ≫ dA.hom ≫ NZA.map tA.hom ≫ eA.inv) ≫ be =
      bpd.app V ≫ PdB.map bc ≫ PdB.map cB.hom ≫ dB.hom ≫
        NZB.map tB.hom ≫ eB.inv := by
  have hc' : bc ≫ cB.hom = PY.map cA.hom ≫ δY.hom.app M ≫ NYB.map βc := by
    apply (cancel_epi (PY.map cA.inv)).mp
    simp only [← PY.map_comp_assoc, Iso.inv_hom_id, PY.map_id, Category.id_comp]
    rw [reassoc_of% hc]
    simp
  have hd' : bpd.app (NYA.obj M) ≫ PdB.map (δY.hom.app M) ≫ dQ.hom =
      PZ.map dA.hom ≫ δZ.hom.app (Fd.obj M) ≫ NZB.map (bd.app M) := by
    apply (cancel_epi (PZ.map dA.inv)).mp
    simp only [← PZ.map_comp_assoc, Iso.inv_hom_id, PZ.map_id, Category.id_comp]
    rw [reassoc_of% hd]
    simp
  have hb := bpd.naturality cA.hom
  have hz := δZ.hom.naturality tA.hom
  dsimp only [Functor.comp_map] at hb hz
  simp only [Functor.map_comp, Category.assoc]
  rw [he, reassoc_of% hz, ← NZB.map_comp_assoc, hcomp]
  simp only [Functor.map_comp, Category.assoc]
  rw [← PdB.map_comp_assoc, hc']
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hb, reassoc_of% hn, reassoc_of% hd']

private theorem compositionTransport
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    {QX : C ⥤ C'} {QY : D ⥤ D'} {QZ : E ⥤ E'}
    {Fc Ff : C ⥤ D} {Fd Fg : D ⥤ E} {Fe Fh : C ⥤ E}
    {Fc' Ff' : C' ⥤ D'} {Fd' Fg' : D' ⥤ E'} {Fe' Fh' : C' ⥤ E'}
    (kc : Fc ≅ Ff) (kd : Fd ≅ Fg) (ke : Fe ≅ Fh)
    (kc' : Fc' ≅ Ff') (kd' : Fd' ≅ Fg') (ke' : Fe' ≅ Fh')
    (comp : Ff ⋙ Fg ≅ Fh) (comp' : Ff' ⋙ Fg' ≅ Fh')
    (bc : Fc ⋙ QY ⟶ QX ⋙ Fc') (bd : Fd ⋙ QZ ⟶ QY ⋙ Fd')
    (be : Fe ⋙ QZ ⟶ QX ⋙ Fe')
    (bf : Ff ⋙ QY ⟶ QX ⋙ Ff') (bg : Fg ⋙ QZ ⟶ QY ⋙ Fg')
    (bh : Fh ⋙ QZ ⟶ QX ⋙ Fh') (M : C)
    (hc : QY.map (kc.hom.app M) ≫ bf.app M = bc.app M ≫ kc'.hom.app (QX.obj M))
    (hd : QZ.map (kd.hom.app (Fc.obj M)) ≫ bg.app (Fc.obj M) =
      bd.app (Fc.obj M) ≫ kd'.hom.app (QY.obj (Fc.obj M)))
    (he : QZ.map (ke.hom.app M) ≫ bh.app M = be.app M ≫ ke'.hom.app (QX.obj M))
    (hh : QZ.map (comp.hom.app M) ≫ bh.app M =
      bg.app (Ff.obj M) ≫ Fg'.map (bf.app M) ≫ comp'.hom.app (QX.obj M)) :
    QZ.map (Fd.map (kc.hom.app M) ≫ kd.hom.app (Ff.obj M) ≫
      comp.hom.app M ≫ ke.inv.app M) ≫ be.app M =
    bd.app (Fc.obj M) ≫ Fd'.map (bc.app M) ≫
      Fd'.map (kc'.hom.app (QX.obj M)) ≫ kd'.hom.app (Ff'.obj (QX.obj M)) ≫
        comp'.hom.app (QX.obj M) ≫ ke'.inv.app (QX.obj M) := by
  apply (cancel_mono (ke'.hom.app (QX.obj M))).mp
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← he]
  simp only [← QZ.map_comp_assoc, Iso.inv_hom_id_app, QZ.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [hh]
  have hn := bg.naturality (kc.hom.app M)
  dsimp only [Functor.comp_map] at hn
  have hk := congrArg QZ.map (kd.hom.naturality (kc.hom.app M))
  simp only [Functor.map_comp] at hk
  rw [reassoc_of% hk]
  rw [reassoc_of% hn, reassoc_of% hd]
  rw [← Fg'.map_comp_assoc, hc, Fg'.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% (kd'.hom.naturality (bc.app M)),
    ← reassoc_of% (kd'.hom.naturality (kc'.hom.app (QX.obj M)))]

private theorem cancelBoundary {C : Type*} [Category C]
    {U V W Q : C} (a : U ≅ V) (b : V ⟶ Q) (c : U ⟶ W) (d : W ⟶ Q)
    (h : a.hom ≫ b = c ≫ d) : a.inv ≫ c ≫ d = b := by
  rw [← h, a.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem compositionSiteBoundary_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (c : Compactification f) (d : Compactification g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hF : DerivedCategory.TStructure.t.plus
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj L.obj)) :
    (compositionSiteBoundary A c d L).hom =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
        ((compactSupportSiteComparison A c).hom.app L) ≫
      (compactSupportSiteComparison A d).hom.app ⟨_, hF⟩ := by
  let K₀ := (Etale.rightDerivedLowerShriekOfCompactificationPlus
    (ModuleCat.{u + 1} A) c).obj L
  let K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) := ⟨_, hF⟩
  let e₀ := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) c).app L
  let e : K₀ ≅ K := DerivedCategory.Plus.ι.preimageIso e₀
  have hn := (compactSupportSiteComparison A d).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  have hm : DerivedCategory.Plus.ι.map e.hom = e₀.hom := by
    exact Functor.map_preimage _ _
  rw [hm] at hn
  change (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map e₀.hom) ≫
      (compactSupportSiteComparison A d).hom.app K =
    (compactSupportSiteComparison A d).hom.app K₀ ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) d).map e₀.hom) at hn
  have hh := cancelBoundary
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).mapIso
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.mapIso e₀))
    ((compactSupportSiteComparison A d).hom.app K)
    ((compactSupportSiteComparison A d).hom.app K₀)
    ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map e₀.hom)) hn
  have ht := congrArg
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
      ((compactSupportSiteComparison A c).hom.app L) ≫ ·) hh
  simpa only [compositionSiteBoundary, Iso.trans_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc, K₀, K, e₀] using ht

set_option maxRecDepth 2000 in
set_option backward.isDefEq.respectTransparency false in
/-- The same coefficient maps respect geometric composition, on each site and for any
three compactifications. Scalar restriction need not be faithful in the derived category.
Source: Stacks 0F7J and 0GL6; blueprint Steps 5, 6, 8 and 9
(blueprint: lem-sp-et-proet-coefficient-compatibility).

Proof: Step 8 chooses the compatible compactification tower of
lem-cbc-compactifiable-compatible-tower. Its compositor is the proper/open interchange
followed by proper and open composition. Step 6 uses lem-sp-proper-open-coefficient-mate
for the cartesian square in that tower. Step 5 commutes coefficients past the proper and
open compositors by counit transposition and the summand tensor calculation. Pasting
gives the composition equation. Step 9 conjugates to arbitrary compactifications using
the refinement square just stated; inverse refinement factors cancel. The site versions
of the same constituent squares give the displayed pro-etale identity. Inserting the
invertible delta at the final input is exactly the retained etale-origin convention. -/
theorem etaleProEtaleCoefficientCompatibility_composition
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (_hL : AdjunctionTransfer.etaleProperty (ULift.{u + 1, u} A) X L.obj) :
    ∃ hLB : DerivedCategory.TStructure.t.plus ((Etale.scalarExtension (uliftRingHom φ) X).obj
      L.obj),
      ((Etale.scalarExtension (uliftRingHom φ) Z).map ((etaleCompositor (ULift.{u + 1, u} A) c d
        e).hom.app L.obj) ≫
        etaleCoefficientMap (uliftRingHom φ) e L.obj =
      etaleCoefficientMap (uliftRingHom φ) d
          ((Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj) ≫
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u}
          B)) d).map
          (etaleCoefficientMap (uliftRingHom φ) c L.obj) ≫
        (etaleCompositor (ULift.{u + 1, u} B) c d e).hom.app ((Etale.scalarExtension
          (uliftRingHom φ) X).obj L.obj)) ∧
      ((@pbcFixedScalarExtension.{u} Z.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology Z)
          (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance (uliftRingHom
            φ)).map
          (siteCompositor (ULift.{u + 1, u} A) c d e L).hom ≫
        (proEtaleCoefficientMap φ e).app
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            X).mapDerivedCategory.obj L.obj) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) e).map
          ((pbcComparisonReduction.{u} X (uliftRingHom φ)).hom.app L.obj) =
      (proEtaleCoefficientMap φ d).app
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            c).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
              X).mapDerivedCategory.obj L.obj)) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) d).map
          ((proEtaleCoefficientMap φ c).app
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
              X).mapDerivedCategory.obj L.obj)) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) d).map
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} B))
            c).map
            ((pbcComparisonReduction.{u} X (uliftRingHom φ)).hom.app L.obj)) ≫
        (siteCompositor (ULift.{u + 1, u} B) c d e ⟨(Etale.scalarExtension (uliftRingHom φ)
          X).obj L.obj, hLB⟩).hom) := by
  obtain ⟨hLB, _, _, hc⟩ := etaleProEtaleCoefficientCompatibility
    ell p _hp _hEll k _hA _hB φ f c L _hL
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian
    (Z ↘ Spec (.of k))
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  let : IsNoetherian Y := ⟨⟩
  let : IsNoetherian Z := ⟨⟩
  let := c.hasCompactification
  let := d.hasCompactification
  let := e.hasCompactification
  let LB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :=
    ⟨(Etale.scalarExtension (uliftRingHom φ) X).obj L.obj, hLB⟩
  have he := Etale.etaleCompactScalarComposition (uliftRingHom φ) f g L ⟨LB, rfl⟩
  have hcChosen := (Etale.etaleCompactScalarCoherence (uliftRingHom φ) f c).2.2
    (HasCompactification.compactification f) L ⟨LB, rfl⟩
  have heChosen := (Etale.etaleCompactScalarCoherence (uliftRingHom φ) (f ≫ g) e).2.2
    (HasCompactification.compactification (f ≫ g)) L ⟨LB, rfl⟩
  let LF₀ := (Etale.rightDerivedLowerShriekOfCompactificationPlus
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L
  let LFB₀ := (Etale.rightDerivedLowerShriekOfCompactificationPlus
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).obj LB
  let eFA := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app L
  let eFB := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).app LB
  let LF : DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
    ⟨_, DerivedCategory.TStructure.t.plus.prop_of_iso eFA LF₀.property⟩
  have hqF : IsIso ((Etale.compactScalarMap (uliftRingHom φ) c).app L.obj) :=
    (Etale.etaleCompactScalarCoherence (uliftRingHom φ) f c).1 L.obj
  have hQF : DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension (uliftRingHom φ) Y).obj LF.obj) := by
    exact DerivedCategory.TStructure.t.plus.prop_of_iso
      (eFB ≪≫ (asIso ((Etale.compactScalarMap (uliftRingHom φ) c).app L.obj)).symm)
      LFB₀.property
  have hdChosen := (Etale.etaleCompactScalarCoherence (uliftRingHom φ) g d).2.2
    (HasCompactification.compactification g) LF ⟨⟨_, hQF⟩, rfl⟩
  have heEt :
      (Etale.scalarExtension (uliftRingHom φ) Z).map
          ((etaleCompositor (ULift.{u + 1, u} A) c d e).hom.app L.obj) ≫
        etaleCoefficientMap (uliftRingHom φ) e L.obj =
      etaleCoefficientMap (uliftRingHom φ) d LF.obj ≫
        (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) d).map
          (etaleCoefficientMap (uliftRingHom φ) c L.obj) ≫
        (etaleCompositor (ULift.{u + 1, u} B) c d e).hom.app LB.obj := by
    have ht := compositionTransport
      (Etale.rightDerivedLowerShriekIso (ULift.{u + 1, u} A) c)
      (Etale.rightDerivedLowerShriekIso (ULift.{u + 1, u} A) d)
      (Etale.rightDerivedLowerShriekIso (ULift.{u + 1, u} A) e)
      (Etale.rightDerivedLowerShriekIso (ULift.{u + 1, u} B) c)
      (Etale.rightDerivedLowerShriekIso (ULift.{u + 1, u} B) d)
      (Etale.rightDerivedLowerShriekIso (ULift.{u + 1, u} B) e)
      (Etale.unboundedEtaleLowerShriekCompIso (ULift.{u + 1, u} A) f g)
      (Etale.unboundedEtaleLowerShriekCompIso (ULift.{u + 1, u} B) f g)
      (Etale.compactScalarMap (uliftRingHom φ) c)
      (Etale.compactScalarMap (uliftRingHom φ) d)
      (Etale.compactScalarMap (uliftRingHom φ) e)
      (Etale.compactScalarChosenMap (uliftRingHom φ) f)
      (Etale.compactScalarChosenMap (uliftRingHom φ) g)
      (Etale.compactScalarChosenMap (uliftRingHom φ) (f ≫ g)) L.obj
      hcChosen hdChosen heChosen he
    simp only [etaleCoefficientMap_eq_compactScalarMap]
    simpa only [etaleCompositor, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
      Category.assoc, LF, LB, Functor.comp_obj, ObjectProperty.ι_obj] using ht
  refine ⟨hLB, heEt, ?_⟩
  have hAU : ∃ n : ℕ, ∀ x : ULift.{u + 1, u} A, (ell ^ n) • x = 0 := by
    obtain ⟨n, hn⟩ := _hA
    refine ⟨n, fun x ↦ ?_⟩
    exact ULift.ext _ _ (hn x.down)
  let := coefficient_hasInvertibleExponent (ULift.{u + 1, u} A) ell p _hEll k hAU
    (Y ↘ Spec (.of k))
  have hLF := compactSupport_preserves_etaleProperty (ULift.{u + 1, u} A) k
    (Y ↘ Spec (.of k)) c L.obj _hL
  obtain ⟨_, _, _, hd⟩ := etaleProEtaleCoefficientCompatibility
    ell p _hp _hEll k _hA _hB φ g d LF hLF
  obtain ⟨_, _, _, heSite⟩ := etaleProEtaleCoefficientCompatibility
    ell p _hp _hEll k _hA _hB φ (f ≫ g) e L _hL
  let LQF : DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) := ⟨_, hQF⟩
  let LFB : DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :=
    ⟨_, DerivedCategory.TStructure.t.plus.prop_of_iso eFB LFB₀.property⟩
  let v : LQF ⟶ LFB := ObjectProperty.homMk
    (etaleCoefficientMap (uliftRingHom φ) c L.obj)
  have hn := (compactSupportSiteComparison (ULift.{u + 1, u} B) d).hom.naturality v
  dsimp only [Functor.comp_map] at hn
  have ht := siteCompositionTransport
    (QY := Etale.scalarExtension (uliftRingHom φ) Y)
    (QZ := Etale.scalarExtension (uliftRingHom φ) Z)
    (pbcComparisonReduction.{u} Y (uliftRingHom φ))
    (pbcComparisonReduction.{u} Z (uliftRingHom φ))
    (Etale.compactScalarMap (uliftRingHom φ) d) (proEtaleCoefficientMap φ d)
    ((compactSupportSiteComparison (ULift.{u + 1, u} A) c).app L)
    ((compactSupportSiteComparison (ULift.{u + 1, u} B) c).app LB)
    ((compactSupportSiteComparison (ULift.{u + 1, u} A) d).app LF)
    ((compactSupportSiteComparison (ULift.{u + 1, u} B) d).app LQF)
    ((compactSupportSiteComparison (ULift.{u + 1, u} B) d).app LFB)
    ((compactSupportSiteComparison (ULift.{u + 1, u} A) e).app L)
    ((compactSupportSiteComparison (ULift.{u + 1, u} B) e).app LB)
    ((etaleCompositor (ULift.{u + 1, u} A) c d e).app L.obj)
    ((etaleCompositor (ULift.{u + 1, u} B) c d e).app LB.obj)
    (etaleCoefficientMap (uliftRingHom φ) c L.obj)
    (etaleCoefficientMap (uliftRingHom φ) e L.obj)
    ((proEtaleCoefficientMap φ c).app
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          X).mapDerivedCategory.obj L.obj) ≫
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).map
        ((pbcComparisonReduction.{u} X (uliftRingHom φ)).hom.app L.obj))
    ((proEtaleCoefficientMap φ e).app
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          X).mapDerivedCategory.obj L.obj) ≫
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) e).map
        ((pbcComparisonReduction.{u} X (uliftRingHom φ)).hom.app L.obj))
    hc (by
      simpa only [← etaleCoefficientMap_eq_compactScalarMap, Functor.comp_obj,
        ObjectProperty.ι_obj, Iso.app_hom, Iso.app_inv, LF, LQF] using hd)
    heSite hn (by
      simpa only [← etaleCoefficientMap_eq_compactScalarMap, Functor.comp_obj,
        ObjectProperty.ι_obj, Iso.app_hom, Iso.app_inv, LF, LB] using heEt)
  simp only [siteCompositor, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [compositionSiteBoundary_hom _ _ _ _ LF.property,
    compositionSiteBoundary_hom _ _ _ _ LFB.property]
  simpa only [Functor.map_comp, Category.assoc, Functor.comp_obj,
    ObjectProperty.ι_obj, Iso.app_hom, Iso.app_inv, LF, LB, LFB, LQF] using ht

/-- Evaluate the recorded normalized sum comparison, supplying the Noetherian and compact
structures derived from finite type over the field. No extra scheme hypothesis is imposed.
Source: SGA 4 XVII 6.2.11; blueprint etale-sum clause
(blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def normalizedSumComparison (A : Type (u + 1)) [CommRing A]
    (k : Type u) [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (N : Etale.EtaleCompactSupportNormalization A) (e : X ⟶ Y) [Etale e] [IsSeparated e]
    (c : Compactification e) :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  N.comparison e c

/-- The compact-support coefficient map agrees with summandwise tensor extension for a
separated etale morphism. The normalization records fix the maps by their graph-extension
and derived-representative equations, so no arbitrary endpoint isomorphism is assumed.
Source: Stacks 0GL6 and 03S6; blueprint Step 10
(blueprint: lem-sp-et-proet-coefficient-compatibility).

Proof: lem-asd-etale-compact-support-normalization sends a properly supported section to
its labelled sheet components and makes j!H acyclic for the proper factor. On the bounded
flat model P of Step 1, sum extension preserves flatness and K-flatness by the slice tensor
formula, exactness of sum extension and exact inverse image. The same applies to j!P.
Apply lem-sp-acyclic-flat-proper-coefficient-model to j!P: the proper coefficient mate is
the sheaf projection map. Composing with the open tensor comparison sends each labelled
section tensor b to the same labelled section with coefficient b, in both orders.
The graph normalizations retain the label, so the complexes give equal derived maps.
lem-amb-etale-sum-stalks includes empty fibres, without requiring finitely many lifts
on each test object. -/
theorem etaleProEtaleCoefficientCompatibility_sum
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [Etale f] (c : Compactification f)
    (NA : Etale.EtaleCompactSupportNormalization A)
    (NB : Etale.EtaleCompactSupportNormalization B)
    (L : Etale.DerivedCategoryModule A X)
    (_hL : AdjunctionTransfer.etaleProperty A X L) :
    etaleCoefficientMap φ c L ≫
        (normalizedSumComparison B k NB f c).hom.app ((Etale.scalarExtension φ X).obj L) =
      (Etale.scalarExtension φ Y).map ((normalizedSumComparison A k NA f c).hom.app L) ≫
        (sumCoefficientIso φ f).hom.app L := by
  sorry

private theorem coefficientCounitTransport
    {C : Type*} [Category C] {U V W D E P Q R S F : C}
    (e : U ≅ V) (c₀ : D ≅ Q) (c₁ : E ≅ R) (z : F ≅ S)
    {b : V ⟶ W} {d : W ⟶ D} {a : D ⟶ E} {δ : U ⟶ P}
    {β : P ⟶ Q} {a' : Q ⟶ R} {ε : R ⟶ S} {r : P ⟶ S} {t : U ⟶ F}
    (hs : e.hom ≫ b ≫ d = δ ≫ β ≫ c₀.inv)
    (hn : a ≫ c₁.hom = c₀.hom ≫ a')
    (hc : β ≫ a' ≫ ε = r) (hd : t ≫ z.hom = δ ≫ r) :
    b ≫ d ≫ a ≫ c₁.hom ≫ ε ≫ z.inv = e.inv ≫ t := by
  apply (cancel_epi e.hom).mp
  rw [reassoc_of% hs, reassoc_of% hn]
  simp only [Iso.inv_hom_id_assoc]
  rw [reassoc_of% hc, ← reassoc_of% hd]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Transport of an actual etale adjunction counit carries its coefficient identity to
the identity for the named pro-etale coefficient map. The two c-inverses in the paper
are `compactSupportSiteComparison.hom` with the existing library's opposite orientation.
The final delta removes only the output coefficient/site identification.
Source: blueprint Step 11, using det-sp-et-proet-adjunction-transfer's counit formula
(blueprint: lem-sp-et-proet-coefficient-compatibility).

Proof: solve the site/coefficient square of Steps 1--4 for the b-inverse. Substitute it
in coefficient extension of the transported A-counit. Naturality of delta moves that
counit across the tensor/site comparison. Apply the assumed etale coefficient-counit
identity. Naturality of the B-site comparison moves the right-functor comparison across
c_B-inverse. What remains is precisely the transported B-counit after compact support of
the transported right-functor comparison. The displayed form avoids inverses of beta and
b by precomposing with b; their invertibility is in the first statement. This substitution
requires no admissibility theorem for arbitrary finite rings. -/
theorem etaleProEtaleCoefficientCompatibility_counit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (HA : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y ⥤ Etale.DerivedCategoryModule
      (ULift.{u + 1, u} A) X)
    (HB : Etale.DerivedCategoryModule (ULift.{u + 1, u} B) Y ⥤ Etale.DerivedCategoryModule
      (ULift.{u + 1, u} B) X)
    (adjA : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u}
      A)) c ⊣ HA)
    (adjB : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u}
      B)) c ⊣ HB)
    (N : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y)
    (hHA : AdjunctionTransfer.etaleProperty (ULift.{u + 1, u} A) X (HA.obj N))
    (hHB : AdjunctionTransfer.etaleProperty (ULift.{u + 1, u} B) X (HB.obj
      ((Etale.scalarExtension (uliftRingHom φ) Y).obj N)))
    (a : (Etale.scalarExtension (uliftRingHom φ) X).obj (HA.obj N) ⟶
      HB.obj ((Etale.scalarExtension (uliftRingHom φ) Y).obj N))
    (_hCounit : etaleCoefficientMap (uliftRingHom φ) c (HA.obj N) ≫
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u}
          B)) c).map a ≫
        adjB.counit.app ((Etale.scalarExtension (uliftRingHom φ) Y).obj N) =
      (Etale.scalarExtension (uliftRingHom φ) Y).map (adjA.counit.app N)) :
    (proEtaleCoefficientMap φ c).app
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj
          (HA.obj N)) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).map
        ((pbcComparisonReduction.{u} X (uliftRingHom φ)).hom.app (HA.obj N) ≫
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B))
            X).mapDerivedCategory.map a) ≫
      (compactSupportSiteComparison (ULift.{u + 1, u} B) c).hom.app
        ((AdjunctionTransfer.etaleToPlus (ULift.{u + 1, u} B) X).obj
          ⟨HB.obj ((Etale.scalarExtension (uliftRingHom φ) Y).obj N), hHB⟩) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) Y).mapDerivedCategory.map
        (adjB.counit.app ((Etale.scalarExtension (uliftRingHom φ) Y).obj N)) ≫
      (pbcComparisonReduction.{u} Y (uliftRingHom φ)).inv.app N =
    (@pbcFixedScalarExtension.{u} Y.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology Y)
          (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance (uliftRingHom
            φ)).map
      ((compactSupportSiteComparison (ULift.{u + 1, u} A) c).hom.app
          ((AdjunctionTransfer.etaleToPlus (ULift.{u + 1, u} A) X).obj ⟨HA.obj N, hHA⟩) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).mapDerivedCategory.map
          (adjA.counit.app N))  := by
  let LA := (AdjunctionTransfer.etaleToPlus (ULift.{u + 1, u} A) X).obj ⟨HA.obj N, hHA⟩
  let MB := (AdjunctionTransfer.etaleToPlus (ULift.{u + 1, u} B) X).obj
    ⟨HB.obj ((Etale.scalarExtension (uliftRingHom φ) Y).obj N), hHB⟩
  obtain ⟨hLB, _, _, hs⟩ := etaleProEtaleCoefficientCompatibility
    ell p _hp _hEll k _hA _hB φ f c LA hHA
  let LB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :=
    ⟨(Etale.scalarExtension (uliftRingHom φ) X).obj (HA.obj N), hLB⟩
  have hn := (compactSupportSiteComparison (ULift.{u + 1, u} B) c).hom.naturality
    (ObjectProperty.homMk a : LB ⟶ MB)
  dsimp only [Functor.comp_map] at hn
  have hc := congrArg
    ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) Y).mapDerivedCategory.map)
    _hCounit
  simp only [Functor.map_comp] at hc
  have hd := (pbcComparisonReduction.{u} Y (uliftRingHom φ)).hom.naturality
    (adjA.counit.app N)
  dsimp only [Functor.comp_map] at hd
  have ht := coefficientCounitTransport
    ((liftedScalarExtension φ Y).mapIso
      ((compactSupportSiteComparison (ULift.{u + 1, u} A) c).app LA).symm)
    ((compactSupportSiteComparison (ULift.{u + 1, u} B) c).app LB)
    ((compactSupportSiteComparison (ULift.{u + 1, u} B) c).app MB)
    ((pbcComparisonReduction.{u} Y (uliftRingHom φ)).app N) hs hn hc hd
  simp only [Functor.map_comp, Category.assoc]
  convert ht using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
private theorem openCoefficientInverse_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X T : Scheme.{u}} (j : X ⟶ T) [IsOpenImmersion j]
    {L M : Etale.DerivedCategoryModule A X} (a : L ⟶ M) :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((Etale.scalarExtension φ X).map a) ≫ Etale.properOpenCoefficientOpenInverse φ j M =
      Etale.properOpenCoefficientOpenInverse φ j L ≫ (Etale.scalarExtension φ T).map
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map a) := by
  unfold Etale.properOpenCoefficientOpenInverse
  apply Adjunction.homEquiv_naturality_right_square
  have hu := (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, ← Functor.map_comp, hu, Functor.map_comp, Category.assoc]
  rw [Category.assoc]
  exact congrArg ((Etale.scalarExtension φ X).map
    ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).unit.app L) ≫ ·)
    ((Etale.properOpenCoefficientPullbackIso φ j).inv.naturality
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map a))

set_option backward.isDefEq.respectTransparency false in
private theorem openCoefficientHom_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X T : Scheme.{u}} (j : X ⟶ T) [IsOpenImmersion j]
    {L M : Etale.DerivedCategoryModule A X} (a : L ⟶ M) :
    (Etale.scalarExtension φ T).map
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map a) ≫
        (Etale.properOpenCoefficientOpenIso φ j M).hom =
      (Etale.properOpenCoefficientOpenIso φ j L).hom ≫
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
          ((Etale.scalarExtension φ X).map a) := by
  have h :
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
          ((Etale.scalarExtension φ X).map a) ≫
          (Etale.properOpenCoefficientOpenIso φ j M).inv =
        (Etale.properOpenCoefficientOpenIso φ j L).inv ≫
          (Etale.scalarExtension φ T).map
            ((Etale.openImmersionLowerShriek
              (ModuleCat.{u + 1} A) j).mapDerivedCategory.map a) :=
    openCoefficientInverse_naturality φ j a
  apply (cancel_mono (Etale.properOpenCoefficientOpenIso φ j M).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the objectwise proper/open etale coefficient map on the stated input
class. All other constituent maps are already natural transformations or composites of
them; the site formulas are their conjugates on the full bounded-below subcategory.
Source: blueprint final sentence and Step 11
(blueprint: lem-sp-et-proet-coefficient-compatibility).

Proof: the proper coefficient comparison is a natural counit mate. Invert the open
coefficient map and transpose under the open adjunction: naturality becomes naturality
of its unit and of scalar/pullback comparison. Transpose back and compose with the proper
mate. This gives the displayed equation. Naturality of c, delta, canonical compactification
changes and compositors then gives naturality of every square and every transported
counit identity, as asserted in Step 11. -/
theorem etaleProEtaleCoefficientCompatibility_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (L M : Etale.DerivedCategoryModule A X)
    (_hL : AdjunctionTransfer.etaleProperty A X L)
    (_hM : AdjunctionTransfer.etaleProperty A X M) (a : L ⟶ M) :
    (Etale.scalarExtension φ Y).map
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map a) ≫
      etaleCoefficientMap φ c M =
    etaleCoefficientMap φ c L ≫
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
        ((Etale.scalarExtension φ X).map a) := by
  unfold etaleCoefficientMap
  have h := (Etale.scalarMate φ c.g).naturality
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.map a)
  dsimp only [Functor.comp_map] at h
  change (Etale.scalarExtension φ Y).map
      ((Etale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.map a)) ≫
      (Etale.scalarMate φ c.g).app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.map
        (Etale.properOpenCoefficientOpenIso φ c.i M).hom =
    ((Etale.scalarMate φ c.g).app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj L) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.map
        (Etale.properOpenCoefficientOpenIso φ c.i L).hom) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.map
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.map
          ((Etale.scalarExtension φ X).map a))
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp,
    openCoefficientHom_naturality φ c.i a, Functor.map_comp, Category.assoc]

end AlgebraicGeometry.ProEtale.CoefficientCompatibility
