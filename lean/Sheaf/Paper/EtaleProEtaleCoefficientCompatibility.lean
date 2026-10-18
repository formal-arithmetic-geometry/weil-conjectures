/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
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
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import Sheaf.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import Sheaf.AlgebraicGeometry.EtaleSumStalks
import Mathlib.Algebra.DirectSum.Module
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
import Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Sites.Etale
import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.Paper.AcyclicFlatProperCoefficientModel
import Sheaf.Paper.ProperOpenCoefficientMate
import Sheaf.Paper.RefinementCoefficientMate
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
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
          L.obj, hLB⟩).hom) := by
  sorry

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
  sorry


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
          (adjA.counit.app N)) := by
  sorry

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
  sorry

end AlgebraicGeometry.ProEtale.CoefficientCompatibility
