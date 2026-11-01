/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.AlgebraicGeometry.P1CompactificationFibre.P1CompactificationFibre
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FixedFinitePositiveCoefficientTwist
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyHom
public import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Derived.DerivedNakayamaFirstReduction
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp

/-!
# The geometric origin-to-compact-support map

Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/thm-pur-rank-one-thom.proof.md,
Step 2 (blueprint: lem-pur-geometric-origin-compact-comparison).
The map is constructed using the closed-support counit. Its normalization through
ordinary direct image specifies the proper/composition identification uniquely.

## Main definitions

* `GeometricOrigin.map`: the actual proper-support-forgetting map.
* `GeometricOrigin.Finite.Comparison`: equality with the retained finite etale map.
* `GeometricOrigin.finiteComparison`: the positive-quotient specialization.

## Main statements

* `GeometricOrigin.properSection_isIso`: the canonical proper-section identification.
* `GeometricOrigin.geometric_origin_compact_comparison`: all four coefficient cases
  together with the finite comparison of the specified arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.GeometricOrigin

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The ordinary unbounded derived category for the pulled-back condensed ring.
Source: det-def-sf-operations
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
abbrev D (T : Scheme.{u}) := DerivedCategory.{u + 1} (supportModules Λ T)

/-- The specified standard compactification functor, without a chosen replacement.
Source: blueprint Step 2 (blueprint: lem-pur-geometric-origin-compact-comparison). -/
abbrev compact (S : Scheme.{u}) :=
  rightDerivedLowerShriekOfCompactification Λ (Etale.P1CompactificationFibre.compactification S)

/-- The canonical map from open extension by zero to ordinary derived direct image.
It is the mate of the inverse open-adjunction unit.
Source: blueprint Step 2 (blueprint: lem-pur-geometric-origin-compact-comparison). -/
def openToDirect {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : D Λ U) :
    (openImmersionLowerShriek Λ j).mapDerivedCategory.obj K ⟶
      (lowerStar Λ j).rightDerivedFunctor.obj K := by
  let a := openImmersionLowerShriekUpperStarAdjunction Λ j
  letI : IsIso a.unit := a.unit_isIso_of_L_fully_faithful
  let J : D Λ U ⥤ D Λ T := (openImmersionLowerShriek Λ j).mapDerivedCategory
  let V : D Λ T ⥤ D Λ U := (upperStar Λ j).mapDerivedCategory
  let A : J ⊣ V := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j
  let e : J ⋙ V ≅ 𝟭 (D Λ U) :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso a.unit).symm ≪≫
      Functor.mapDerivedCategoryIdIso _
  let hf := A.fullyFaithfulLOfCompIsoId e
  letI := hf.full
  letI := hf.faithful
  letI : IsIso A.unit := A.unit_isIso_of_L_fully_faithful
  exact ((upperStarLowerStarAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction
    ).homEquiv _ _ (inv (A.unit.app K))

/-- Forget compact support, using the unit-normalized open comparison and the
ordinary derived direct-image compositor.
Source: blueprint Step 2 (blueprint: lem-pur-geometric-origin-compact-comparison). -/
def compactToDirect (S : Scheme.{u}) (K : D Λ (𝔸(PUnit.{u + 1}; S))) :
    (compact Λ S).obj K ⟶
      (lowerStar Λ (𝔸(PUnit.{u + 1}; S) ↘ S)).rightDerivedFunctor.obj K :=
  (lowerStar Λ (ProjectiveLine S ↘ S)).rightDerivedFunctor.map
      (openToDirect Λ (Etale.P1CompactificationFibre.j S) K) ≫
    (rightDerivedLowerStarComp Λ (Etale.P1CompactificationFibre.j S)
      (ProjectiveLine S ↘ S)).hom.app K ≫
    (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ
      (ProjectiveLine.infinityChart_over (S := S)))).hom.app K

/-- The origin complement over a field is quasi-compact, since the affine line
is Noetherian. Source: the finite-type geometry in Step 2
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
instance originComplementQuasiCompact (Ω : Type u) [Field Ω] :
    QuasiCompact (AffineSpace.zeroSection PUnit.{u + 1} (Spec (.of Ω))).openComplement.ι := by
  let : IsNoetherian (𝔸(PUnit.{u + 1}; Spec (.of Ω))) :=
    isNoetherian_of_locallyOfFiniteType (𝔸(PUnit.{u + 1}; Spec (.of Ω)) ↘ Spec (.of Ω))
  infer_instance

variable (S : Scheme.{u})
  [QuasiCompact (AffineSpace.zeroSection PUnit.{u + 1} S).openComplement.ι]

/-- Exact closed direct image, with the canonical complementary open.
Source: closed-support formalism in Step 2
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
instance originPushExact :
    PreservesFiniteColimits (lowerStar Λ (AffineSpace.zeroSection PUnit.{u + 1} S)) :=
  closedSupport_lowerStarExact Λ _ _
    (AffineSpace.zeroSection PUnit.{u + 1} S).range_eq_compl_range_openComplement_ι

/-- The actual closed exceptional inverse image, computed by derived supported sections.
Source: blueprint Step 2 (blueprint: lem-pur-geometric-origin-compact-comparison). -/
abbrev supported :=
  (closedSupport Λ (AffineSpace.zeroSection PUnit.{u + 1} S)
    (AffineSpace.zeroSection PUnit.{u + 1} S).openComplement.ι).rightDerivedFunctor

/-- The proper/composition identification in its forward direction, normalized by
forgetting compact support, exact closed direct image, and the identity compositor.
Source: blueprint Step 2 (blueprint: lem-pur-geometric-origin-compact-comparison). -/
def properSection (Q : D Λ S) :
    (compact Λ S).obj
      ((lowerStar Λ (AffineSpace.zeroSection PUnit.{u + 1} S)).mapDerivedCategory.obj Q) ⟶ Q :=
  compactToDirect Λ S _ ≫
    (lowerStar Λ (𝔸(PUnit.{u + 1}; S) ↘ S)).rightDerivedFunctor.map
      ((lowerStar Λ (AffineSpace.zeroSection PUnit.{u + 1} S)
        ).rightDerivedFunctorIsoMapDerivedCategory.inv.app Q) ≫
    (rightDerivedLowerStarComp Λ (AffineSpace.zeroSection PUnit.{u + 1} S)
      (𝔸(PUnit.{u + 1}; S) ↘ S)).hom.app Q ≫
    (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ
      (AffineSpace.zeroSection_comp_over _ _))).hom.app Q ≫
    (Functor.rightDerivedFunctorNatIso (lowerStarId Λ S) ≪≫
      Functor.rightDerivedFunctorIdIso _).hom.app Q

/-- Proper origin support identifies compact direct image with the identity.
Source: blueprint Step 2 (blueprint: lem-pur-geometric-origin-compact-comparison).
Proof: extension by zero of a sheaf supported on the closed origin agrees with its
ordinary direct image in P1, because that origin is proper over the base. This
identification is induced by the open unit. Derive on K-injective resolutions,
compose the two direct images and use ai=id. These are exactly the factors of
properSection, so the comparison is invertible for every complex Q. -/
theorem properSection_isIso (Q : D Λ S) : IsIso (properSection Λ S Q) := by
  sorry

/-- The specified map u: invert the proper/composition identification and apply
compact support to the actual closed-support counit, with no chosen abstract isomorphism.
Source: blueprint Step 2 (blueprint: lem-pur-geometric-origin-compact-comparison). -/
def map (M : D Λ (𝔸(PUnit.{u + 1}; S))) :
    (supported Λ S).obj M ⟶ (compact Λ S).obj M := by
  letI := properSection_isIso Λ S ((supported Λ S).obj M)
  exact inv (properSection Λ S ((supported Λ S).obj M)) ≫
    (compact Λ S).map ((closedSupportDerivedAdjunction Λ
      (AffineSpace.zeroSection PUnit.{u + 1} S)
      (AffineSpace.zeroSection PUnit.{u + 1} S).openComplement.ι
      (AffineSpace.zeroSection PUnit.{u + 1} S).range_eq_compl_range_openComplement_ι
      ).counit.app M)

end AlgebraicGeometry.ProEtale.CondensedRing.GeometricOrigin

namespace AlgebraicGeometry.ProEtale.CondensedRing.GeometricOrigin.Finite
open FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
  [IsTopologicalRing A] [Finite A]
  (E : ∀ T : Scheme.{u}, Encoding A T)

/-- Realization through the retained ordinary finite coefficient encoding.
Source: finite comparison in Step 2
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
abbrev realize (T : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory ⋙
    (E T).fixedDerived.inverse

/-- Realization on bounded-below etale complexes, retaining the antecedent.
Source: def-weil-pbc-etale-origin-witness
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
abbrev realizePlus (T : Scheme.{u}) := DerivedCategory.Plus.ι ⋙ realize A E T

/-- The normalized inverse-image comparison obtained by conjugating the recorded
sectionwise direct-image comparison and taking its left-adjunction mate.
Source: def-sf-normalized-encoding-direct-image, blueprint rank-one Thom Step 2
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
def encodingPullbackIso {T U : Scheme.{u}} (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) :
    CondensedRing.upperStar (coefficient A) f ⋙ (eU.ordinary.trans eU.fixed).functor ≅
      (eT.ordinary.trans eT.fixed).functor ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let R := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let i : CondensedRing.lowerStar (coefficient A) f ⋙ ET.functor ≅ EU.functor ⋙ R :=
    encodingPushforwardNatIso A T U f eT eU
  let k := Iso.isoCompInverse (H := ET) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EU) k
  let a := ET.toAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
  let b := (CondensedRing.upperStarLowerStarAdjunction (coefficient A) f).comp
    EU.toAdjunction
  exact (a.leftAdjointUniq (b.ofNatIsoRight kr)).symm

/-- The open-extension comparison is the left-adjunction mate of the normalized
inverse-image comparison, after cancelling the supplied encoding equivalences.
Source: def-sf-normalized-encoding-direct-image, blueprint rank-one Thom Step 2
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
def encodingOpenShriekIso {T U : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (eT : Encoding A T) (eU : Encoding A U) :
    CondensedRing.openImmersionLowerShriek (coefficient A) j ⋙
        (eT.ordinary.trans eT.fixed).functor ≅
      (eU.ordinary.trans eU.fixed).functor ⋙
        ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let i := encodingPullbackIso A j eT eU
  let k := Iso.isoCompInverse (H := EU) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := ET) k
  let a := (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
    (coefficient A) j).comp ET.toAdjunction
  let b := EU.toAdjunction.comp
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)
  exact a.leftAdjointUniq (b.ofNatIsoRight kr.symm)

/-- Derive the recorded identity-on-sections direct-image comparison using the
canonical exact-functor/localization comparisons on both sides.
Source: def-sf-normalized-encoding-direct-image, blueprint rank-one Thom Step 2
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
def encodingDerivedPushforwardIso {T U : Scheme.{u}} (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) :
    (CondensedRing.lowerStar (coefficient A) f).rightDerivedFunctor ⋙
        eT.fixedDerived.functor ≅
      eU.fixedDerived.functor ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).rightDerivedFunctor := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let F := CondensedRing.lowerStar (coefficient A) f
  let G := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  letI : ET.functor.Additive := inferInstanceAs
    (eT.ordinary.functor ⋙ eT.fixed.functor).Additive
  letI : EU.functor.Additive := inferInstanceAs
    (eU.ordinary.functor ⋙ eU.fixed.functor).Additive
  change F.rightDerivedFunctor ⋙ ET.functor.mapDerivedCategory ≅
    EU.functor.mapDerivedCategory ⋙ G.rightDerivedFunctor
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      F ET.functor).symm ≪≫
    Functor.rightDerivedFunctorNatIso (encodingPushforwardNatIso A T U f eT eU) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso EU.functor G

/-- Termwise localization of the canonical open-adjunction mate, with its exact
composition identifications. No isomorphism is chosen by an existence assertion.
Source: def-sf-normalized-encoding-direct-image, blueprint rank-one Thom Step 2
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
def encodingDerivedOpenShriekIso {T U : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (eT : Encoding A T) (eU : Encoding A U) :
    (CondensedRing.openImmersionLowerShriek (coefficient A) j).mapDerivedCategory ⋙
        eT.fixedDerived.functor ≅
      eU.fixedDerived.functor ⋙
        (ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).mapDerivedCategory := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let F := CondensedRing.openImmersionLowerShriek (coefficient A) j
  let G := ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j
  letI : ET.functor.Additive := inferInstanceAs
    (eT.ordinary.functor ⋙ eT.fixed.functor).Additive
  letI : EU.functor.Additive := inferInstanceAs
    (eU.ordinary.functor ⋙ eU.fixed.functor).Additive
  change F.mapDerivedCategory ⋙ ET.functor.mapDerivedCategory ≅
    EU.functor.mapDerivedCategory ⋙ G.mapDerivedCategory
  exact (Functor.mapDerivedCategoryCompIso F ET.functor).symm ≪≫
    Functor.mapDerivedCategoryNatIso (encodingOpenShriekIso A j eT eU) ≪≫
    Functor.mapDerivedCategoryCompIso EU.functor G


/-- The specified section-action compactification comparison, assembled from its
open-adjunction and direct-image comparisons, rather than chosen from Nonempty.
Source: finite encoding and blueprint Step 2
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
def encodingCompact (S : Scheme.{u}) :
    compact (coefficient A) S ⋙ (E S).fixedDerived.functor ≅
      (E (𝔸(PUnit.{u + 1}; S))).fixedDerived.functor ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A))
          (Etale.P1CompactificationFibre.compactification S) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (encodingDerivedPushforwardIso A
      (ProjectiveLine S ↘ S) (E S) (E (ProjectiveLine S))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (encodingDerivedOpenShriekIso A
      (Etale.P1CompactificationFibre.j S) (E (ProjectiveLine S))
      (E (𝔸(PUnit.{u + 1}; S)))) _ ≪≫ Functor.associator _ _ _

/-- The canonical compact-support comparison at a retained bounded-below witness.
Source: finite etale-origin comparison in Step 2
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
def compactComparison (S : Scheme.{u})
    (K : DerivedCategory.Plus (Sheaf (𝔸(PUnit.{u + 1}; S)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    (compact (coefficient A) S).obj ((realizePlus A E _).obj K) ≅
      (realizePlus A E S).obj
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} (ULift.{u + 1} A))
          (Etale.P1CompactificationFibre.compactification S)).obj K) :=
  (E S).fixedDerived.fullyFaithfulFunctor.preimageIso
    ((encodingCompact A E S).app _ ≪≫
      (ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A))
        (Etale.P1CompactificationFibre.compactification S)).mapIso
          ((E _).fixedDerived.counitIso.app _) ≪≫
      (compactSupportSiteComparison (ULift.{u + 1} A)
        (Etale.P1CompactificationFibre.compactification S)).app K ≪≫
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) S
        ).mapDerivedCategory.mapIso
          ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
            (ModuleCat.{u + 1} (ULift.{u + 1} A))
            (Etale.P1CompactificationFibre.compactification S)).symm.app K) ≪≫
      ((E S).fixedDerived.counitIso.app _).symm)

variable (S : Scheme.{u})
  [QuasiCompact (AffineSpace.zeroSection PUnit.{u + 1} S).openComplement.ι]

/-- The closed etale exceptional functor on bounded-below complexes.
Source: supported-cohomology realization in Step 2
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
abbrev etaleSupport :=
  (Etale.closedUpperShriek (ModuleCat.{u + 1} (ULift.{u + 1} A))
    (AffineSpace.zeroSection PUnit.{u + 1} S)
    (AffineSpace.zeroSection PUnit.{u + 1} S).openComplement.ι).rightDerivedFunctorPlus

/-- The canonical closed direct-image comparison, with both exact models retained.
Source: finite etale-origin comparison in Step 2
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
def pushComparison
    (Q : DerivedCategory.Plus (Sheaf S.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    (lowerStar (coefficient A) (AffineSpace.zeroSection PUnit.{u + 1} S)
      ).mapDerivedCategory.obj ((realizePlus A E S).obj Q) ≅
    (realizePlus A E _).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A))
        (AffineSpace.zeroSection PUnit.{u + 1} S)).mapDerivedCategoryPlus.obj Q) := by
  let i := AffineSpace.zeroSection PUnit.{u + 1} S
  let X := 𝔸(PUnit.{u + 1}; S)
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let cp := comparisonUpperStar B S
  let cx := comparisonUpperStar B X
  let p := ProEtale.lowerStar B i
  let t := Etale.lowerStar B i
  letI := isIso_fixedComparisonDirectImageMatePlus (ULift.{u + 1} A) i
  exact (E X).fixedDerived.fullyFaithfulFunctor.preimageIso
    ((E X).fixedDerived.functor.mapIso
      ((lowerStar (coefficient A) i).rightDerivedFunctorIsoMapDerivedCategory.symm.app _) ≪≫
    (encodingDerivedPushforwardIso A i (E X) (E S)).app _ ≪≫
    p.rightDerivedFunctor.mapIso ((E S).fixedDerived.counitIso.app _) ≪≫
    p.rightDerivedFunctor.mapIso (cp.mapDerivedCategoryPlusCompatibility.symm.app Q) ≪≫
    p.rightDerivedFunctorPlusCompatibility.symm.app (cp.mapDerivedCategoryPlus.obj Q) ≪≫
    DerivedCategory.Plus.ι.mapIso
      ((asIso (fixedComparisonDirectImageMatePlus (ULift.{u + 1} A) i)).symm.app Q) ≪≫
    cx.mapDerivedCategoryPlusCompatibility.app (t.rightDerivedFunctorPlus.obj Q) ≪≫
    cx.mapDerivedCategory.mapIso (t.rightDerivedFunctorPlusCompatibility.app Q) ≪≫
    cx.mapDerivedCategory.mapIso (t.rightDerivedFunctorIsoMapDerivedCategory.app Q.obj) ≪≫
    cx.mapDerivedCategory.mapIso (t.mapDerivedCategoryPlusCompatibility.symm.app Q) ≪≫
    ((E X).fixedDerived.counitIso.app _).symm)

/-- The source comparison is the unique adjunct of the realized etale support
counit. This specifies it before the compact-support arrow is considered.
Source: supported-Hom comparison in Step 2
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
def supportComparison
    (K : DerivedCategory.Plus (Sheaf (𝔸(PUnit.{u + 1}; S)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    (realizePlus A E S).obj ((etaleSupport A S).obj K) ⟶
      (supported (coefficient A) S).obj ((realizePlus A E _).obj K) :=
  (closedSupportDerivedAdjunction (coefficient A)
    (AffineSpace.zeroSection PUnit.{u + 1} S)
    (AffineSpace.zeroSection PUnit.{u + 1} S).openComplement.ι
    (AffineSpace.zeroSection PUnit.{u + 1} S).range_eq_compl_range_openComplement_ι
    ).homEquiv _ _
    ((pushComparison A E S ((etaleSupport A S).obj K)).hom ≫
      (realizePlus A E _).map
        ((Etale.lowerStarClosedUpperShriekAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} A))
          (AffineSpace.zeroSection PUnit.{u + 1} S)
          (AffineSpace.zeroSection PUnit.{u + 1} S).openComplement.ι
          (AffineSpace.zeroSection PUnit.{u + 1} S).range_eq_compl_range_openComplement_ι
          ).derivedPlus.counit.app K))

end AlgebraicGeometry.ProEtale.CondensedRing.GeometricOrigin.Finite

namespace AlgebraicGeometry.ProEtale.CondensedRing.GeometricOrigin.Finite
open FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
  [IsTopologicalRing A] [Finite A]
  (Ω : Type u) [Field Ω] [IsAlgClosed Ω]

/-- The shifted bounded-below finite etale line, retaining its exact antecedent.
Source: M=Lambda(1)[2] in Step 2
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
abbrev shiftedEtaleLine
    (F : Sheaf (𝔸(PUnit.{u + 1}; Spec (.of Ω))).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
  (shiftFunctor _ (2 : ℤ)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)

/-- The retained witness supplied by the actual comparison functor.
Source: def-weil-pbc-etale-origin-witness
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
def retainedWitness (T : Scheme.{u})
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    Scheme.FixedEtaleOriginWitness T (ULift.{u + 1} A)
      ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
        ).mapDerivedCategoryPlus.obj K) where
  complex := K
  iso := (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
    ).mapDerivedCategoryPlusCompatibility.symm.app K

/-- The etale map is literally excision in P1 followed by the proper-support kernel
inclusion, shifted by two and transported through the point sections equivalence.
Source: blueprint Step 2 (blueprint: lem-pur-geometric-origin-compact-comparison). -/
def etaleForget
    (F : Sheaf (𝔸(PUnit.{u + 1}; Spec (.of Ω))).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    ((etaleSupport A (Spec (.of Ω))).obj (shiftedEtaleLine A Ω F)).obj ⟶
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} (ULift.{u + 1} A))
        (Etale.P1CompactificationFibre.compactification (Spec (.of Ω)))).obj
          (shiftedEtaleLine A Ω F)).obj := by
  let S := Spec (.of Ω)
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let i := AffineSpace.zeroSection PUnit.{u + 1} S
  let H := Etale.closedUpperShriek B i i.openComplement.ι
  let G := Etale.rightDerivedGlobalSections B S
  let C := Etale.rightDerivedLowerShriekOfCompactification B
    (Etale.P1CompactificationFibre.compactification S)
  let K := shiftedEtaleLine A Ω F
  let L := (DerivedCategory.singleFunctor _ 0).obj F
  letI : G.IsEquivalence :=
    Etale.isEquivalence_rightDerivedGlobalSections_of_isEquivalence B S
  let kShift : K.obj ≅ (shiftFunctor _ (2 : ℤ)).obj L :=
    (DerivedCategory.Plus.ι.commShiftIso (2 : ℤ)).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≪≫
      (shiftFunctor _ (2 : ℤ)).mapIso
        ((DerivedCategory.Plus.singleFunctorιIso _ 0).app F)
  let source := G.mapIso (H.rightDerivedFunctorPlusCompatibility.app K) ≪≫
    (Etale.rightDerivedClosedUpperShriekCompIso B i).app K.obj ≪≫
    (Etale.rightDerivedSectionsWithSupport B i).mapIso kShift ≪≫
    ((Etale.rightDerivedSectionsWithSupport B i).commShiftIso (2 : ℤ)).app L
  let target := G.mapIso
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility B
        (Etale.P1CompactificationFibre.compactification S)).app K) ≪≫
    G.mapIso (C.mapIso kShift) ≪≫
    G.mapIso ((C.commShiftIso (2 : ℤ)).app L) ≪≫
    (G.commShiftIso (2 : ℤ)).app (C.obj L) ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      (Etale.P1CompactificationFibre.compactSupportComparison S (ULift.{u + 1} A) F).symm
  exact G.preimage (source.hom ≫
    (shiftFunctor _ (2 : ℤ)).map
      ((Etale.P1CompactificationFibre.excision S (ULift.{u + 1} A) F).hom ≫
        (Etale.P1CompactificationFibre.forgetSupport S (ULift.{u + 1} A)).app _) ≫
    target.inv)

/-- Compatibility with the retained etale-origin maps. The endpoint comparisons
are already defined from the closed counit and the specified open/proper comparison;
no endpoint isomorphism is selected to force this equation.
Source: finite comparison in Step 2
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
def Comparison (E : ∀ T : Scheme.{u}, Encoding A T)
    (F : Sheaf (𝔸(PUnit.{u + 1}; Spec (.of Ω))).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (M : D (coefficient A) (𝔸(PUnit.{u + 1}; Spec (.of Ω)))) : Prop :=
  Nonempty ((realizePlus A E _).obj (shiftedEtaleLine A Ω F) ≅ M) ∧
  ∀ e : (realizePlus A E _).obj (shiftedEtaleLine A Ω F) ≅ M,
    let β := supportComparison A E (Spec (.of Ω)) (shiftedEtaleLine A Ω F) ≫
      (supported (coefficient A) (Spec (.of Ω))).map e.hom
    IsIso β ∧
      β ≫ GeometricOrigin.map (coefficient A) (Spec (.of Ω)) M =
        (realize A E (Spec (.of Ω))).map (etaleForget A Ω F) ≫
          (compactComparison A E (Spec (.of Ω)) (shiftedEtaleLine A Ω F)).inv ≫
          (compact (coefficient A) (Spec (.of Ω))).map e.hom

end AlgebraicGeometry.ProEtale.CondensedRing.GeometricOrigin.Finite

namespace AlgebraicGeometry.ProEtale.CondensedRing.GeometricOrigin

variable (P : WeilConjectures.PurityFiniteSetting.{u})
  (Ω : Type u) [Field Ω] [algebraΩ : Algebra P.field.k Ω] [IsAlgClosed Ω]

/-- The actual shifted finite twist at every positive coefficient exponent n+1.
Source: def-coefficient-twists-detailed
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
abbrev finiteM (n : ℕ) :=
  (shiftFunctor _ (2 : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj
    (coefficientFiniteTwistOne P.coefficients.l P.extension
      (𝔸(PUnit.{u + 1}; Spec (.of Ω))) n))

/-- The actual shifted integral inverse-limit line.
Source: def-coefficient-twists-detailed
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
abbrev integralM :=
  (shiftFunctor _ (2 : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj
    (coefficientIntegralTwistOne P.coefficients.l P.extension
      (𝔸(PUnit.{u + 1}; Spec (.of Ω)))))

/-- The actual shifted rational scalar extension of the integral line.
Source: def-coefficient-twists-detailed
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
abbrev rationalM :=
  (shiftFunctor _ (2 : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj
    (coefficientRationalTwistOne P.coefficients.l P.extension
      (𝔸(PUnit.{u + 1}; Spec (.of Ω)))))

/-- The published finite-subextension-valued algebraic-closure coefficient line.
Source: def-coefficient-twists-detailed
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
abbrev qbarM :=
  (shiftFunctor _ (2 : ℤ)).obj
    (tateTwistDerived (𝔸(PUnit.{u + 1}; Spec (.of Ω))) P.coefficients.l 1)

/-- The finite clause uses the published positive-level quotient and its root line,
with the retained ordinary etale antecedent, for every normalized finite encoding.
Source: finite comparison in Step 2
(blueprint: lem-pur-geometric-origin-compact-comparison). -/
def finiteComparison (n : ℕ) : Prop :=
  let Q : WeilConjectures.PurityFiniteSetting.{u} :=
    { P with level := n + 1, level_pos := Nat.succ_le_succ (Nat.zero_le n) }
  let A := Q.Ring
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : Finite A := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  ∀ E : ∀ T : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A T,
    Finite.Comparison A Ω E
      (Scheme.finiteEtaleTateLine (𝔸(PUnit.{u + 1}; Spec (.of Ω)))
        Q.diagonalExponent Q.Coefficient Q.diagonalExponent_annihilates)
      (finiteM P Ω n)

include algebraΩ in
/-- The canonical proper-support-forgetting map is invertible for all four
coefficient choices, over every algebraically closed extension Omega/k.
Source: latest blueprint, rank-one Thom proof Step 2
(blueprint: lem-pur-geometric-origin-compact-comparison).
Proof: transpose the supported origin class through the closed-support adjunction.
Naturality identifies its image under this precise map with the compact origin
class. At finite coefficients, the etale excision calculation sends the supported
Kummer boundary to minus the hyperplane class, a basis of Hc^2; the other compact
cohomology groups vanish. Full faithfulness on retained etale origins and exact
sections on the algebraically closed etale point give the derived isomorphism.
For integral coefficients the endpoints are constructible, finite-Tor and derived
complete over this finite-CD base. Reduction modulo the uniformizer identifies
the actual counit maps; derived Nakayama gives invertibility. Scalar extension
then gives the rational and algebraic-closure cases. This does not assert a tower
comparison or a scalar-exchange isomorphism as an additional conclusion. -/
theorem geometric_origin_compact_comparison :
    (∀ n : ℕ, IsIso (map (twistFiniteRing P.coefficients.l P.extension n)
      (Spec (.of Ω)) (finiteM P Ω n))) ∧
    IsIso (map (twistIntegralRing P.coefficients.l P.extension)
      (Spec (.of Ω)) (integralM P Ω)) ∧
    IsIso (map (twistRationalRing P.coefficients.l P.extension)
      (Spec (.of Ω)) (rationalM P Ω)) ∧
    IsIso (map (Profinite.padicAlgClRingObj P.coefficients.l)
      (Spec (.of Ω)) (qbarM P Ω)) ∧
    (∀ n : ℕ, finiteComparison P Ω n) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.GeometricOrigin
