/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.Paper.EtaleOriginDerivedCategory
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons

import Sheaf.AlgebraicGeometry.CompactifiableOverField
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.Paper.CompactificationCoherence
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.FiniteDirectImageComposition
import Sheaf.Paper.RefinementComparisonIsomorphism
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
/-!
# Canonical compact-support composition on the etale-origin class

Source: blueprint thm-sf-comp-composition, construction and coherence paragraphs;
Stacks Project, Tags 0F7J and 0F7K (blueprint: thm-sf-comp-composition).
The comparison is transported from the specified etale compositor. Full faithfulness
makes it natural for all ambient morphisms, independently of retained witnesses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
  [QuasiCompact f] [QuasiCompact g]

/-- Compact support restricted to the full bounded-below etale-origin class.
Source: blueprint thm-sf-comp-composition, first paragraph
(blueprint: thm-sf-comp-composition). -/
def originCompactSupport :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory ⥤
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y).FullSubcategory :=
  ObjectProperty.lift _
    ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (fun K ↦ K.property.rightDerivedLowerShriek_obj f)

/-- The ordered etale model of the compositor, using the actual compact-support
comparison, bounded-below compatibility, and the canonical etale compositor.
Source: blueprint thm-sf-comp-composition, proof steps 2 and 7
(blueprint: thm-sf-comp-composition). -/
def originCompositionModel :
    comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X ⋙
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ≅
    comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X ⋙
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g) :=
  Functor.isoWhiskerRight (compactSupportSiteComparison A (HasCompactification.compactification f))
      (rightDerivedLowerShriek _ g) ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).symm
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        rightDerivedLowerShriek _ g) ≪≫
    Functor.isoWhiskerLeft (Etale.rightDerivedLowerShriekPlus _ f)
      (compactSupportSiteComparison A (HasCompactification.compactification g)) ≪≫
    Functor.isoWhiskerLeft (Etale.rightDerivedLowerShriekPlus _ f)
      (Functor.isoWhiskerRight
        (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) g).symm
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory) ≪≫
    Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekPlusCompIso A f g)
      (DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory) ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (f ≫ g))
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory ≪≫
    (compactSupportSiteComparison A (HasCompactification.compactification (f ≫ g))).symm

/-- Descend the specified model along the canonical etale-origin equivalence.
This preimage is unique, rather than an arbitrary choice of a natural isomorphism.
Source: blueprint thm-sf-comp-composition, witness conjugation in proof step 2
(blueprint: thm-sf-comp-composition). -/
def originCompositionAmbient :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ≅
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g) :=
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso
    (originCompositionModel A f g)

/-- The canonical natural isomorphism alpha on the full origin class. Its homs are
all ambient derived morphisms, so changing or forgetting witnesses does not affect it.
Source: blueprint thm-sf-comp-composition, displayed isomorphism
(blueprint: thm-sf-comp-composition). -/
def originComposition :
    originCompactSupport A f ⋙ originCompactSupport A g ≅ originCompactSupport A (f ≫ g) :=
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).fullyFaithfulι
  (H.whiskeringRight _).preimageIso (originCompositionAmbient A f g)

/-- Canonical identity comparison, transported from the ordinary etale identity.
Source: blueprint thm-sf-comp-composition, identity convention
(blueprint: thm-sf-comp-composition). -/
def originCompactSupportId (T : Scheme.{u}) :
    originCompactSupport A (𝟙 T) ≅ 𝟭 _ :=
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) T
  let ν := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let model := compactSupportSiteComparison A (HasCompactification.compactification (𝟙 T)) ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (𝟙 T)).symm ν ≪≫
    Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekPlusId A T)
      (DerivedCategory.Plus.ι ⋙ ν)
  let ambient : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 T) ≅
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).ι :=
    (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso model
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).fullyFaithfulι
  (H.whiskeringRight _).preimageIso ambient

/-- Equality transport for the chosen compact-support functors.
Source: blueprint thm-sf-comp-composition, coherent identifications
(blueprint: thm-sf-comp-composition). -/
def originCompactSupportCongr {f' : X ⟶ Y} [HasCompactification f'] (h : f = f') :
    originCompactSupport A f ≅ originCompactSupport A f' :=
  h ▸ Iso.refl _

/-- The canonical compositor is the identity when its first morphism is an identity.
Source: blueprint thm-sf-comp-composition, unit clause
(blueprint: thm-sf-comp-composition).
Proof: precompose with the etale-origin equivalence, substitute the defining model,
and cancel inverse comparison maps. The equation becomes the ordinary etale unit law.
Full faithfulness then reflects the equality; all ambient morphisms are retained. -/
theorem originComposition_id_left [HasCompactification (𝟙 X ≫ f)] :
    (originComposition A (𝟙 X) f).hom =
      Functor.whiskerRight (originCompactSupportId A X).hom _ ≫
        (Functor.leftUnitor _).hom ≫
          (originCompactSupportCongr A f (Category.id_comp f).symm).hom := by
  sorry

/-- The canonical compositor is the identity when its second morphism is an identity.
Source: blueprint thm-sf-comp-composition, unit clause
(blueprint: thm-sf-comp-composition).
Proof: expand the model after precomposition with the comparison equivalence. Cancel
adjacent comparisons, apply the etale right-unit equation, and reflect equality by
full faithfulness. This is independent of any choice of etale-origin witness. -/
theorem originComposition_id_right [HasCompactification (f ≫ 𝟙 Y)] :
    (originComposition A f (𝟙 Y)).hom =
      Functor.whiskerLeft _ (originCompactSupportId A Y).hom ≫
        (Functor.rightUnitor _).hom ≫
          (originCompactSupportCongr A f (Category.comp_id f).symm).hom := by
  sorry

/-- Associativity with the specified associator and equality transport.
Source: blueprint thm-sf-comp-composition, associativity clause
(blueprint: thm-sf-comp-composition).
Proof: expand every model after the fully faithful etale-origin equivalence.
Comparison composition coherence cancels the intermediate site comparisons. Both
remaining expressions are the etale associativity equation, conjugated by the same
end comparisons. Reflect the equality using full faithfulness. -/
theorem originComposition_assoc {T : Scheme.{u}} (h : Z ⟶ T)
    [HasCompactification h] [HasCompactification (g ≫ h)]
    [HasCompactification ((f ≫ g) ≫ h)] [HasCompactification (f ≫ g ≫ h)]
    [QuasiCompact h] :
    Functor.whiskerRight (originComposition A f g).hom (originCompactSupport A h) ≫
        (originComposition A (f ≫ g) h).hom ≫
        (originCompactSupportCongr A ((f ≫ g) ≫ h) (Category.assoc f g h)).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (originCompactSupport A f) (originComposition A g h).hom ≫
          (originComposition A f (g ≫ h)).hom := by
  sorry

/-- The canonical fixed-scalar presentation of a retained origin witness.
Source: blueprint thm-sf-comp-composition, witnessed domain
(blueprint: thm-sf-comp-composition). -/
def originWitnessFixedAmbient (T : Scheme.{u})
    [TopologicalSpace A] [DiscreteTopology A] :
    EtaleOriginDerivedCategory T A ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :=
  letI : (finiteCoefficientRealization T A).asEquivalence.inverse.Additive :=
    @Equivalence.inverse_additive _ _ _ _ _ _
      (finiteCoefficientRealization T A).asEquivalence
        (finiteCoefficientRealization_additive T A)
  etaleOriginForgetful T A ⋙
    (finiteCoefficientRealization T A).asEquivalence.inverse.mapDerivedCategory

/-- The retained etale witness remains an origin witness after the canonical
coefficient equivalence; this supplies the full-subcategory lift.
Source: blueprint thm-sf-comp-composition, coefficient transport
(blueprint: thm-sf-comp-composition).
Proof: apply the exact inverse coefficient equivalence to the retained alpha.
The unit of that equivalence identifies its composite with coefficient realization
with the identity. The resulting alpha is precisely an isomorphism from the
comparison inverse image of the same bounded-below etale L to the transported K. -/
theorem originWitnessFixed_property (T : Scheme.{u})
    [TopologicalSpace A] [DiscreteTopology A] (K : EtaleOriginDerivedCategory T A) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T
      ((originWitnessFixedAmbient A T).obj K) := by
  sorry

/-- Forget the witness after canonical coefficient transport, without discarding any
ambient morphisms. Source: blueprint thm-sf-comp-composition, witnessed domain
(blueprint: thm-sf-comp-composition). -/
def originWitnessFixed (T : Scheme.{u}) [TopologicalSpace A] [DiscreteTopology A] :=
  ObjectProperty.lift _ (originWitnessFixedAmbient A T)
    (fun K ↦ originWitnessFixed_property A T K)

/-- Alpha on the recorded witness-retaining category. Its components are the same
ambient alpha components, so the identity between two witnesses identifies them.
Source: blueprint thm-sf-comp-composition, independence of the witness
(blueprint: thm-sf-comp-composition). -/
def originCompositionWitnessed [TopologicalSpace A] [DiscreteTopology A] :=
  Functor.isoWhiskerLeft (originWitnessFixed A X) (originCompositionAmbient A f g)

end AlgebraicGeometry.ProEtale
