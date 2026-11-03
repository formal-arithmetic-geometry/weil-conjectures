/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurSupportTriangle
public import WeilConjectures.AlgebraicGeometry.PurTriangleMeaning
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ConstructibleExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.ClosedFiniteTransport.ClosedFiniteAdjointCounitTransport
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import
  WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek

import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedClosedKernelAdjoint
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicClosedAmbient
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDerivedOpenAdjunction
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.ExactDerivedAdjunctionUnitShift
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenClosedTriangle
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.SixFunctors.ProEtale.BaseChange.ClosedLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence

/-!
# The intrinsic support-localization triangle and its finite exceptional comparison

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/`
`lem-pur-support-localization-triangle.md`, proof paragraphs 1--3, with the finite-domain
correction recorded in the DAG (blueprint: lem-pur-support-localization-triangle).

The ambient support functor is the right derived functor of the actual supported kernel.
The finite exceptional functor is the recorded comparison transport of the etale adjoint.
The latter comparison is asserted only on bounded-below inputs of etale origin.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open WeilConjectures

namespace AlgebraicGeometry.Scheme

/-- Identify the two recorded direct-image presentations using the actual adjunction
transpose of the constant-section map. No new scalar map is chosen.
Source: Stacks 03D6 and the canonical coefficient convention
(blueprint: lem-pur-support-localization-triangle). -/
def purSupportDirectImageIso {Y T : Scheme.{u}} (f : Y ⟶ T)
    (A : Type u) [CommRing A] [Finite A] :
    sfConstantModuleDirectImage f A ≅ proEtaleConstantModuleDirectImage f A := by
  apply eqToIso
  unfold sfConstantModuleDirectImage proEtaleRingModuleDirectImage
    proEtaleConstantModuleDirectImage
  have h : proEtaleRingDirectImageMap f (proEtaleConstantRing T A)
      (proEtaleConstantRing Y A) (sfConstantCoefficientIso f A) =
        proEtaleCoefficientDirectImageMap f A :=
    ((proEtaleSheafAdjunction f CommRingCat).homEquiv _ _).apply_symm_apply _
  rw [h]

/-- The direct-image realization comparison, obtained by deriving the preceding
coefficient identification and the recorded section-normalized realization comparison.
Source: Stacks 00YV and 07A5 (blueprint: lem-pur-support-localization-triangle). -/
def purSupportDerivedDirectImageIso {Y T : Scheme.{u}} (f : Y ⟶ T)
    (A : Type u) [CommRing A] [Finite A] :
    (sfConstantModuleDirectImage f A).rightDerivedFunctor ≅
      (sfIntrinsicDerivedEquivalence Y A).inverse ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor ⋙
          (sfIntrinsicDerivedEquivalence T A).functor :=
  Functor.rightDerivedFunctorNatIso (purSupportDirectImageIso f A) ≪≫
    (Functor.leftUnitor (proEtaleConstantDerivedDirectImage f A)).symm ≪≫
    Functor.isoWhiskerRight (sfIntrinsicDerivedEquivalence Y A).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sfIntrinsicDerivedDirectImageComparison f A)

/-- The ordinary etale exceptional adjunction with proper compact support identified
with closed direct image by the canonical proper comparison.
Source: blueprint proof paragraph 2; Stacks 04CA and 0G2C
(blueprint: lem-pur-support-localization-triangle). -/
def purSupportEtaleExceptionalAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (s : Z ⟶ X) [IsClosedImmersion s] [HasCompactification s] :
    (Etale.lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctor ⊣
      Etale.rightDerivedUpperShriek A s :=
  (Etale.rightDerivedUpperShriekAdjunction A s).ofNatIsoLeft
    (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) s)

/-- The fixed-scalar finite exceptional counit for a closed immersion. Its three factors
are the inverse closed comparison, the transported etale counit, and the comparison
adjunction counit. This is defined without an ambient exceptional adjunction.
Source: blueprint proof paragraph 2 and the closed finite counit transport
(blueprint: lem-pur-support-localization-triangle). -/
def purSupportFixedExceptionalCounit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X U : Scheme.{u}} (s : Z ⟶ X) [IsClosedImmersion s] [HasCompactification s]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range s.base) (Set.range j.base))
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctor.obj
      ((ProEtale.rightDerivedUpperShriek A s).obj K) ⟶ K := by
  letI := ProEtale.preservesFiniteColimits_lowerStar_of_isCompl (R := A) s j hPair
  exact
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctorIsoMapDerivedCategory.hom.app
        ((ProEtale.rightDerivedUpperShriek A s).obj K) ≫
      (ProEtale.ClosedFiniteTransport.closedComparison A s j hPair).inv.app _ ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((purSupportEtaleExceptionalAdjunction A s).counit.app _) ≫
      (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).counit.app K

/-- The ambient support-adjunction triangle with its prescribed counit and open unit.
The argument is its connecting arrow, not a choice of either adjunction map.
Source: blueprint displayed support triangle, proof paragraphs 1--2
(blueprint: lem-pur-support-localization-triangle). -/
def purSupportAdjunctionTriangle {Z X U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
    (A : Type u) [CommRing A] [Finite A]
    (adj : (sfConstantModuleDirectImage s A).rightDerivedFunctor ⊣
      (sfIntrinsicClosedUpperShriek s j A).rightDerivedFunctor)
    (K : proEtaleDerivedCategory X A)
    (δ : (sfConstantModuleDirectImage j A).rightDerivedFunctor.obj
        ((sfConstantModulePullback j A).mapDerivedCategory.obj K) ⟶
      ((sfConstantModuleDirectImage s A).rightDerivedFunctor.obj
        ((sfIntrinsicClosedUpperShriek s j A).rightDerivedFunctor.obj K))⟦(1 : ℤ)⟧) :
    Triangle (proEtaleDerivedCategory X A) :=
  Triangle.mk (adj.counit.app K)
    ((sfConstantModuleAdjunction j A).mapDerivedCategoryRightDerivedAdjunction.unit.app K) δ

variable (P : PurityFiniteSetting.{u})
variable {Z X : Scheme.{u}}
  [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable (s : Z ⟶ X) [IsClosedImmersion s]

/-- The recorded finite exceptional functor, expressed using the canonical realization
and the existing fixed-scalar finite functor. This only separates the comparison from
module realization; the underlying etale adjoint is unchanged.
Source: def-weil-exceptional-inverse-image, its finite displayed formula
(blueprint: lem-pur-support-localization-triangle). -/
def purSupportFiniteExceptionalModelIso :
    P.exceptionalInverseImage s ≅
      (sfIntrinsicDerivedEquivalence X P.Ring).inverse ⋙
        ProEtale.rightDerivedUpperShriek P.Coefficient s ⋙
          (sfIntrinsicDerivedEquivalence Z P.Ring).functor := by
  letI := (ProEtale.finiteCoefficientIntrinsicRealization_exact Z P.Ring).2.1
  letI := (ProEtale.finiteCoefficientIntrinsicRealization_exact Z P.Ring).2.2.1
  letI := (ProEtale.finiteCoefficientIntrinsicRealization_exact Z P.Ring).2.2.2
  exact Functor.isoWhiskerLeft (sfIntrinsicDerivedEquivalence X P.Ring).inverse
    (Functor.isoWhiskerLeft
      (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) X).rightDerivedFunctor
      (Functor.isoWhiskerLeft (Etale.rightDerivedUpperShriek P.Coefficient s)
        (Functor.mapDerivedCategoryCompIso
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z)
          (ProEtale.finiteCoefficientIntrinsicRealization Z P.Ring)))) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicDerivedEquivalence X P.Ring).inverse
      (Functor.isoWhiskerLeft
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) X).rightDerivedFunctor
        (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm)

/-- The canonical finite transported exceptional counit, in the intrinsic coefficient
category of the node. All identifications are the recorded coefficient realization,
closed direct-image comparison, proper comparison and adjunction counits.
Source: blueprint proof paragraph 2, closed finite adjoint counit transport
(blueprint: lem-pur-support-localization-triangle). -/
def purSupportFiniteExceptionalCounit {U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range s.base) (Set.range j.base))
    (K : proEtaleDerivedCategory X P.Ring) :
    (sfConstantModuleDirectImage s P.Ring).rightDerivedFunctor.obj
      ((P.exceptionalInverseImage s).obj K) ⟶ K :=
  (sfConstantModuleDirectImage s P.Ring).rightDerivedFunctor.map
      ((purSupportFiniteExceptionalModelIso P s).hom.app K) ≫
    (purSupportDerivedDirectImageIso s P.Ring).hom.app _ ≫
    (sfIntrinsicDerivedEquivalence X P.Ring).functor.map
      ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) s).rightDerivedFunctor.map
          ((sfIntrinsicDerivedEquivalence Z P.Ring).unitIso.inv.app _) ≫
        purSupportFixedExceptionalCounit P.Coefficient s j hPair
          ((sfIntrinsicDerivedEquivalence X P.Ring).inverse.obj K)) ≫
    (sfIntrinsicDerivedEquivalence X P.Ring).counitIso.hom.app K

/-- The finite exceptional-adjunction triangle with the actual transported counit
and open unit. Its boundary is supplied explicitly for comparison with the cone model.
Source: blueprint proof paragraph 2, finite etale-origin identification
(blueprint: lem-pur-support-localization-triangle). -/
def purSupportExceptionalTriangle {U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range s.base = (Set.range j.base)ᶜ)
    (K : proEtaleDerivedCategory X P.Ring)
    (δ : (sfConstantModuleDirectImage j P.Ring).rightDerivedFunctor.obj
        ((sfConstantModulePullback j P.Ring).mapDerivedCategory.obj K) ⟶
      ((sfConstantModuleDirectImage s P.Ring).rightDerivedFunctor.obj
        ((P.exceptionalInverseImage s).obj K))⟦(1 : ℤ)⟧) :
    Triangle (proEtaleDerivedCategory X P.Ring) :=
  Triangle.mk
    (purSupportFiniteExceptionalCounit P s j
      (by rw [hcomp]; exact isCompl_compl.symm) K)
    ((sfConstantModuleAdjunction j P.Ring).mapDerivedCategoryRightDerivedAdjunction.unit.app K) δ

end AlgebraicGeometry.Scheme
end
