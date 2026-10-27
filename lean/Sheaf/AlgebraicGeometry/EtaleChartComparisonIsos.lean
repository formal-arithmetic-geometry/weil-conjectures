/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.AlgebraicGeometry.FiniteRootSiteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import Sheaf.CategoryTheory.DerivedCategory.ResolvingAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalars

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat


/-! # Canonical scalar and chart comparisons between etale and pro-etale sites

Source: Stacks Project, proetale.tex, Tag 0GLZ; sites-cohomology.tex,
Tags 06YY, 0D6D and 07A4; the Charts paragraph of det-sp-reduction-exceptional
(blueprint: lem-sp-etale-chart-comparison-isos).

The inverse images below are the ordinary derived inverse images. Tensor and
shift comparisons are the existing normalized derived comparisons. Finite roots
and their scalar extensions use the recorded same-unit root comparison.
-/

@[expose] public noncomputable section

set_option Elab.async true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorCompNatIso
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryNatIso
  CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.leftDerivedFunctorCounit
  CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.singleFunctorCompLeftDerivedFunctorIso
  CategoryTheory.Functor.leftDerivedFunctorCompIso
  CategoryTheory.Functor.leftDerivedFunctorNatIso

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
  CategoryTheory.MonoidalCategory Opposite


namespace CategoryTheory


variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]

private instance sheafSmallColimits (J : GrothendieckTopology C)
    (R : Type (u + 1)) [CommRing R] :
    HasColimitsOfSize.{0, 0} (Sheaf J (ModuleCat.{u + 1} R)) :=
  ⟨fun _ ↦ Sheaf.instHasColimitsOfShape⟩

/-- Sheafified balanced extension of constant scalars, with the new ring acting on
its tensor factor. Source: Stacks, Tags 03EK and 06YY
(blueprint: lem-sp-etale-chart-comparison-isos). -/
def fixedCoefficientScalarExtension (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B) :
    Sheaf J (ModuleCat.{u + 1} A) ⥤ Sheaf J (ModuleCat.{u + 1} B) :=
  Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f)

/-- Additivity follows from the actual scalar-extension/restriction adjunction.
Source: Stacks, Tag 06YY (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance fixedCoefficientScalarExtension_additive (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B) :
    (fixedCoefficientScalarExtension J f).Additive :=
  (Sheaf.adjunction J
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f)).left_adjoint_additive

private theorem fixedExtension_preservesKFlat (J : GrothendieckTopology C)
    {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    (fixedCoefficientScalarExtension J φ).PreservesKFlatQuasiIso := by
  classical
  let E := fixedCoefficientScalarExtension J φ
  let U := Sheaf.restrictScalars J φ
  let adj : E ⊣ U :=
    Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)
  have : E.Additive := adj.left_adjoint_additive
  have : PreservesLimitsOfSize.{0, 0} U := adj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits U := inferInstance
  have : PreservesColimitsOfSize.{0, 0} U :=
    (Sheaf.restrictCoextendScalarsAdj J φ).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits U := inferInstance
  let _ := φ.toAlgebra
  let X := (constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R S)
  let e : E ⋙ U ≅ tensorRight X := Sheaf.extendScalarsCompRestrictScalarsIso J R S
  have hU : U.Faithful := inferInstance
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (ModuleCat.{u + 1} R)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{0, 0} (Sheaf J (ModuleCat.{u + 1} R)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have : HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} R)) :=
    ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩
  have : E.PreservesKFlatQuasiIso := by
    apply CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'
    intro K hK hKa
    have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa X
    have hEU := ht.of_iso
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app K).symm
    have hUK : ((U.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
      hEU.of_iso ((CategoryTheory.Functor.mapHomologicalComplexCompIso
        (Iso.refl (E ⋙ U)) (.up ℤ)).app K)
    intro n
    exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (hUK n)
  infer_instance

/-- Everywhere-defined ordinary derived scalar extension. Source: Stacks, Tags
06YS, 06YT and 06YY (blueprint: lem-sp-etale-chart-comparison-isos).
Proof: resolve by flat-term K-flat complexes (06YS). Restricted back to A,
ordinary extension is tensoring with the constant A-module B. The cone of a
quasi-isomorphism between K-flat complexes is acyclic K-flat, and remains
acyclic after this tensor (06YT). Therefore extension descends along these
resolutions. The resolving-class construction gives the pointwise universal
left-derived pair (06YY), with its counit computing ordinary extension on
K-flat representatives. No flatness of B over A is used. -/
@[instance]
theorem fixedCoefficientScalarExtension_hasPointwiseLeftDerivedFunctor
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B) :
    ((fixedCoefficientScalarExtension J f).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
        (HomologicalComplex.quasiIso (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ)) := by
  let E := fixedCoefficientScalarExtension J f
  let U := Sheaf.restrictScalars J f
  let adj : E ⊣ U :=
    Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f)
  have : PreservesLimitsOfSize.{0, 0} U := adj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits U := inferInstance
  have : PreservesColimitsOfSize.{0, 0} U :=
    (Sheaf.restrictCoextendScalarsAdj J f).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits U := inferInstance
  have : E.PreservesKFlatQuasiIso := fixedExtension_preservesKFlat J f
  exact (Adjunction.exists_leftDerived_adjunction E U adj
    (HomologicalComplex.quasiIso (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ)).kFlat
    (fun K ↦ by
      obtain ⟨r⟩ := LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
        (Φ := (HomologicalComplex.quasiIso
          (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ)).localizerMorphismKFlat) K
      exact ⟨r.X₁.obj, r.w, r.X₁.property,
        (HomologicalComplex.mem_quasiIso_iff _).1 r.hw⟩)
    (fun g hK hL hg ↦ by
      let _ := hg
      exact E.quasiIso_mapHomologicalComplex_map_of_kFlat hK hL g)).1

attribute [local irreducible] fixedCoefficientScalarExtension

/-- The canonical total left derived extension, the universal right Kan extension
of ordinary extension followed by localization. Its universal property determines
it up to the unique comparison preserving its counit.
Source: Stacks, Tag 06YY (blueprint: lem-sp-etale-chart-comparison-isos). -/
def fixedCoefficientDerivedExtension (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B) :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)) :=
  ((fixedCoefficientScalarExtension J f).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q).totalLeftDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ))

/-- The universal counit of the displayed ordinary left derived extension.
Source: Stacks, Tag 06YY (blueprint: lem-sp-etale-chart-comparison-isos). -/
def fixedCoefficientDerivedExtensionCounit (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B) :
    DerivedCategory.Q ⋙ fixedCoefficientDerivedExtension J f ⟶
      (fixedCoefficientScalarExtension J f).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  ((fixedCoefficientScalarExtension J f).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q).totalLeftDerivedCounit DerivedCategory.Q
      (HomologicalComplex.quasiIso (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ))

attribute [local irreducible] fixedCoefficientDerivedExtension
  fixedCoefficientDerivedExtensionCounit


end CategoryTheory

namespace AlgebraicGeometry.ProEtale.EtaleChartComparison


/-- Ordinary etale coefficient modules. Source: Stacks, Tag 05RU
(blueprint: lem-sp-etale-chart-comparison-isos). -/
abbrev Et (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) : Type (u + 2) :=
  Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)

/-- Ordinary pro-etale coefficient modules. Source: Stacks, Tags 099R and 05RU
(blueprint: lem-sp-etale-chart-comparison-isos). -/
abbrev Pro (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) : Type (u + 2) :=
  Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)

/-- Existing left-exact etale sheafification at the fixed module universe.
Source: Stacks, 00WX (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance etSheafify (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    HasSheafify T.smallEtaleTopology (ModuleCat.{u + 1} R) := inferInstance

/-- Existing left-exact pro-etale sheafification at the fixed module universe.
Source: Stacks, 00WX (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance proSheafify (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R) := inferInstance

/-- Cache the right adjoint underlying etale sheafification.
Source: Stacks, 00WX (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance etWeakSheafify (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u + 1} R) := HasSheafify.isRightAdjoint

/-- Cache the right adjoint underlying pro-etale sheafification.
Source: Stacks, 00WX (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance proWeakSheafify (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R) :=
  HasSheafify.isRightAdjoint

/-- Existing small colimits, made explicit for the unbounded derived construction.
Source: Stacks, Tag 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance etSmallColimits (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (Et R T) := ⟨fun _ ↦ Sheaf.instHasColimitsOfShape⟩

/-- Existing small colimits in the pro-etale coefficient category.
Source: Stacks, Tag 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance proSmallColimits (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (Pro R T) := ⟨fun _ ↦ Sheaf.instHasColimitsOfShape⟩

/-- Cache the existing Abelian structure, without choosing a new category.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance etAbelian (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    Abelian (Et R T) := inferInstance

/-- Cache the existing Abelian structure, without choosing a new category.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance proAbelian (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    Abelian (Pro R T) := inferInstance

/-- Cache the existing IsGrothendieckAbelian.{u + 1} structure, without choosing a new category.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance etGroth (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Et R T) := inferInstance

/-- Cache the existing IsGrothendieckAbelian.{u + 1} structure, without choosing a new category.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance proGroth (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Pro R T) := inferInstance

/-- Cache the existing MonoidalPreadditive structure, without choosing a new category.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance etMonoidalPreadditive (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    MonoidalPreadditive (Et R T) := inferInstance

/-- Cache the existing MonoidalPreadditive structure, without choosing a new category.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance proMonoidalPreadditive (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    MonoidalPreadditive (Pro R T) := inferInstance

/-- Cache the existing SymmetricCategory structure, without choosing a new category.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance etSymmetricCategory (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    SymmetricCategory (Et R T) := inferInstance

/-- Cache the existing SymmetricCategory structure, without choosing a new category.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance proSymmetricCategory (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    SymmetricCategory (Pro R T) := inferInstance

/-- Cache the existing MonoidalClosed structure, without choosing a new category.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance etMonoidalClosed (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    MonoidalClosed (Et R T) := inferInstance

/-- Cache the existing MonoidalClosed structure, without choosing a new category.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance proMonoidalClosed (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    MonoidalClosed (Pro R T) := inferInstance

/-- Cache the existing functorial flat resolution structure.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance etHasFunctorialFlatResolution (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    CategoryTheory.Abelian.HasFunctorialFlatResolution (Et R T) := inferInstance

/-- Cache the existing functorial flat resolution structure.
Source: Stacks, 06YS (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance proHasFunctorialFlatResolution (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    CategoryTheory.Abelian.HasFunctorialFlatResolution (Pro R T) := inferInstance

/-- The exact comparison, localized at quasi-isomorphisms. Source: Stacks, 0GLZ
(blueprint: lem-sp-etale-chart-comparison-isos). -/
abbrev nu (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    DerivedCategory (Et R T) ⥤ DerivedCategory (Pro R T) :=
  (comparisonUpperStar (ModuleCat.{u + 1} R) T).leftDerivedFunctor

/-- Scheme inverse image on ordinary etale complexes. Source: Stacks, Tag 0D6D
(blueprint: lem-sp-etale-chart-comparison-isos). -/
abbrev etPull (R : Type (u + 1)) [CommRing R] {T T' : Scheme.{u}} (v : T' ⟶ T) :
    DerivedCategory (Et R T) ⥤ DerivedCategory (Et R T') :=
  (Etale.upperStar (ModuleCat.{u + 1} R) v).leftDerivedFunctor

/-- Scheme inverse image on ordinary pro-etale complexes. Source: Stacks, Tag 0D6D
(blueprint: lem-sp-etale-chart-comparison-isos). -/
abbrev proPull (R : Type (u + 1)) [CommRing R] {T T' : Scheme.{u}} (v : T' ⟶ T) :
    DerivedCategory (Pro R T) ⥤ DerivedCategory (Pro R T') :=
  (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v).leftDerivedFunctor

/-- The exact comparison on degree-zero sheaves. Source: Stacks 05RU.
(blueprint: lem-sp-etale-chart-comparison-isos). -/
def nuSingle (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    DerivedCategory.singleFunctor (Et R T) 0 ⋙ nu R T ≅
      comparisonUpperStar (ModuleCat.{u + 1} R) T ⋙
        DerivedCategory.singleFunctor (Pro R T) 0 :=
  Functor.singleFunctorCompLeftDerivedFunctorIso
    (comparisonUpperStar (ModuleCat.{u + 1} R) T)

/-- The etale inverse image on degree-zero sheaves. Source: Stacks 05RU.
(blueprint: lem-sp-etale-chart-comparison-isos). -/
def etSingle (R : Type (u + 1)) [CommRing R] {T T' : Scheme.{u}} (v : T' ⟶ T) :
    DerivedCategory.singleFunctor (Et R T) 0 ⋙ etPull R v ≅
      Etale.upperStar (ModuleCat.{u + 1} R) v ⋙ DerivedCategory.singleFunctor (Et R T') 0 :=
  Functor.singleFunctorCompLeftDerivedFunctorIso (Etale.upperStar (ModuleCat.{u + 1} R) v)

/-- The pro-etale inverse image on degree-zero sheaves. Source: Stacks 05RU.
(blueprint: lem-sp-etale-chart-comparison-isos). -/
def proSingle (R : Type (u + 1)) [CommRing R] {T T' : Scheme.{u}} (v : T' ⟶ T) :
    DerivedCategory.singleFunctor (Pro R T) 0 ⋙ proPull R v ≅
      AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v ⋙
        DerivedCategory.singleFunctor (Pro R T') 0 :=
  Functor.singleFunctorCompLeftDerivedFunctorIso
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v)

attribute [local irreducible] nuSingle etSingle proSingle

/-- Ordinary balanced scalar comparison, fixed by the commuting restriction square.
Both right adjoints restrict the same sections with the same A-action. Consequently
left-adjoint uniqueness gives the ordinary balanced-tensor map, in B-modules.
Source: Stacks, Tags 03EL and 06YY (blueprint: lem-sp-etale-chart-comparison-isos). -/
def scalarSheafIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :
    fixedCoefficientScalarExtension T.smallEtaleTopology f ⋙
        comparisonUpperStar (ModuleCat.{u + 1} B) T ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙
        fixedCoefficientScalarExtension (Scheme.ProEt.topology T) f :=
  ((Sheaf.adjunction T.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f)).comp
      (comparisonAdjunction (ModuleCat.{u + 1} B) T)).leftAdjointUniq
    ((comparisonAdjunction (ModuleCat.{u + 1} A) T).comp
      (Sheaf.adjunction (Scheme.ProEt.topology T)
        (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f)))

attribute [local irreducible] scalarSheafIso

/-- The usual inverse-image square with its fixed coefficient source and target exposed.
Source: Stacks, 0GLZ (blueprint: lem-sp-etale-chart-comparison-isos). -/
def schemeSheafIso (R : Type (u + 1)) [CommRing R]
    {T T' : Scheme.{u}} (v : T' ⟶ T) :
    Etale.upperStar (ModuleCat.{u + 1} R) v ⋙
        comparisonUpperStar (ModuleCat.{u + 1} R) T' ≅
      comparisonUpperStar (ModuleCat.{u + 1} R) T ⋙
        AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v :=
  supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} R) v

attribute [local irreducible] schemeSheafIso

/-- The specified inverse-image square, exactly localized from the site square.
Source: Stacks, Tags 0GLZ and 0D6D (blueprint: lem-sp-etale-chart-comparison-isos). -/
def schemeIso (R : Type (u + 1)) [CommRing R] {T T' : Scheme.{u}} (v : T' ⟶ T) :
    etPull R v ⋙ nu R T' ≅ nu R T ⋙ proPull R v :=
  Functor.leftDerivedFunctorCompNatIso
    (comparisonUpperStar (ModuleCat.{u + 1} R) T)
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v)
    (Etale.upperStar (ModuleCat.{u + 1} R) v)
    (comparisonUpperStar (ModuleCat.{u + 1} R) T') (schemeSheafIso R v)

attribute [local irreducible] schemeIso

/-- The normalized finite-root scalar comparison already specified by its generators.
The theorem determines its map uniquely: each local root goes to the same unit and
its scalar factor is unchanged. Source: Stacks, Tags 0GLZ and 03EL
(blueprint: lem-sp-etale-chart-comparison-isos). -/
def rootIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).obj
        (Scheme.finiteEtaleTateLine T N R hR) ≅
      Scheme.finiteRootProTensor R N hN hR T :=
  Classical.choose (Scheme.finiteRootSiteComparison R) N hN hR T hT

/-- Nonnegative powers of the actual pro-etale root tensor, with constant unit in degree zero.
Source: Stacks, Section 03PK and Tag 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def proTwist (R : Type (u + 1)) [CommRing R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (T : Scheme.{u}) : ℕ → Pro R T
  | 0 => 𝟙_ _
  | 1 => Scheme.finiteRootProTensor R N hN hR T
  | c + 2 => proTwist R N hN hR T (c + 1) ⊗ Scheme.finiteRootProTensor R N hN hR T

/-- Iterated canonical tensor comparison, initialized by the unit and the same-unit root map.
Source: Stacks, Tags 03EL, 0GLZ and 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def twistSheafIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) : ∀ c : ℕ,
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).obj
        (Scheme.finiteEtaleTateTwist T N R hR c) ≅ proTwist R N hN hR T c
  | 0 => (Functor.Monoidal.εIso (comparisonUpperStar (ModuleCat.{u + 1} R) T)).symm
  | 1 => rootIso R N hN hR T hT
  | c + 2 =>
    (Functor.Monoidal.μIso (comparisonUpperStar (ModuleCat.{u + 1} R) T)
      (Scheme.finiteEtaleTateTwist T N R hR (c + 1))
      (Scheme.finiteEtaleTateLine T N R hR)).symm ≪≫
    (twistSheafIso R N hN hR T hT (c + 1) ⊗ᵢ rootIso R N hN hR T hT)

attribute [local irreducible] twistSheafIso rootIso

/-- The degree-zero finite-root comparison in the ordinary derived categories.
Source: Stacks, Tags 0GLZ and 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def twistLineIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (c : ℕ) :
    (nu R T).obj ((DerivedCategory.singleFunctor (Et R T) 0).obj
        (Scheme.finiteEtaleTateTwist T N R hR c)) ≅
      (DerivedCategory.singleFunctor (Pro R T) 0).obj (proTwist R N hN hR T c) :=
  (nuSingle R T).app (Scheme.finiteEtaleTateTwist T N R hR c) ≪≫
    (DerivedCategory.singleFunctor (Pro R T) 0).mapIso (twistSheafIso R N hN hR T hT c)

attribute [local irreducible] twistLineIso

/-- The canonical derived tensor comparison for the site inverse image.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def nuTensorRaw (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    (K M : DerivedCategory (Et R T)) :
    (nu R T).obj (K ⊗ M) ⟶ (nu R T).obj K ⊗ (nu R T).obj M :=
  ((Functor.leftDerivedTensorComparison
    (comparisonUpperStar (ModuleCat.{u + 1} R) T)).app K).app M

/-- Source identity exposing the tensor bifunctor's object formula.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos).
Proof: unfold Functor.leftDerivedDerivedTensor and curriedTensor; this is reflexivity. -/
theorem nuTensor_source (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    (K M : DerivedCategory (Et R T)) :
    ((comparisonUpperStar (ModuleCat.{u + 1} R) T).leftDerivedDerivedTensor.obj K).obj M =
      (nu R T).obj (K ⊗ M) := by
  rfl

/-- Target identity exposing the tensor bifunctor's object formula.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos).
Proof: unfold Functor.derivedTensorLeftDerived and the two whiskerings;
this is reflexivity. -/
theorem nuTensor_target (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    (K M : DerivedCategory (Et R T)) :
    ((comparisonUpperStar (ModuleCat.{u + 1} R) T).derivedTensorLeftDerived.obj K).obj M =
      (nu R T).obj K ⊗ (nu R T).obj M := by
  rfl

/-- The same canonical tensor arrow with its source and target written explicitly.
The transports are identities on the displayed bifunctor objects.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def nuTensor (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    (K M : DerivedCategory (Et R T)) :
    (nu R T).obj (K ⊗ M) ⟶ (nu R T).obj K ⊗ (nu R T).obj M :=
  nuTensorRaw R T K M


/-- The specified tensor comparison is invertible.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos).
Proof: use flat-term K-flat resolutions in both variables. Comparison inverse
image is exact and preserves flat objects; its canonical ordinary tensor map is
an isomorphism. Localization gives the inverse of nuTensor, independently of
resolutions, as in Functor.isIso_leftDerivedTensorComparison. -/
@[instance]
theorem nuTensor_isIso (R : Type (u + 1)) [CommRing R] [Finite R] (T : Scheme.{u})
    (K M : DerivedCategory (Et R T)) : IsIso (nuTensor R T K M) := by
  unfold nuTensor nuTensorRaw
  dsimp only [nu]
  infer_instance

attribute [local irreducible] nuTensor nuTensorRaw

/-- The specified derived twist comparison: the derived tensor comparison followed by
one tensor the finite-root comparison, including the constant-unit case c=0.
Source: Stacks, Tag 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def twistIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (c : ℕ) (L : DerivedCategory (Et R T)) :
    (nu R T).obj (L ⊗ (DerivedCategory.singleFunctor (Et R T) 0).obj
      (Scheme.finiteEtaleTateTwist T N R hR c)) ≅
    (nu R T).obj L ⊗ (DerivedCategory.singleFunctor (Pro R T) 0).obj
      (proTwist R N hN hR T c) :=
  asIso (nuTensor R T L ((DerivedCategory.singleFunctor (Et R T) 0).obj
    (Scheme.finiteEtaleTateTwist T N R hR c))) ≪≫
  (Iso.refl ((nu R T).obj L) ⊗ᵢ twistLineIso R N hN hR T hT c)

attribute [local irreducible] twistIso

/-- The canonical shift map, obtained from termwise inverse image with the signed
cochain differential. Source: Stacks, Tag 05RU
(blueprint: lem-sp-etale-chart-comparison-isos). -/
def shiftIso (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) (s : ℤ) :
    shiftFunctor (DerivedCategory (Et R T)) s ⋙ nu R T ≅
      nu R T ⋙ shiftFunctor (DerivedCategory (Pro R T)) s :=
  Functor.isoWhiskerLeft (shiftFunctor (DerivedCategory (Et R T)) s)
      (comparisonUpperStar (ModuleCat.{u + 1} R) T).leftDerivedFunctorIsoMapDerivedCategory ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.commShiftIso s ≪≫
    Functor.isoWhiskerRight
      (comparisonUpperStar (ModuleCat.{u + 1} R) T).leftDerivedFunctorIsoMapDerivedCategory.symm
      (shiftFunctor (DerivedCategory (Pro R T)) s)

/-- Pullback of finite etale tensor powers, using the actual root pullback and
canonical tensor comparisons. Source: Stacks, Tags 03EL and 03PK
(blueprint: lem-sp-etale-chart-comparison-isos). -/
def etTwistSheafPullback (R : Type (u + 1)) [CommRing R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤))) : ∀ c : ℕ,
    (Etale.upperStar (ModuleCat.{u + 1} R) v).obj
        (Scheme.finiteEtaleTateTwist T N R hR c) ≅
      Scheme.finiteEtaleTateTwist T' N R hR c
  | 0 => (Functor.Monoidal.εIso (Etale.upperStar (ModuleCat.{u + 1} R) v)).symm
  | 1 => (Scheme.finiteEtaleTwistPullbackData R N hN hR).c v hT hT' 1
  | c + 2 =>
    (Functor.Monoidal.μIso (Etale.upperStar (ModuleCat.{u + 1} R) v)
      (Scheme.finiteEtaleTateTwist T N R hR (c + 1))
      (Scheme.finiteEtaleTateLine T N R hR)).symm ≪≫
    (etTwistSheafPullback R N hN hR v hT hT' (c + 1) ⊗ᵢ
      (Scheme.finiteEtaleTwistPullbackData R N hN hR).c v hT hT' 1)

/-- Pullback of pro-etale powers through the specified inverse-image square.
The normalization laws below identify its first power with pullback of the same
unit and its zero power with the unit map.
Source: Stacks, Tags 0GLZ and 03EL (blueprint: lem-sp-etale-chart-comparison-isos). -/
def proTwistSheafPullback (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤))) (c : ℕ) :
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v).obj
        (proTwist R N hN hR T c) ≅ proTwist R N hN hR T' c :=
  (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v).mapIso
      (twistSheafIso R N hN hR T hT c).symm ≪≫
    (schemeSheafIso R v).symm.app (Scheme.finiteEtaleTateTwist T N R hR c) ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} R) T').mapIso
      (etTwistSheafPullback R N hN hR v hT hT' c) ≪≫
    twistSheafIso R N hN hR T' hT' c

attribute [local irreducible] proTwistSheafPullback

/-- The canonical derived tensor map for et-site scheme inverse image.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def etTensorRaw (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T) (K M : DerivedCategory (Et R T)) :
    (etPull R v).obj (K ⊗ M) ⟶ (etPull R v).obj K ⊗ (etPull R v).obj M :=
  ((Functor.leftDerivedTensorComparison
    (Etale.upperStar (ModuleCat.{u + 1} R) v)).app K).app M

/-- Source identity exposing the tensor bifunctor's object formula.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos).
Proof: unfold Functor.leftDerivedDerivedTensor and curriedTensor; this is reflexivity. -/
theorem etTensor_source (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (K M : DerivedCategory (Et R T)) :
    ((Etale.upperStar (ModuleCat.{u + 1} R) v).leftDerivedDerivedTensor.obj K).obj M =
      (etPull R v).obj (K ⊗ M) := by
  rfl

/-- Target identity exposing the tensor bifunctor's object formula.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos).
Proof: unfold Functor.derivedTensorLeftDerived and the two whiskerings;
this is reflexivity. -/
theorem etTensor_target (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (K M : DerivedCategory (Et R T)) :
    ((Etale.upperStar (ModuleCat.{u + 1} R) v).derivedTensorLeftDerived.obj K).obj M =
      (etPull R v).obj K ⊗ (etPull R v).obj M := by
  rfl

/-- The same canonical tensor arrow with its source and target written explicitly.
The transports are identities on the displayed bifunctor objects.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def etTensor (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (K M : DerivedCategory (Et R T)) :
    (etPull R v).obj (K ⊗ M) ⟶ (etPull R v).obj K ⊗ (etPull R v).obj M :=
  etTensorRaw R v K M


/-- The canonical et-site derived tensor map is invertible.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos).
Proof: resolve both factors by flat-term K-flat complexes. Exact inverse image
preserves their flatness and K-flatness; its ordinary balanced tensor comparison
is invertible. The two-variable derived universal property gives the stated
inverse, as in Functor.isIso_leftDerivedTensorComparison. -/
@[instance]
theorem etTensor_isIso (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T) (K M : DerivedCategory (Et R T)) :
    IsIso (etTensor R v K M) := by
  unfold etTensor etTensorRaw
  dsimp only [etPull]
  infer_instance

/-- Expose the existing preservation instance at the concrete coefficient category.
Source: Stacks, 0G7E (blueprint: lem-sp-etale-chart-comparison-isos). -/
instance proPreservesFlat (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T) :
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v).PreservesFlat :=
  (AlgebraicGeometry.ProEtale.upperStarPreservesFlat_moduleCat R).preservesFlat v

/-- The canonical derived tensor map for pro-site scheme inverse image.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def proTensorRaw (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T) (K M : DerivedCategory (Pro R T)) :
    (proPull R v).obj (K ⊗ M) ⟶ (proPull R v).obj K ⊗ (proPull R v).obj M :=
  ((Functor.leftDerivedTensorComparison
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v)).app K).app M

/-- Source identity exposing the tensor bifunctor's object formula.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos).
Proof: unfold Functor.leftDerivedDerivedTensor and curriedTensor; this is reflexivity. -/
theorem proTensor_source (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (K M : DerivedCategory (Pro R T)) :
    ((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v).leftDerivedDerivedTensor.obj
      K).obj M =
      (proPull R v).obj (K ⊗ M) := by
  rfl

/-- Target identity exposing the tensor bifunctor's object formula.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos).
Proof: unfold Functor.derivedTensorLeftDerived and the two whiskerings;
this is reflexivity. -/
theorem proTensor_target (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (K M : DerivedCategory (Pro R T)) :
    ((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v).derivedTensorLeftDerived.obj
      K).obj M =
      (proPull R v).obj K ⊗ (proPull R v).obj M := by
  rfl

/-- The same canonical tensor arrow with its source and target written explicitly.
The transports are identities on the displayed bifunctor objects.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def proTensor (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (K M : DerivedCategory (Pro R T)) :
    (proPull R v).obj (K ⊗ M) ⟶ (proPull R v).obj K ⊗ (proPull R v).obj M :=
  proTensorRaw R v K M


/-- The canonical pro-site derived tensor map is invertible.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos).
Proof: resolve both factors by flat-term K-flat complexes. Exact inverse image
preserves their flatness and K-flatness; its ordinary balanced tensor comparison
is invertible. The two-variable derived universal property gives the stated
inverse, as in Functor.isIso_leftDerivedTensorComparison. -/
@[instance]
theorem proTensor_isIso (R : Type (u + 1)) [CommRing R] [Finite R]
    {T T' : Scheme.{u}} (v : T' ⟶ T) (K M : DerivedCategory (Pro R T)) :
    IsIso (proTensor R v K M) := by
  unfold proTensor proTensorRaw
  dsimp only [proPull]
  infer_instance

attribute [local irreducible] etTensor etTensorRaw proTensor proTensorRaw

/-- Derived etale pullback of the twist, via the canonical derived tensor comparison.
Source: Stacks, Tag 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def etTwistPullback (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤)))
    (c : ℕ) (L : DerivedCategory (Et R T)) :
    (etPull R v).obj (L ⊗ (DerivedCategory.singleFunctor (Et R T) 0).obj
      (Scheme.finiteEtaleTateTwist T N R hR c)) ≅
    (etPull R v).obj L ⊗ (DerivedCategory.singleFunctor (Et R T') 0).obj
      (Scheme.finiteEtaleTateTwist T' N R hR c) :=
  asIso (etTensor R v L ((DerivedCategory.singleFunctor (Et R T) 0).obj
    (Scheme.finiteEtaleTateTwist T N R hR c))) ≪≫
  (Iso.refl ((etPull R v).obj L) ⊗ᵢ
    ((etSingle R v).app (Scheme.finiteEtaleTateTwist T N R hR c) ≪≫
      (DerivedCategory.singleFunctor (Et R T') 0).mapIso
        (etTwistSheafPullback R N hN hR v hT hT' c)))

/-- Derived pro-etale pullback of the twist, with its fixed root normalization.
Source: Stacks, Tag 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def proTwistPullback (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤)))
    (c : ℕ) (L : DerivedCategory (Pro R T)) :
    (proPull R v).obj (L ⊗ (DerivedCategory.singleFunctor (Pro R T) 0).obj
      (proTwist R N hN hR T c)) ≅
    (proPull R v).obj L ⊗ (DerivedCategory.singleFunctor (Pro R T') 0).obj
      (proTwist R N hN hR T' c) :=
  asIso (proTensor R v L ((DerivedCategory.singleFunctor (Pro R T) 0).obj
    (proTwist R N hN hR T c))) ≪≫
  (Iso.refl ((proPull R v).obj L) ⊗ᵢ
    ((proSingle R v).app (proTwist R N hN hR T c) ≪≫
      (DerivedCategory.singleFunctor (Pro R T') 0).mapIso
        (proTwistSheafPullback R N hN hR v hT hT' c)))

attribute [local irreducible] etTwistPullback proTwistPullback

/-- The localization comparison for the exact site inverse image, on cochain complexes.
Source: Stacks, Tags 0GLZ and 05RU (blueprint: lem-sp-etale-chart-comparison-isos). -/
def nuQFactor (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    DerivedCategory.Q ⋙ nu R T ≅
      (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q
      (comparisonUpperStar (ModuleCat.{u + 1} R) T).leftDerivedFunctorIsoMapDerivedCategory ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategoryFactors

attribute [local irreducible] nuQFactor

/-- The equation specifying the scalar comparison on every flat-term K-flat model.
The ordinary arrow is scalarSheafIso, so this retains its B-action and tensor normalization.
Source: Stacks, Tags 06YY and 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def ScalarModel {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u})
    (alpha : fixedCoefficientDerivedExtension T.smallEtaleTopology f ⋙ nu B T ⟶
      nu A T ⋙ fixedCoefficientDerivedExtension (Scheme.ProEt.topology T) f) : Prop :=
  ∀ P : CochainComplex (Et A T) ℤ,
    (HomologicalComplex.quasiIso (Et A T) (.up ℤ)).kFlat P →
    (∀ i : ℤ, exactFunctor _ _ (tensorRight (P.X i))) →
    IsIso ((fixedCoefficientDerivedExtensionCounit T.smallEtaleTopology f).app P) ∧
    IsIso ((fixedCoefficientDerivedExtensionCounit (Scheme.ProEt.topology T) f).app
      (((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapHomologicalComplex (.up ℤ)).obj P)) ∧
    alpha.app (DerivedCategory.Q.obj P) ≫
        (fixedCoefficientDerivedExtension (Scheme.ProEt.topology T) f).map
          ((nuQFactor A T).hom.app P) ≫
        (fixedCoefficientDerivedExtensionCounit (Scheme.ProEt.topology T) f).app
          (((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapHomologicalComplex (.up ℤ)).obj P) =
      (nu B T).map
          ((fixedCoefficientDerivedExtensionCounit T.smallEtaleTopology f).app P) ≫
        (nuQFactor B T).hom.app
          (((fixedCoefficientScalarExtension T.smallEtaleTopology f).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (scalarSheafIso f T) (.up ℤ)).hom.app P)

attribute [local irreducible] ScalarModel

/-- Naturality of the specified twist comparison on constructible finite-Tor objects.
Source: Stacks, 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def TwistNatural (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) : Prop :=
  ∀ (c : ℕ) (L M : DerivedCategory (Et R T)),
    Etale.DerivedCategory.boundedConstructibleFiniteTor R T L →
    Etale.DerivedCategory.boundedConstructibleFiniteTor R T M → ∀ a : L ⟶ M,
    (nu R T).map (a ⊗ₘ 𝟙 ((DerivedCategory.singleFunctor (Et R T) 0).obj
        (Scheme.finiteEtaleTateTwist T N R hR c))) ≫ (twistIso R N hN hR T hT c M).hom =
      (twistIso R N hN hR T hT c L).hom ≫
        ((nu R T).map a ⊗ₘ 𝟙 ((DerivedCategory.singleFunctor (Pro R T) 0).obj
          (proTwist R N hN hR T c)))

attribute [local irreducible] TwistNatural

/-- The derived pullback square for each twist, with its actual normalized arrows.
Source: Stacks, Tags 0GLZ and 07A4 (blueprint: lem-sp-etale-chart-comparison-isos). -/
def TwistPullbackLaw (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤))) : Prop :=
  ∀ L : DerivedCategory (Et R T),
    Etale.DerivedCategory.boundedConstructibleFiniteTor R T L → ∀ c : ℕ,
    (nu R T').map (etTwistPullback R N hN hR v hT hT' c L).hom ≫
        (twistIso R N hN hR T' hT' c ((etPull R v).obj L)).hom ≫
        ((schemeIso R v).hom.app L ⊗ₘ 𝟙 _) =
      (schemeIso R v).hom.app
          (L ⊗ (DerivedCategory.singleFunctor (Et R T) 0).obj
            (Scheme.finiteEtaleTateTwist T N R hR c)) ≫
        (proPull R v).map (twistIso R N hN hR T hT c L).hom ≫
        (proTwistPullback R N hN hR v hT hT' c ((nu R T).obj L)).hom

attribute [local irreducible] TwistPullbackLaw

/-- The integer modulus is invertible on every scheme over the given field.
Source: Stacks, Section 03PK; the field setting sk-def-sfb-dc-setting
(blueprint: lem-sp-etale-chart-comparison-isos).
Proof: a prime ell different from the characteristic p has nonzero image in k
(CharP.cast_ne_zero_of_ne_of_prime), hence is a unit. Its nth power is a unit.
Map it along k = Gamma(Spec k) to Gamma(T); ring homomorphisms preserve units
and natural-number casts. This also handles n=0 and the empty scheme. -/
theorem modulus_isUnit (k : Type u) [Field k] (p ell : ℕ) [CharP k p]
    (_hp : 0 < p) (hell : ell.Prime) (hne : ell ≠ p) (n : ℕ)
    (T : Over (Spec (CommRingCat.of k))) : IsUnit ((ell ^ n : ℕ) : Γ(T.left, ⊤)) := by
  have h : IsUnit (ell : k) :=
    isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime k hell hne.symm)
  let g : k →+* Γ(T.left, ⊤) :=
    T.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  simpa only [map_natCast, map_pow, Nat.cast_pow] using (h.pow n).map g

/-- The etale derived identity comparison. Source: Stacks, Tag 0D6D
(blueprint: lem-sp-etale-chart-comparison-isos). -/
def etId (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) : etPull R (𝟙 T) ≅ 𝟭 _ :=
  Functor.leftDerivedFunctorNatIso
    (Etale.upperStar (ModuleCat.{u + 1} R) (𝟙 T))
    (show Etale.upperStar (ModuleCat.{u + 1} R) (𝟙 T) ≅ 𝟭 (Et R T) from
      supportSiteEtaleComparisonId (ModuleCat.{u + 1} R) T) ≪≫
    (𝟭 (Et R T)).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The pro-etale derived identity comparison. Source: Stacks, Tag 0D6D
(blueprint: lem-sp-etale-chart-comparison-isos). -/
def proId (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) : proPull R (𝟙 T) ≅ 𝟭 _ :=
  Functor.leftDerivedFunctorNatIso
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) (𝟙 T))
    (show AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) (𝟙 T) ≅ 𝟭 (Pro R T) from
      supportSiteProEtaleComparisonId (ModuleCat.{u + 1} R) T) ≪≫
    (𝟭 (Pro R T)).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The etale derived composition comparison. Source: Stacks, Tag 0D6D
(blueprint: lem-sp-etale-chart-comparison-isos). -/
def etComp (R : Type (u + 1)) [CommRing R] {T T' T'' : Scheme.{u}}
    (v : T'' ⟶ T') (w : T' ⟶ T) : etPull R (v ≫ w) ≅ etPull R w ⋙ etPull R v :=
  Functor.leftDerivedFunctorNatIso
    (Etale.upperStar (ModuleCat.{u + 1} R) (v ≫ w))
    (show Etale.upperStar (ModuleCat.{u + 1} R) (v ≫ w) ≅
      Etale.upperStar (ModuleCat.{u + 1} R) w ⋙
        Etale.upperStar (ModuleCat.{u + 1} R) v from
      supportSiteEtaleComparisonComp (ModuleCat.{u + 1} R) v w) ≪≫
    Functor.leftDerivedFunctorCompIso
      (Etale.upperStar (ModuleCat.{u + 1} R) w) (Etale.upperStar (ModuleCat.{u + 1} R) v)

/-- The pro-etale derived composition comparison. Source: Stacks, Tag 0D6D
(blueprint: lem-sp-etale-chart-comparison-isos). -/
def proComp (R : Type (u + 1)) [CommRing R] {T T' T'' : Scheme.{u}}
    (v : T'' ⟶ T') (w : T' ⟶ T) : proPull R (v ≫ w) ≅ proPull R w ⋙ proPull R v :=
  Functor.leftDerivedFunctorNatIso
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) (v ≫ w))
    (show AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) (v ≫ w) ≅
      AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) w ⋙
        AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v from
      supportSiteProEtaleComparisonComp (ModuleCat.{u + 1} R) v w) ≪≫
    Functor.leftDerivedFunctorCompIso
      (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) w)
      (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v)

/-- Identity and composition coherence of the specified derived site square.
Source: Stacks, Tags 0GLZ and 0D6D (blueprint: lem-sp-etale-chart-comparison-isos). -/
def SchemeCoherent (R : Type (u + 1)) [CommRing R] (k : Type u) [Field k] : Prop :=
  (∀ (T : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (L : DerivedCategory (Et R T.left)),
    Etale.DerivedCategory.boundedConstructibleFiniteTor R T.left L →
    (schemeIso R (𝟙 T.left)).hom.app L ≫ (proId R T.left).hom.app ((nu R T.left).obj L) =
      (nu R T.left).map ((etId R T.left).hom.app L)) ∧
  (∀ (T T' T'' : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType T'.hom] [QuasiCompact T'.hom] [IsSeparated T'.hom]
    [LocallyOfFiniteType T''.hom] [QuasiCompact T''.hom] [IsSeparated T''.hom]
    (v : T'' ⟶ T') (w : T' ⟶ T) (L : DerivedCategory (Et R T.left)),
    Etale.DerivedCategory.boundedConstructibleFiniteTor R T.left L →
    (nu R T''.left).map ((etComp R v.left w.left).hom.app L) ≫
        (schemeIso R v.left).hom.app ((etPull R w.left).obj L) ≫
        (proPull R v.left).map ((schemeIso R w.left).hom.app L) =
      (schemeIso R (v.left ≫ w.left)).hom.app L ≫
        (proComp R v.left w.left).hom.app ((nu R T.left).obj L))

attribute [local irreducible] etId proId etComp proComp

/-- The pro-etale power pullbacks keep the root unit, the constant unit, and tensor recursion.
Source: Stacks, Tags 0GLZ and 03EL (blueprint: lem-sp-etale-chart-comparison-isos). -/
def RootPullbackNormalized (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤))) : Prop :=
  (proTwistSheafPullback R N hN hR v hT hT' 1).hom =
    Classical.choose (Classical.choose_spec (Scheme.finiteRootSiteComparison R)) N hN hR v ∧
  (proTwistSheafPullback R N hN hR v hT hT' 0).hom =
    Functor.OplaxMonoidal.η (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v) ∧
  ∀ c : ℕ, (proTwistSheafPullback R N hN hR v hT hT' (c + 2)).hom =
    Functor.OplaxMonoidal.δ (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} R) v)
        (proTwist R N hN hR T (c + 1)) (Scheme.finiteRootProTensor R N hN hR T) ≫
      ((proTwistSheafPullback R N hN hR v hT hT' (c + 1)).hom ⊗ₘ
        (proTwistSheafPullback R N hN hR v hT hT' 1).hom)

/-- Canonical scalar, scheme, finite-root twist, and signed-shift comparisons.
The isomorphisms schemeIso, twistIso and shiftIso are actual constructions above;
this statement supplies their coherence and the normalized scalar comparison.

Source: Stacks, Tags 0GLZ, 06YS, 06YY, 0G7E, 0D6D, 07A4 and 05RU;
Charts paragraph of det-sp-reduction-exceptional
(blueprint: lem-sp-etale-chart-comparison-isos).

Proof:
1. Restriction of scalars is exact and faithful. After restriction, sheafified
scalar extension is tensoring with the constant new coefficient module. K-flat
acyclicity therefore proves preservation of quasi-isomorphisms between K-flat
complexes, and the resolving-class derived adjunction gives the universal derived
extension. Its counit is invertible on K-flat complexes.
2. Apply the existing functorial flat resolution before comparison inverse image.
The source-library preservation theorem makes its comparison K-flat. The ordinary
balanced scalar square transports the extension quasi-isomorphism across exact
comparison. Counit naturality and derived-functor uniqueness give the scalar
isomorphism with precisely the equation in ScalarModel.
3. The support-site mate equals the source-library comparison on sections.
Localize its identity and composition equations, then conjugate by the canonical
isomorphisms between derived exact inverse images and exact localization. This
proves SchemeCoherent for all ordinary derived complexes.
4. The derived tensor comparison is invertible by the existing monoidal theorem.
Tensor naturality proves TwistNatural. At degree zero the site-square mate obeys
its monoidal unit equation; at degree one the given root square sends each root
to the same unit; higher degrees follow by tensoring those equations. These are
the three assertions of RootPullbackNormalized.
5. Compatibility of the single-degree embedding with derived composition and
natural isomorphisms gives the twist-line square. Paste it with the derived
monoidal square and tensor naturality to prove TwistPullbackLaw. The existing
shift isomorphism uses the signed cochain shift for every integer.
6. A prime different from the characteristic has nonzero image in the field,
so every power is a unit on each structural scheme. Assemble the comparisons. -/
theorem etale_chart_comparison_isos
    (k : Type u) [Field k] (p ell : ℕ) [CharP k p] (hp : 0 < p)
    (hell : ell.Prime) (hne : ell ≠ p)
    (T T' : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType T'.hom] [QuasiCompact T'.hom] [IsSeparated T'.hom]
    (v : T' ⟶ T) (A B : Type (u + 1)) [CommRing A] [Finite A]
    [CommRing B] [Finite B] (f : A →+* B) (n : ℕ)
    (hA : ((ell ^ n : ℕ) : A) = 0) (hB : ((ell ^ n : ℕ) : B) = 0) :
    (∃ alpha : fixedCoefficientDerivedExtension T.left.smallEtaleTopology f ⋙ nu B T.left ⟶
        nu A T.left ⋙ fixedCoefficientDerivedExtension (Scheme.ProEt.topology T.left) f,
      (∀ K : DerivedCategory (Et A T.left),
        Etale.DerivedCategory.boundedConstructibleFiniteTor A T.left K → IsIso (alpha.app K)) ∧
      ScalarModel f T.left alpha) ∧
    SchemeCoherent A k ∧ SchemeCoherent B k ∧
    TwistNatural A (ell ^ n) (Nat.pow_pos hell.pos) hA T.left
      (modulus_isUnit k p ell hp hell hne n T) ∧
    TwistNatural B (ell ^ n) (Nat.pow_pos hell.pos) hB T.left
      (modulus_isUnit k p ell hp hell hne n T) ∧
    RootPullbackNormalized A (ell ^ n) (Nat.pow_pos hell.pos) hA v.left
      (modulus_isUnit k p ell hp hell hne n T)
      (modulus_isUnit k p ell hp hell hne n T') ∧
    RootPullbackNormalized B (ell ^ n) (Nat.pow_pos hell.pos) hB v.left
      (modulus_isUnit k p ell hp hell hne n T)
      (modulus_isUnit k p ell hp hell hne n T') ∧
    TwistPullbackLaw A (ell ^ n) (Nat.pow_pos hell.pos) hA v.left
      (modulus_isUnit k p ell hp hell hne n T)
      (modulus_isUnit k p ell hp hell hne n T') ∧
    TwistPullbackLaw B (ell ^ n) (Nat.pow_pos hell.pos) hB v.left
      (modulus_isUnit k p ell hp hell hne n T)
      (modulus_isUnit k p ell hp hell hne n T') := by
  sorry

end AlgebraicGeometry.ProEtale.EtaleChartComparison
