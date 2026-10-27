/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.NormalizedInternalSupportScalars
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.Paper.ConstructibleAlgClTopologyComparison
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
public import Sheaf.Paper.OpenInternalKFlatMateNormalization
public import Sheaf.Paper.InternalSectionTotalComparison

/-! # Supported common finite-field comparison data

Source: blueprint main-20261015, direct-image stability proof (3), common-field obligation;
scalar-six pullback proof (1)--(3)
(blueprint: def-sfb-supported-common-field-scalar-data).

## Main definitions

* `commonField`, `ordinary`, `finiteModel`, `generator`: the fixed finite-field models.
* `alpha`, `alphaB`, `directB`: the prescribed comparison compositions.
* `ModelAssertions`: lisse models, normalized comparisons, units and section transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u u₁ u₂ v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.SupportedCommonField

variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [MonObj Λ''] [IsCommMonObj Λ'']

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The actual smallest common intermediate field, with finiteness supplied by Mathlib's
compositum theorem; it is not an arbitrary common overfield.
Source: direct-image stability proof (3), E_0=EF
(blueprint: def-sfb-supported-common-field-scalar-data). -/
abbrev commonField (E F : PadicAlgCl.FiniteIntermediateField ℓ) :
    PadicAlgCl.FiniteIntermediateField ℓ := ⟨E.1 ⊔ F.1, inferInstance⟩

/-- The continuous inclusion from a finite subfield into a larger finite subfield.
Source: direct-image stability proof (3), E to EF and F to EF
(blueprint: def-sfb-supported-common-field-scalar-data). -/
abbrev finiteInclusion {E A : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ A) :=
  Profinite.padicSubfieldRingObjMap.{u} ℓ h

/-- The continuous finite-stage coefficient inclusion into C.
Source: direct-image stability proof (3), A to C
(blueprint: def-sfb-supported-common-field-scalar-data). -/
abbrev toC (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ E

/-- The recorded inclusion from C into the full norm-continuous coefficient ring B.
Source: direct-image stability proof (3), c:C to B
(blueprint: def-sfb-supported-common-field-scalar-data). -/
abbrev toB := algClTopologyInclusion.{u} ℓ

/-- Ordinary scalar extension of a module to the fixed common finite field.
Source: direct-image stability proof (3), L_0 and M_0
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def ordinary {E A : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ A)
    (S : Scheme.{u}) (L : Modules (Profinite.continuousMapRingObj E) S) :
    Modules (Profinite.continuousMapRingObj A) S :=
  (Mod.extendScalars (coefficientMap (finiteInclusion ℓ h) S)).obj L

/-- The degree-zero supported object over the common finite field.
Source: direct-image stability proof (3), K and N
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def finiteModel {E A : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ A)
    {S X : Scheme.{u}} [IsNoetherian X] [TopologicalSpace.NoetherianSpace S]
    (a : S ⟶ X) [IsImmersion a] (L : Modules (Profinite.continuousMapRingObj E) S) :
    D (Profinite.continuousMapRingObj A) X :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((coefficientHeartLocallyClosedExtension (Profinite.continuousMapRingObj A)
      a inferInstance).obj (ordinary ℓ h S L))

/-- The supported C-object in the assertion, with its original finite field retained.
Source: direct-image stability proof (3), G and H
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def generator (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {S X : Scheme.{u}} [IsNoetherian X] [TopologicalSpace.NoetherianSpace S]
    (a : S ⟶ X) [IsImmersion a] (L : Modules (Profinite.continuousMapRingObj E) S) :
    D (Profinite.padicAlgClRingObj ℓ) X :=
  (support (Profinite.padicAlgClRingObj ℓ) a).obj
    ((scalar (toC ℓ E) S).obj ((DerivedCategory.singleFunctor _ 0).obj L))

/-- Equality transport between the existing scalar functors, retaining their ring-hom
instances by proof irrelevance. This is an equality eliminator, not a chosen comparison.
Source: scalar-six pullback proof (3)
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def scalarCongr (c d : Λ ⟶ Λ') [IsMonHom c] [IsMonHom d] (h : c = d)
    (X : Scheme.{u}) : scalar c X ≅ scalar d X := by
  subst d
  exact Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- Scalar reassociation from the original finite field to the common finite field,
followed by the canonical derived-to-ordinary comparison of its lisse module.
Source: scalar-six pullback proof (3), direct-image stability proof (3)
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def finiteReassociation {E A : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ A)
    (S : Scheme.{u}) (L : Modules (Profinite.continuousMapRingObj E) S)
    [IsIso (singleComparison (finiteInclusion ℓ h) S L)] :
    (scalar (toC ℓ E) S).obj ((DerivedCategory.singleFunctor _ 0).obj L) ≅
      (scalar (toC ℓ A) S).obj ((DerivedCategory.singleFunctor _ 0).obj (ordinary ℓ h S L)) :=
  (scalarCongr (toC ℓ E) (finiteInclusion ℓ h ≫ toC ℓ A)
    (Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl ℓ h).symm S).app _ ≪≫
    (tower (finiteInclusion ℓ h) (toC ℓ A) S).symm.app _ ≪≫
      (scalar (toC ℓ A) S).mapIso (asIso (singleComparison (finiteInclusion ℓ h) S L))

/-- The displayed alpha, constructed from the actual finite-field reassociation, support
comparison, and degree-zero support realization. The analogous beta uses its own field
and support, without identifying them.
Source: direct-image stability proof (3), normalized common-field obligation
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def alpha {E A : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ A)
    {S X : Scheme.{u}} [IsNoetherian X] [TopologicalSpace.NoetherianSpace S]
    (a : S ⟶ X) [IsImmersion a] (L : Modules (Profinite.continuousMapRingObj E) S)
    [IsIso (singleComparison (finiteInclusion ℓ h) S L)]
    (d : SupportComparison (toC ℓ A) a) :
    generator ℓ E a L ≅ (scalar (toC ℓ A) X).obj (finiteModel ℓ h a L) :=
  (support (Profinite.padicAlgClRingObj ℓ) a).mapIso (finiteReassociation ℓ h S L) ≪≫
    (supportComparison (toC ℓ A) a d.closedIso).symm.app _ ≪≫
      (scalar (toC ℓ A) X).mapIso
        (supportSingle (Profinite.continuousMapRingObj A) a (ordinary ℓ h S L))

/-- The B-comparison defined by applying J to alpha and the canonical A-C-B associator.
Source: scalar-six pullback proof (3), alpha_B and beta_B
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def alphaB {E A : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ A)
    {S X : Scheme.{u}} [IsNoetherian X] [TopologicalSpace.NoetherianSpace S]
    (a : S ⟶ X) [IsImmersion a] (L : Modules (Profinite.continuousMapRingObj E) S)
    [IsIso (singleComparison (finiteInclusion ℓ h) S L)]
    (d : SupportComparison (toC ℓ A) a) :
    (scalar (toB ℓ) X).obj (generator ℓ E a L) ≅
      (scalar (toC ℓ A ≫ toB ℓ) X).obj (finiteModel ℓ h a L) :=
  (scalar (toB ℓ) X).mapIso (alpha ℓ h a L d) ≪≫
    (tower (toC ℓ A) (toB ℓ) X).app _

/-- The original-field B-reassociation, using the same actual scalar towers.
Source: scalar-six pullback proof (3)
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def finiteReassociationB {E A : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ A)
    (S : Scheme.{u}) (L : Modules (Profinite.continuousMapRingObj E) S)
    [IsIso (singleComparison (finiteInclusion ℓ h) S L)] :
    (scalar (toC ℓ E ≫ toB ℓ) S).obj ((DerivedCategory.singleFunctor _ 0).obj L) ≅
      (scalar (toC ℓ A ≫ toB ℓ) S).obj
        ((DerivedCategory.singleFunctor _ 0).obj (ordinary ℓ h S L)) :=
  (tower (toC ℓ E) (toB ℓ) S).symm.app _ ≪≫
    (scalar (toB ℓ) S).mapIso (finiteReassociation ℓ h S L) ≪≫
      (tower (toC ℓ A) (toB ℓ) S).app _

/-- The direct supported B-comparison with the prescribed open and closed normalizations.
Source: direct-image stability proof (3), direct B-support identification
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def directB {E A : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ A)
    {S X : Scheme.{u}} [IsNoetherian X] [TopologicalSpace.NoetherianSpace S]
    (a : S ⟶ X) [IsImmersion a] (L : Modules (Profinite.continuousMapRingObj E) S)
    [IsIso (singleComparison (finiteInclusion ℓ h) S L)]
    (dB : SupportComparison (toC ℓ A ≫ toB ℓ) a)
    (dCB : SupportComparison (toB ℓ) a) :
    (scalar (toB ℓ) X).obj (generator ℓ E a L) ≅
      (scalar (toC ℓ A ≫ toB ℓ) X).obj (finiteModel ℓ h a L) :=
  (supportComparison (toB ℓ) a dCB.closedIso).app _ ≪≫
    (support (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) a).mapIso
      ((tower (toC ℓ E) (toB ℓ) S).app _ ≪≫ finiteReassociationB ℓ h S L) ≪≫
    (supportComparison (toC ℓ A ≫ toB ℓ) a dB.closedIso).symm.app _ ≪≫
      (scalar (toC ℓ A ≫ toB ℓ) X).mapIso
        (supportSingle (Profinite.continuousMapRingObj A) a (ordinary ℓ h S L))

/-- The actual displayed scalar-unit equation, after restriction to the common finite
coefficient ring. The right side is the independently defined coefficient-induced map.
Source: direct-image stability proof (3), displayed unit compatibility
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def UnitEquation {E A : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ A)
    {S X : Scheme.{u}} [IsNoetherian X] [TopologicalSpace.NoetherianSpace S]
    (a : S ⟶ X) [IsImmersion a] (L : Modules (Profinite.continuousMapRingObj E) S)
    [IsIso (singleComparison (finiteInclusion ℓ h) S L)]
    (d : SupportComparison (toC ℓ A) a) : Prop :=
  (restrict (toC ℓ A) X).map
      ((alpha ℓ h a L d).inv ≫
        (adj (toB ℓ) X).unit.app (generator ℓ E a L) ≫
          (restrict (toB ℓ) X).map (alphaB ℓ h a L d).hom) ≫
    (restrictComp (toC ℓ A) (toB ℓ) X).hom.app
      ((scalar (toC ℓ A ≫ toB ℓ) X).obj (finiteModel ℓ h a L)) =
    inducedMap (toC ℓ A) (toB ℓ) X (finiteModel ℓ h a L)

/-- Successive scalar units become the direct unit under the specified balanced tower.
Source: scalar-six pullback proof (3), insertion of the two scalar units
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def UnitTower {A B C : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    [MonObj C] [IsCommMonObj C] (e : A ⟶ B) [IsMonHom e]
    (c : B ⟶ C) [IsMonHom c] (X : Scheme.{u}) : Prop :=
  ∀ V : D A X,
    (adj e X).unit.app V ≫
      (restrict e X).map ((adj c X).unit.app ((scalar e X).obj V)) ≫
      (restrictComp e c X).hom.app ((scalar c X).obj ((scalar e X).obj V)) ≫
      (restrict (e ≫ c) X).map ((tower e c X).hom.app V) =
    (adj (e ≫ c) X).unit.app V

/-- The actual equivalence to section-ring modules, localized termwise.
Source: scalar-six pullback proof (1), internal/section transport
(blueprint: def-sfb-supported-common-field-scalar-data). -/
abbrev forward (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] (X : Scheme.{u}) :=
  ModuleObjectRingedComparison.forward A X

/-- Closed section direct image has the exactness of its internal counterpart.
Only a proof of a property is selected.
Source: scalar-six pullback proof (2), internal module operations transport
(blueprint: def-sfb-supported-common-field-scalar-data). -/
instance sectionClosedExact
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {Z X : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesFiniteColimits (InternalModuleOperations.lowerStar A i) :=
  ((InternalModuleOperations.internal_module_operations_transport A).2.2.2.1 i).2.2.2.mp
    inferInstance

/-- Open section extension has the exactness of its internal counterpart.
Source: scalar-six pullback proof (2), internal module operations transport
(blueprint: def-sfb-supported-common-field-scalar-data). -/
instance sectionOpenExact
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {S X : Scheme.{u}}
    (j : S ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteLimits (InternalModuleOperations.extension A j) :=
  ((InternalModuleOperations.internal_module_operations_transport A).2.2.2.2.1 j).1.mp
    inferInstance

/-- Additivity of closed section direct image, obtained from its finite-limit property.
Source: scalar-six pullback proof (2), canonical section operations
(blueprint: def-sfb-supported-common-field-scalar-data). -/
instance sectionClosedAdditive
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (InternalModuleOperations.lowerStar A i).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Additivity of open section extension, obtained from its finite-limit property.
Source: scalar-six pullback proof (2), canonical section operations
(blueprint: def-sfb-supported-common-field-scalar-data). -/
instance sectionOpenAdditive
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {S X : Scheme.{u}}
    (j : S ⟶ X) [IsOpenImmersion j] :
    (InternalModuleOperations.extension A j).Additive :=
  Functor.additive_of_preserves_binary_products _

set_option backward.isDefEq.respectTransparency false in
/-- The actual section support functor, localizing the same open and closed factors.
Source: scalar-six pullback proof (2), transport of support extension
(blueprint: def-sfb-supported-common-field-scalar-data). -/
abbrev sectionSupport (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {S X : Scheme.{u}} [IsNoetherian X]
    [TopologicalSpace.NoetherianSpace S] (a : S ⟶ X) [IsImmersion a] :=
  (InternalModuleOperations.extension A a.toImage).mapDerivedCategory ⋙
    (InternalModuleOperations.lowerStar A a.imageι).mapDerivedCategory

set_option backward.isDefEq.respectTransparency false in
/-- Localize the identity-on-sections closed comparison and the adjunction-normalized
open comparison, then compose them through the closure. This fixes the support comparison
rather than asserting existence of an unspecified isomorphism.
Source: scalar-six pullback proof (2)
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def sectionSupportComparison
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {S X : Scheme.{u}} [IsNoetherian X]
    [TopologicalSpace.NoetherianSpace S] (a : S ⟶ X) [IsImmersion a] :
    support A a ⋙ forward A X ≅ forward A S ⋙ sectionSupport A a :=
  letI := sectionClosedAdditive A a.imageι
  letI := sectionOpenAdditive A a.toImage
  letI := sectionClosedExact A a.imageι
  letI := sectionOpenExact A a.toImage
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (InternalModuleOperations.lowerComparison A a.imageι) ≪≫
          Functor.mapDerivedCategoryCompIso _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (InternalModuleOperations.openComparison A a.toImage) ≪≫
          Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _

/-- The existing localization of the identity-on-sections restriction square.
Source: scalar-six pullback proof (1), OpenInternalScalar.restrictionComparison
(blueprint: def-sfb-supported-common-field-scalar-data). -/
abbrev sectionRestriction (c : Λ ⟶ Λ') [IsMonHom c] (X : Scheme.{u}) :=
  OpenInternalScalar.restrictionComparison.{u + 1, u, u + 1, u + 1}
    (Scheme.ProEt.topology X) (coefficientMap c X)

/-- Reuse the normalized scalar transport for the actual fixed internal adjunction.
This is the published interface, not a second scalar comparison structure.
Source: scalar-six pullback proof (1), OpenInternalScalar.scalarTransport
(blueprint: def-sfb-supported-common-field-scalar-data). -/
abbrev SectionScalarComparison (c : Λ ⟶ Λ') [IsMonHom c] (X : Scheme.{u}) :=
  OpenInternalScalar.ScalarTransport.{u + 1, u, u + 1, u + 1}
    (Scheme.ProEt.topology X) (coefficientMap c X) (scalar c X) (adj c X)

/-- Transport the specified normalized support square using the canonical section support
comparison and the scalar transpose comparisons. Its component is a real composite of
these fixed comparisons, on arbitrary unbounded objects.
Source: scalar-six pullback proof (1)--(2)
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def sectionSupportScalar (c : Λ ⟶ Λ') [IsMonHom c]
    {S X : Scheme.{u}} [IsNoetherian X] [TopologicalSpace.NoetherianSpace S]
    (a : S ⟶ X) [IsImmersion a] (d : SupportComparison c a)
    (qS : SectionScalarComparison c S) (qX : SectionScalarComparison c X) (V : D Λ S) :
    qX.1.derived.obj ((sectionSupport Λ a).obj ((forward Λ S).obj V)) ≅
      (sectionSupport Λ' a).obj (qS.1.derived.obj ((forward Λ S).obj V)) :=
  qX.1.derived.mapIso ((sectionSupportComparison Λ a).symm.app V) ≪≫
    qX.2.2.1.symm.app ((support Λ a).obj V) ≪≫
    (forward Λ' X).mapIso ((supportComparison c a d.closedIso).app V) ≪≫
    (sectionSupportComparison Λ' a).app ((scalar c S).obj V) ≪≫
    (sectionSupport Λ' a).mapIso (qS.2.2.1.app V)

/-- The section generator uses the actual section scalar pair and actual open/closed
support functors. Its comparison with G uses only the two canonical comparison squares.
Source: direct-image proof (3), section model of G
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def sectionGeneratorComparison (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {S X : Scheme.{u}} [IsNoetherian X] [TopologicalSpace.NoetherianSpace S]
    (a : S ⟶ X) [IsImmersion a] (L : Modules (Profinite.continuousMapRingObj E) S)
    (qES : SectionScalarComparison (toC ℓ E) S) :
    (forward (Profinite.padicAlgClRingObj ℓ) X).obj (generator ℓ E a L) ≅
      (sectionSupport (Profinite.padicAlgClRingObj ℓ) a).obj
        (qES.1.derived.obj
          ((forward (Profinite.continuousMapRingObj E) S).obj
            ((DerivedCategory.singleFunctor _ 0).obj L))) :=
  (sectionSupportComparison (Profinite.padicAlgClRingObj ℓ) a).app _ ≪≫
    (sectionSupport (Profinite.padicAlgClRingObj ℓ) a).mapIso (qES.2.2.1.app _)

/-- Assemble alpha in the section model: reassociate on the support, use the inverse
normalized section support square, and realize the finite supported single complex.
This definition does not use the internal alpha.
Source: direct-image proof (3), section common-field comparison
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def sectionAlpha {E A : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ A)
    {S X : Scheme.{u}} [IsNoetherian X] [TopologicalSpace.NoetherianSpace S]
    (a : S ⟶ X) [IsImmersion a] (L : Modules (Profinite.continuousMapRingObj E) S)
    [IsIso (singleComparison (finiteInclusion ℓ h) S L)]
    (d : SupportComparison (toC ℓ A) a)
    (qES : SectionScalarComparison (toC ℓ E) S)
    (qAS : SectionScalarComparison (toC ℓ A) S)
    (qAX : SectionScalarComparison (toC ℓ A) X) :
    (sectionSupport (Profinite.padicAlgClRingObj ℓ) a).obj
        (qES.1.derived.obj ((forward (Profinite.continuousMapRingObj E) S).obj
          ((DerivedCategory.singleFunctor _ 0).obj L))) ≅
      qAX.1.derived.obj
        ((forward (Profinite.continuousMapRingObj A) X).obj (finiteModel ℓ h a L)) :=
  (sectionSupport (Profinite.padicAlgClRingObj ℓ) a).mapIso
      ((qES.2.2.1.symm.app _) ≪≫
        (forward (Profinite.padicAlgClRingObj ℓ) S).mapIso (finiteReassociation ℓ h S L) ≪≫
          qAS.2.2.1.app _) ≪≫
    (sectionSupportScalar (toC ℓ A) a d qAS qAX _).symm ≪≫
    qAX.1.derived.mapIso
      ((sectionSupportComparison (Profinite.continuousMapRingObj A) a).symm.app _ ≪≫
        (forward (Profinite.continuousMapRingObj A) X).mapIso
          (supportSingle (Profinite.continuousMapRingObj A) a (ordinary ℓ h S L)))

/-- The scalar tower in section modules, obtained from the canonical internal tower
and the specified scalar-adjunction comparisons, at an arbitrary unbounded object.
Source: scalar-six pullback proof (3)
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def sectionTower (c : Λ ⟶ Λ') [IsMonHom c] (e : Λ' ⟶ Λ'') [IsMonHom e]
    (X : Scheme.{u}) (q : SectionScalarComparison c X)
    (r : SectionScalarComparison e X) (s : SectionScalarComparison (c ≫ e) X)
    (V : D Λ X) :
    r.1.derived.obj (q.1.derived.obj ((forward Λ X).obj V)) ≅
      s.1.derived.obj ((forward Λ X).obj V) :=
  r.1.derived.mapIso (q.2.2.1.symm.app V) ≪≫
    r.2.2.1.symm.app ((scalar c X).obj V) ≪≫
    (forward Λ'' X).mapIso ((tower c e X).app V) ≪≫ s.2.2.1.app V

/-- The section B-comparison is section J applied to the separately assembled section
alpha, followed by the canonical section scalar tower.
Source: scalar-six pullback proof (3)
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def sectionAlphaB {E A : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ A)
    {S X : Scheme.{u}} [IsNoetherian X] [TopologicalSpace.NoetherianSpace S]
    (a : S ⟶ X) [IsImmersion a] (L : Modules (Profinite.continuousMapRingObj E) S)
    [IsIso (singleComparison (finiteInclusion ℓ h) S L)]
    (d : SupportComparison (toC ℓ A) a)
    (qES : SectionScalarComparison (toC ℓ E) S)
    (qAS : SectionScalarComparison (toC ℓ A) S)
    (qAX : SectionScalarComparison (toC ℓ A) X)
    (qCX : SectionScalarComparison (toB ℓ) X)
    (qBX : SectionScalarComparison (toC ℓ A ≫ toB ℓ) X) :=
  qCX.1.derived.mapIso (sectionAlpha ℓ h a L d qES qAS qAX) ≪≫
    sectionTower (toC ℓ A) (toB ℓ) X qAX qCX qBX (finiteModel ℓ h a L)

/-- The section version of the displayed unit equation uses the actual section unit,
section alpha and section alpha_B. Exact restriction comparisons transport its endpoints
back to the common A-model. The right side is the image of the independently defined
coefficient-induced map, not an equality copied from UnitEquation.
Source: direct-image proof (3), displayed unit compatibility in section modules
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def SectionUnitEquation {E A : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ A)
    {S X : Scheme.{u}} [IsNoetherian X] [TopologicalSpace.NoetherianSpace S]
    (a : S ⟶ X) [IsImmersion a] (L : Modules (Profinite.continuousMapRingObj E) S)
    [IsIso (singleComparison (finiteInclusion ℓ h) S L)]
    (d : SupportComparison (toC ℓ A) a)
    (qES : SectionScalarComparison (toC ℓ E) S)
    (qAS : SectionScalarComparison (toC ℓ A) S)
    (qAX : SectionScalarComparison (toC ℓ A) X)
    (qCX : SectionScalarComparison (toB ℓ) X)
    (qBX : SectionScalarComparison (toC ℓ A ≫ toB ℓ) X) : Prop :=
  (sectionRestriction (toC ℓ A) X qAX.2.1).hom.app
      ((scalar (toC ℓ A) X).obj (finiteModel ℓ h a L)) ≫
    (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
      (InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        (coefficientMap (toC ℓ A) X))).map
      (qAX.2.2.1.hom.app (finiteModel ℓ h a L) ≫
        (sectionAlpha ℓ h a L d qES qAS qAX).inv ≫
        qCX.1.adjunction.unit.app _ ≫
        (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
            (coefficientMap (toB ℓ) X))).map
          ((sectionAlphaB ℓ h a L d qES qAS qAX qCX qBX).hom ≫
            qBX.2.2.1.inv.app (finiteModel ℓ h a L)) ≫
        (sectionRestriction (toB ℓ) X qCX.2.1).inv.app _) ≫
    (sectionRestriction (toC ℓ A) X qAX.2.1).inv.app _ ≫
    (forward (Profinite.continuousMapRingObj A) X).map
      ((restrictComp (toC ℓ A) (toB ℓ) X).hom.app _) =
    (forward (Profinite.continuousMapRingObj A) X).map
      (inducedMap (toC ℓ A) (toB ℓ) X (finiteModel ℓ h a L))

/-- The same alpha, alpha_B and unit equation in actual section modules. Both comparison
identities use the canonical localized support comparison, and alpha_B is assembled using
the actual section scalar pair. Tensor and internal-Hom preservation are the existing
internal/section comparison theorem, not repeated predicates here.
Source: direct-image proof (3), final section-ring clause
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def SectionModelAssertions {E A : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ A)
    {S X : Scheme.{u}} [IsNoetherian X] [TopologicalSpace.NoetherianSpace S]
    (a : S ⟶ X) [IsImmersion a] (L : Modules (Profinite.continuousMapRingObj E) S)
    [IsIso (singleComparison (finiteInclusion ℓ h) S L)]
    (d : SupportComparison (toC ℓ A) a) : Prop :=
  ∃ (qES : SectionScalarComparison (toC ℓ E) S)
    (qAS : SectionScalarComparison (toC ℓ A) S)
    (qAX : SectionScalarComparison (toC ℓ A) X)
    (qCX : SectionScalarComparison (toB ℓ) X)
    (qBX : SectionScalarComparison (toC ℓ A ≫ toB ℓ) X),
    sectionGeneratorComparison ℓ E a L qES ≪≫ sectionAlpha ℓ h a L d qES qAS qAX =
      (forward (Profinite.padicAlgClRingObj ℓ) X).mapIso (alpha ℓ h a L d) ≪≫
        qAX.2.2.1.app (finiteModel ℓ h a L) ∧
    qCX.2.2.1.app (generator ℓ E a L) ≪≫
        qCX.1.derived.mapIso (sectionGeneratorComparison ℓ E a L qES) ≪≫
        sectionAlphaB ℓ h a L d qES qAS qAX qCX qBX =
      (forward (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X).mapIso
        (alphaB ℓ h a L d) ≪≫ qBX.2.2.1.app (finiteModel ℓ h a L) ∧
    SectionUnitEquation ℓ h a L d qES qAS qAX qCX qBX

/-- All clauses for one independently supported lisse module. The canonical comparisons
are definitions above; existence is asserted only for their normalized support factors
and for the invertibility of the derived-to-ordinary map.
Source: direct-image stability proof (3), common-field obligation
(blueprint: def-sfb-supported-common-field-scalar-data). -/
def ModelAssertions {E A : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ A)
    {S X : Scheme.{u}} [IsNoetherian X] [TopologicalSpace.NoetherianSpace S]
    (a : S ⟶ X) [IsImmersion a] (L : Modules (Profinite.continuousMapRingObj E) S) : Prop :=
  IsLisseCoefficientModule (Profinite.continuousMapRingObj A) (ordinary ℓ h S L) ∧
  constantModelBoundedConstructible (Profinite.continuousMapRingObj A) X
    (finiteModel ℓ h a L) ∧
  Exists fun [_hSingle : IsIso (singleComparison (finiteInclusion ℓ h) S L)] ↦
    ∃ (dC : SupportComparison (toC ℓ A) a)
      (dB : SupportComparison (toC ℓ A ≫ toB ℓ) a)
      (dCB : SupportComparison (toB ℓ) a),
      UnitEquation ℓ h a L dC ∧ alphaB ℓ h a L dC = directB ℓ h a L dB dCB ∧
      (∀ V : Scheme.{u}, V = S ∨ V = a.image ∨ V = X →
        UnitTower (finiteInclusion ℓ h) (toC ℓ A) V ∧
        UnitTower (toC ℓ A) (toB ℓ) V) ∧
      SectionModelAssertions ℓ h a L dC

end AlgebraicGeometry.ProEtale.SupportedCommonField
