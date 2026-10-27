/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Algebra.Homology.RingedSiteScalarGlobalSections
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.RingedTensorSquarePresentation

/-! # Representative-normalized global derived Hom

Source: Stacks Project, Tag 08JA, Equation 0A8Z, Tags 07A4 and 08J9.
(blueprint: def-sfb-ringed-site-global-hom-identification).

This records the normalization condition, without asserting existence of the equivalences.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RingedSiteGlobalHomIdentification
open RingedSiteScalarGlobalSections
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) (A : Type u) [CommRing A]
  (s : A →+* Scalars R)
  [HasDerivedCategory.{w} (Modules R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]

attribute [local irreducible] derivedInternalHomOfUniverses Functor.rightDerivedFunctor

/-- Global derived Hom is the recorded internal Hom followed by scalar-valued sections.
Source: Stacks 08JA (blueprint: def-sfb-ringed-site-global-hom-identification). -/
abbrev globalHom := derivedInternalHomOfUniverses.{u, u, u, w} J R ⋙
  derivedSections R A s

/-- The canonical computation map on complexes for the right derived direct image.
Source: Stacks 0D6E (blueprint: def-sfb-ringed-site-global-hom-identification). -/
abbrev computationUnit {E : Type*} [Category E] [Abelian E]
    [HasDerivedCategory.{w} E] (F : Modules R ⥤ E) [F.Additive] :=
  F.rightDerivedFunctorUnitQ

/-- Complexes in the recorded module category.
Source: Stacks 08JA (blueprint: def-sfb-ringed-site-global-hom-identification). -/
abbrev Complexes := CochainComplex (Modules R) ℤ

/-- The scalar global sections complex of a sheaf Hom complex.
Source: Stacks 08JA (blueprint: def-sfb-ringed-site-global-hom-identification). -/
abbrev sectionComplex (P I : Complexes R) :=
  ((sections R A s).mapHomologicalComplex (.up ℤ)).obj (homComplex (R := R) P I)

/-- The actual comparison from the fixed Hom-complex representative to global derived Hom.
Source: Stacks 0A95, 08JA (blueprint: def-sfb-ringed-site-global-hom-identification). -/
def representativeMap (P M : Complexes R) :
    DerivedCategory.Q.obj
      (sectionComplex R A s P ((WeilConjectures.coefficientHomResolution.{u, u, u} J R).obj M)) ⟶
    (globalHom R A s).obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj M) :=
  computationUnit R (sections R A s)
      (homComplex (R := R) P ((WeilConjectures.coefficientHomResolution.{u, u, u} J R).obj M)) ≫
    (derivedSections R A s).map
      (WeilConjectures.coefficientHomResolutionIso.{u, u, u, w} J R P M).inv

/-- A scalar section represents a cochain when its product projections are the
usual sheaf-Hom sections of the components of that cochain.
Source: Stacks 0A8Z, 08JA (blueprint: def-sfb-ringed-site-global-hom-identification). -/
def Represents (P I : Complexes R) (n : ℤ)
    (x : (sectionComplex R A s P I).X n)
    (z : CochainComplex.HomComplex.Cocycle P I n) : Prop :=
  ∀ (p q : ℤ) (h : p + n = q),
    SheafOfModules.homObjSectionsEquiv (P.X p) (I.X q)
      (SheafOfModules.sectionsMap
        (WeilConjectures.coefficientHomComponent.{u, u, u} J R P I n p q h)
        ⟨x.val, fun i ↦ x.property i⟩) = z.val.v p q h

/-- The usual localized morphism of a cocycle, followed by the inverse of the fixed
K-injective augmentation. This fixes every sign and every shift comparison.
Source: Stacks 08JA (blueprint: def-sfb-ringed-site-global-hom-identification). -/
def cocycleMorphism (P M : Complexes R) (n : ℤ)
    (z : CochainComplex.HomComplex.Cocycle P
      ((WeilConjectures.coefficientHomResolution.{u, u, u} J R).obj M) n) :
    DerivedCategory.Q.obj P ⟶ (DerivedCategory.Q.obj M)⟦n⟧ :=
  DerivedCategory.Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z) ≫
    (DerivedCategory.Q.commShiftIso n).hom.app _ ≫
      (shiftFunctor _ n).map (WeilConjectures.coefficientHomResolutionInverse.{u, u, u, w} J R M)

attribute [local irreducible] sections sectionSubmodule scalarAt

/-- The usual global-Hom/cohomology identification, with its naturality and fixed
Hom-complex normalization. The normalization is tested on all K-flat representatives
and all cycles of their section complexes, using the fixed K-injective replacement.
Source: Stacks 08JA (blueprint: def-sfb-ringed-site-global-hom-identification). -/
structure HomIdentification where
  equiv : ∀ (K L : DerivedCategory (Modules R)) (n : ℤ),
    ((DerivedCategory.homologyFunctor (ModuleCat A) n).obj
      ((globalHom R A s).obj (op K, L))) ≃+ (K ⟶ L⟦n⟧)
  naturality : ∀ {K K' L L' : DerivedCategory (Modules R)}
    (a : K' ⟶ K) (b : L ⟶ L') (n : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat A) n).obj
      ((globalHom R A s).obj (op K, L))),
    equiv K' L' n
        (((DerivedCategory.homologyFunctor (ModuleCat A) n).map
          ((globalHom R A s).map (a.op, b))) x) =
      a ≫ equiv K L n x ≫ (shiftFunctor _ n).map b
  normalization : ∀ (P M : Complexes R), P.IsKFlatIndependentCoefficients → ∀ (n : ℤ)
    (x : (sectionComplex R A s P
      ((WeilConjectures.coefficientHomResolution.{u, u, u} J R).obj M)).cycles n)
    (z : CochainComplex.HomComplex.Cocycle P
      ((WeilConjectures.coefficientHomResolution.{u, u, u} J R).obj M) n),
    Represents R A s P _ n
      (((sectionComplex R A s P
        ((WeilConjectures.coefficientHomResolution.{u, u, u} J R).obj M)).iCycles n) x) z →
    equiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj M) n
      (((DerivedCategory.homologyFunctor (ModuleCat A) n).map
          (representativeMap R A s P M))
        (((DerivedCategory.homologyFunctorFactors (ModuleCat A) n).inv.app _)
          (((sectionComplex R A s P
            ((WeilConjectures.coefficientHomResolution.{u, u, u} J R).obj M)).homologyπ n) x))) =
      cocycleMorphism R P M n z

/-- Present the recorded closed tensor structure in the existing ringed-topos interface.
Source: Stacks 07A4, 08J9 (blueprint: def-sfb-ringed-site-global-hom-identification). -/
def corner
    (S : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u, u, u, w} J R)) :
    SheafOfModules.RingedTensorCorner.{u, w} where
  site := C
  category := inferInstance
  topology := J
  ring := R
  derived := inferInstance
  tensor := S.tensor

/-- The inclusion of flat-term K-flat representatives into all K-flat representatives.
Source: Stacks 07A4 (blueprint: def-sfb-ringed-site-global-hom-identification). -/
def flatInclusion :
    ObjectProperty.FullSubcategory (fun P : CochainComplex (Modules R) ℤ ↦
      P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat) ⥤
    ObjectProperty.FullSubcategory (fun P : CochainComplex (Modules R) ℤ ↦
      P.IsKFlatIndependentCoefficients) where
  obj P := ⟨P.obj, P.property.1⟩
  map f := ObjectProperty.homMk f.hom

/-- Restriction of the fixed tensor representative comparison.
Source: Stacks 07A4 (blueprint: def-sfb-ringed-site-global-hom-identification). -/
def tensorModel
    (S : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u, u, u, w} J R))
    (T : WeilConjectures.CoefficientTensorModels.{u, u, u, w} J R S) :
    SheafOfModules.RingedTensorModel (corner R S) :=
  ⟨Functor.isoWhiskerLeft ((flatInclusion R).prod (flatInclusion R)) T.comparison⟩

end CategoryTheory.RingedSiteGlobalHomIdentification
