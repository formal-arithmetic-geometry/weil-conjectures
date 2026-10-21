/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.FiniteFieldFiber
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.KFlatMapFactorization
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
import Sheaf.Algebra.Homology.KFlat
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomTensorTotal
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel
import Sheaf.SixFunctors.GeometricInverseImageConstantModule
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
/-! # External global derived Hom and coefficient cones

Source: Stacks Project, Cohomology on Sites, Tags 08J9, 08JC, 0A90 and 0G7D;
blueprint main-20261015, `lem-pur-kunneth-supported.proof.md`, paragraphs 1 and 3
(blueprint: lem-pur-external-rhom-cone-pairing).

## Main definitions

* `globalHom`, `evaluation`, `pairing`: global derived Hom and its evaluation transpose.
* `HomModel`, `HasChainNormalization`: evaluation-normalized cochain representatives.
* `IsNatural`, `CommutesWithOpenRestriction`: the four variances and restriction square.
* `HasSignedHomShift`, `PreservesCoefficientCones`: both signed triangle comparisons.

## Main statements

* `external_rhom_cone_pairing`: the normalized construction and all its compatibilities.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u uC vC uD vD uB vB

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.ExternalRHom

/-- Pull an evaluation through the constant and tensor comparisons before specializing
categories. Source: Stacks 08J9 and 0G7E
(blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def pullEvaluationOf
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
    {B : Type uB} [Category.{vB} B]
    (F : C ⥤ D) (c : B ⥤ C) (d : B ⥤ D) (α : d ≅ c ⋙ F)
    (δ : ∀ E H : C, F.obj E ⊗ F.obj H ⟶ F.obj (E ⊗ H))
    (E K : C) (Q : B) (t : c.obj Q ⊗ E ⟶ K) :
    d.obj Q ⊗ F.obj E ⟶ F.obj K :=
  (α.hom.app Q ▷ F.obj E) ≫ δ (c.obj Q) E ≫ F.map t

/-- Tensor two evaluations with the Koszul interchange before specializing categories.
Source: Stacks 08J9 and 0A90 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def externalEvaluationOf
    {B : Type uB} [Category.{vB} B] [MonoidalCategory B]
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    (c : B ⥤ C)
    (δ : (Functor.postcompose₂.obj c).obj (curriedTensor B) ⟶
      (((Functor.whiskeringLeft₂ C).obj c).obj c).obj (curriedTensor C))
    (Q R : B) (E H K L' : C)
    (t : c.obj Q ⊗ E ⟶ K) (t' : c.obj R ⊗ H ⟶ L') :
    c.obj (Q ⊗ R) ⊗ (E ⊗ H) ⟶ K ⊗ L' :=
  (((δ.app Q).app R) ▷ (E ⊗ H)) ≫
    tensorμ (c.obj Q) (c.obj R) E H ≫ (t ⊗ₘ t')

/-- The external transpose with its adjunction left abstract. This is the same
external evaluation composite, with no extra choices of maps.
Source: Stacks 08J9 and 0A90 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def pairingOf
    {B : Type uB} [Category.{vB} B] [MonoidalCategory B]
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    (c : B ⥤ C) (h : Cᵒᵖ ⥤ C ⥤ B)
    (tr : ∀ (E K : C) (Q : B), (c.obj Q ⊗ E ⟶ K) → (Q ⟶ (h.obj (op E)).obj K))
    (δ : (Functor.postcompose₂.obj c).obj (curriedTensor B) ⟶
      (((Functor.whiskeringLeft₂ C).obj c).obj c).obj (curriedTensor C))
    (Q R : B) (E H K L' : C)
    (t : c.obj Q ⊗ E ⟶ K) (t' : c.obj R ⊗ H ⟶ L') :
    Q ⊗ R ⟶ (h.obj (op (E ⊗ H))).obj (K ⊗ L') :=
  tr (E ⊗ H) (K ⊗ L') (Q ⊗ R) (externalEvaluationOf c δ Q R E H K L' t t')

/-- Braiding compatibility at one pair, expressed in arbitrary categories.
Source: Stacks 0A90 (blueprint: lem-pur-external-rhom-cone-pairing). -/
def IsBraidedAt
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D] [BraidedCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] (E H : C) : Prop :=
  (β_ (F.obj E) (F.obj H)).hom ≫ Functor.LaxMonoidal.μ F H E =
    Functor.LaxMonoidal.μ F E H ≫ F.map (β_ E H).hom

/-- Transpose an evaluation after its two representative comparisons.
Source: Stacks 08JA (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def modelTransposeOf
    {B : Type uB} [Category.{vB} B]
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    (c : B ⥤ C) (h : Cᵒᵖ ⥤ C ⥤ B)
    (tr : ∀ (E K : C) (Q : B), (c.obj Q ⊗ E ⟶ K) → (Q ⟶ (h.obj (op E)).obj K))
    (Q : B) (E K V W : C) (α : c.obj Q ⟶ V)
    (μ : V ⊗ E ⟶ W) (t : W ⟶ K) : Q ⟶ (h.obj (op E)).obj K :=
  tr E K Q ((α ▷ E) ≫ μ ≫ t)

/-- Compare the tensor of two represented objects using a lax tensor constraint.
Source: Stacks 06YS (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def tensorModelOf
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] (E H : C) (M N : D)
    (f : M ⟶ F.obj E) (g : N ⟶ F.obj H) : M ⊗ N ⟶ F.obj (E ⊗ H) :=
  (f ⊗ₘ g) ≫ Functor.LaxMonoidal.μ F E H

/-- Tensor two comparison arrows and postcompose with two further comparisons.
Source: Stacks 06YS and 0G7D (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def tensorThenOf
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {E E' H H' K M : C} (f : E ⟶ E') (g : H ⟶ H')
    (t : E' ⊗ H' ⟶ K) (i : K ⟶ M) : E ⊗ H ⟶ M :=
  (f ⊗ₘ g) ≫ t ≫ i

/-- A summand inclusion in the ordinary total tensor complex.
Source: Stacks 0A90 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def tensorInclusionOf
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasColimitsOfSize.{0, 0} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    (K L' : CochainComplex C ℤ) (r q n : ℤ) (h : r + q = n) :
    K.X r ⊗ L'.X q ⟶ (K ⊗ L').X n :=
  HomologicalComplex.ιTensorObj K L' r q n h

/-- Transpose an ordinary evaluation after the localization tensor constraint.
Source: Stacks 08JA and 06YS (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def chainModelTransposeOf
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [MonoidalCategory (CochainComplex C ℤ)]
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
    {B : Type uB} [Category.{vB} B]
    (Q : CochainComplex C ℤ ⥤ D) [Q.LaxMonoidal]
    (c : B ⥤ D) (h : Dᵒᵖ ⥤ D ⥤ B)
    (tr : ∀ (E K : D) (U : B), (c.obj U ⊗ E ⟶ K) → (U ⟶ (h.obj (op E)).obj K))
    (U : B) (E I V : CochainComplex C ℤ) (α : c.obj U ⟶ Q.obj V)
    (t : V ⊗ E ⟶ I) : U ⟶ (h.obj (op (Q.obj E))).obj (Q.obj I) :=
  modelTransposeOf c h tr U (Q.obj E) (Q.obj I) (Q.obj V) (Q.obj (V ⊗ E)) α
    (Functor.LaxMonoidal.μ Q V E) (Q.map t)

/-- Pull an ordinary chain evaluation through the canonical termwise comparisons.
Source: Stacks 0G7E (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def pullComplexEvaluationOf
    {B : Type uB} [Category.{vB} B] [Preadditive B]
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [MonoidalCategory (CochainComplex C ℤ)]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [MonoidalCategory (CochainComplex D ℤ)]
    (F : C ⥤ D) [F.Additive] [(F.mapHomologicalComplex (.up ℤ)).Monoidal]
    (c : B ⥤ C) [c.Additive] (d : B ⥤ D) [d.Additive] (α : d ≅ c ⋙ F)
    (E K : CochainComplex C ℤ) (U : CochainComplex B ℤ)
    (t : (c.mapHomologicalComplex (.up ℤ)).obj U ⊗ E ⟶ K) :
    (d.mapHomologicalComplex (.up ℤ)).obj U ⊗
        (F.mapHomologicalComplex (.up ℤ)).obj E ⟶
      (F.mapHomologicalComplex (.up ℤ)).obj K :=
  pullEvaluationOf (F.mapHomologicalComplex (.up ℤ))
    (c.mapHomologicalComplex (.up ℤ)) (d.mapHomologicalComplex (.up ℤ))
    (Functor.mapHomologicalComplexCompIso α.symm (.up ℤ)).symm
    (fun E' H' ↦ (Functor.Monoidal.μIso (F.mapHomologicalComplex (.up ℤ)) E' H').hom) E K U t

/-- Tensor two ordinary chain evaluations and postcompose with the target resolution.
Source: Stacks 0A90 and 0G7D (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def externalComplexEvaluationOf
    {B : Type uB} [Category.{vB} B] [Preadditive B]
    [MonoidalCategory (CochainComplex B ℤ)]
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [MonoidalCategory (CochainComplex C ℤ)] [BraidedCategory (CochainComplex C ℤ)]
    (c : B ⥤ C) [c.Additive] [(c.mapHomologicalComplex (.up ℤ)).OplaxMonoidal]
    (U V : CochainComplex B ℤ) (E H K L' J : CochainComplex C ℤ)
    (t : (c.mapHomologicalComplex (.up ℤ)).obj U ⊗ E ⟶ K)
    (t' : (c.mapHomologicalComplex (.up ℤ)).obj V ⊗ H ⟶ L') (i : K ⊗ L' ⟶ J) :
    (c.mapHomologicalComplex (.up ℤ)).obj (U ⊗ V) ⊗ (E ⊗ H) ⟶ J :=
  externalEvaluationOf (c.mapHomologicalComplex (.up ℤ))
    (Functor.OplaxMonoidal.δNatTrans (c.mapHomologicalComplex (.up ℤ))) U V E H K L' t t' ≫ i

variable (A : Type (u + 1)) [CommRing A]


/-- Ordinary module-valued sheaves, the recorded constant-coefficient encoding.
Source: Stacks 08J7 (blueprint: lem-pur-external-rhom-cone-pairing). -/
abbrev Modules (X : Scheme.{u}) := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)

/-- Cochain complexes of ordinary constant-coefficient module sheaves.
Source: Stacks 0A8X (blueprint: lem-pur-external-rhom-cone-pairing). -/
abbrev Complexes (X : Scheme.{u}) := CochainComplex (Modules A X) ℤ

/-- Cache the existing monoidal structure on ordinary module sheaves.
Source: Stacks 06YL (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable instance modulesMonoidal (X : Scheme.{u}) : MonoidalCategory (Modules A X) :=
  inferInstance

/-- Cache the native direct-sum total tensor structure on complexes.
Source: Stacks 0A90 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable instance complexesMonoidal (X : Scheme.{u}) : MonoidalCategory (Complexes A X) :=
  inferInstance

/-- Use the existing canonical derived Koszul braiding at this fixed sheaf category.
Naming the specialization shares its inferred structure arguments between the evaluations.
Source: Stacks 0A90 (blueprint: lem-pur-external-rhom-cone-pairing). -/
@[instance_reducible]
noncomputable def derivedBraiding (X : Scheme.{u}) :
    BraidedCategory (DerivedCategoryModule A X) :=
  DerivedCategory.braidedCategory' (Modules A X)

attribute [local instance] derivedBraiding

/-- The existing derived constant-coefficient functor.
Source: Stacks 07A6 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev constant (X : Scheme.{u}) :
    DerivedCategory (ModuleCat.{u + 1} A) ⥤ DerivedCategoryModule A X :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).leftDerivedFunctor

/-- The existing constant-coefficient derived inverse image.
Source: Stacks 0G7E (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev pull {X P : Scheme.{u}} (a : P ⟶ X) :
    DerivedCategoryModule A X ⥤ DerivedCategoryModule A P :=
  (upperStar (ModuleCat.{u + 1} A) a).leftDerivedFunctor

/-- Existing module-valued derived global sections.
Source: Stacks 07A6 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev sections (X : Scheme.{u}) :
    DerivedCategoryModule A X ⥤ DerivedCategory (ModuleCat.{u + 1} A) :=
  rightDerivedGlobalSections (ModuleCat.{u + 1} A) X

/-- The existing closed derived internal Hom of ordinary module sheaves.
Source: Stacks 08J9 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev internalHom (X : Scheme.{u}) :=
  MonoidalClosed.internalHom (C := DerivedCategoryModule A X)

/-- Existing tensor--Hom adjunction in the ordinary module encoding.
Source: Stacks 08J9 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def closedAdjunction {X : Scheme.{u}} (E : DerivedCategoryModule A X) :
    tensorLeft E ⊣ (internalHom A X).obj (op E) :=
  MonoidalClosed.internalHomAdjunction₂.adj E

/-- Existing derived constant--sections adjunction in the common coefficient universe.
Source: Stacks 07A6 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def constantSectionsAdjunction (X : Scheme.{u}) :
    constant A X ⊣ sections A X :=
  derivedConstantGlobalSectionsAdjunction (ModuleCat.{u + 1} A) X

/-- Global derived Hom, using the existing closed derived tensor and derived sections.
Source: Stacks 08J9 and 08JA (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev globalHom (X : Scheme.{u}) :
    (DerivedCategoryModule A X)ᵒᵖ ⥤ DerivedCategoryModule A X ⥤
      DerivedCategory (ModuleCat.{u + 1} A) :=
  internalHom A X ⋙ (Functor.whiskeringRight _ _ _).obj (sections A X)

/-- The composite of the existing constant/sections and tensor/Hom adjunctions.
Source: Stacks 08J9 and 07A6 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def globalAdjunction {X : Scheme.{u}} (E : DerivedCategoryModule A X) :
    (constant A X ⋙ tensorLeft E) ⊣ (globalHom A X).obj (op E) :=
  (constantSectionsAdjunction A X).comp (closedAdjunction A E)

/-- The tensor--Hom transpose, with the global coefficient on the left.
Source: Stacks 08J9 and 07A6 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def transpose {X : Scheme.{u}}
    (E K : DerivedCategoryModule A X) (Q : DerivedCategory (ModuleCat.{u + 1} A))
    (t : (constant A X).obj Q ⊗ E ⟶ K) :
    Q ⟶ ((globalHom A X).obj (op E)).obj K :=
  (globalAdjunction A E).homEquiv Q K ((β_ E ((constant A X).obj Q)).hom ≫ t)

/-- Evaluation of global derived morphisms, as the composite adjunction counit.
Source: Stacks 08J9 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def evaluation {X : Scheme.{u}} (E K : DerivedCategoryModule A X) :
    (constant A X).obj (((globalHom A X).obj (op E)).obj K) ⊗ E ⟶ K :=
  (β_ E ((constant A X).obj (((globalHom A X).obj (op E)).obj K))).inv ≫
    (globalAdjunction A E).counit.app K

/-- The tensor constraint of the existing canonical monoidal inverse image.
Source: Stacks 0G7E (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def pullTensorIso {X P : Scheme.{u}} (a : P ⟶ X)
    (E H : DerivedCategoryModule A X) :
    (pull A a).obj E ⊗ (pull A a).obj H ≅ (pull A a).obj (E ⊗ H) :=
  letI := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} A) a
  Functor.Monoidal.μIso (pull A a) E H

/-- Pull evaluation back, with the canonical constant and tensor comparisons.
Source: Stacks 08J9 and 0G7E (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def pulledEvaluation {X P : Scheme.{u}} (a : P ⟶ X)
    (E K : DerivedCategoryModule A X) :
    (constant A P).obj
      (((globalHom A X).obj (op E)).obj K) ⊗
        (pull A a).obj E ⟶
      (pull A a).obj K :=
  pullEvaluationOf (pull A a) (constant A X) (constant A P)
    (derivedConstantPullbackIso (ModuleCat.{u + 1} A) a)
    (fun E' H' ↦ (pullTensorIso A a E' H').hom) E K
    (((globalHom A X).obj (op E)).obj K) (evaluation A E K)

/-- The external evaluation transpose, with the Koszul interchange between the second
Hom factor and the first coefficient factor. Source: Stacks 08J9 and 0A90
(blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def pairing {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (E K : DerivedCategoryModule A X) (H L' : DerivedCategoryModule A Y) :
    ((globalHom A X).obj (op E)).obj K ⊗ ((globalHom A Y).obj (op H)).obj L' ⟶
      ((globalHom A P).obj (op ((pull A a).obj E ⊗
        (pull A b).obj H))).obj
          ((pull A a).obj K ⊗
            (pull A b).obj L') :=
  pairingOf (constant A P) (globalHom A P) (transpose A (X := P))
    (constantSheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)).leftDerivedTensorComparison
    (((globalHom A X).obj (op E)).obj K) (((globalHom A Y).obj (op H)).obj L')
    ((pull A a).obj E) ((pull A b).obj H) ((pull A a).obj K) ((pull A b).obj L')
    (pulledEvaluation A a E K) (pulledEvaluation A b H L')

/-- Existing localization of ordinary sheaf complexes.
Source: Stacks 05RU (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev siteQ (X : Scheme.{u}) : Complexes A X ⥤ DerivedCategoryModule A X :=
  DerivedCategory.Q

/-- Existing localization of coefficient complexes.
Source: Stacks 05RU (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev moduleQ : CochainComplex (ModuleCat.{u + 1} A) ℤ ⥤
    DerivedCategory (ModuleCat.{u + 1} A) :=
  DerivedCategory.Q

/-- Global A-linear Hom cochains with the standard Hom differential, without a
boundedness assumption. Source: Stacks 0A8X
(blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def homComplex {X : Scheme.{u}} (E I : Complexes A X) :
    CochainComplex (ModuleCat.{u + 1} A) ℤ where
  X n := ModuleCat.of A (CochainComplex.HomComplex.Cochain E I n)
  d n m := ModuleCat.ofHom (CochainComplex.HomComplex.δ_hom A E I n m)
  shape n m h := ModuleCat.hom_ext (LinearMap.ext
    (fun z ↦ CochainComplex.HomComplex.δ_shape n m h z))
  d_comp_d' n m k _ _ := ModuleCat.hom_ext (LinearMap.ext
    (fun z ↦ CochainComplex.HomComplex.δ_δ n m k z))

/-- The termwise constant complex.
Source: Stacks 0A8X (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev constantComplex (X : Scheme.{u}) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)

/-- The ordinary source of a global chain evaluation, using the native total tensor.
Source: Stacks 0A8X and 0A90 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def chainEvaluationSource (X : Scheme.{u})
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (E : Complexes A X) : Complexes A X :=
  (constantComplex A X).obj U ⊗ E

/-- A constant local section is the image under the sheafification unit.
Source: Stacks 0A8X (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def constantSection (X : Scheme.{u}) (M : ModuleCat.{u + 1} A)
    (W : X.Etaleᵒᵖ) (w : M) :
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M).obj.obj W :=
  (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app W w

/-- The canonical pure tensor of local sections, followed by sheafification.
Source: Stacks 06YL (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def tensorSection {X : Scheme.{u}} (M N : Modules A X)
    (W : X.Etaleᵒᵖ) (m : M.obj.obj W) (n : N.obj.obj W) : (M ⊗ N).obj.obj W :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} A)) M N).app W) (TensorProduct.tmul A m n)

/-- The pure tensor of sections in a specified total-complex summand.
Source: Stacks 0A90 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def tensorComplexSection {X : Scheme.{u}} (K L' : Complexes A X)
    (r q n : ℤ) (h : r + q = n) (W : X.Etaleᵒᵖ)
    (x : (K.X r).obj.obj W) (y : (L'.X q).obj.obj W) :=
  ((tensorInclusionOf K L' r q n h).hom.app W)
    (tensorSection A (K.X r) (L'.X q) W x y)

/-- The evaluation identity for a chain map to a global Hom complex. This fixes every
local component, including the unsigned ordinary evaluation.
Source: Stacks 0A8X and 08J9 (blueprint: lem-pur-external-rhom-cone-pairing). -/
def IsChainEvaluation {X : Scheme.{u}} (E I : Complexes A X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (f : U ⟶ homComplex A E I)
    (t : chainEvaluationSource A X U E ⟶ I) : Prop :=
  ∀ (r q : ℤ) (W : X.Etaleᵒᵖ) (w : U.X r) (e : (E.X q).obj.obj W),
    ((t.f (q + r)).hom.app W)
      (tensorComplexSection A ((constantComplex A X).obj U) E
        r q (q + r) (add_comm r q) W (constantSection A X (U.X r) W w) e) =
      (((((f.f r).hom w).v q (q + r) rfl).hom.app W) e)

/-- The canonical realization of ordinary module sheaves over the commutative
constant ring sheaf, using the existing scalar-extension functor and ring comparison.
Source: Stacks 03CV and 093J (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def ringedRealization (X : Scheme.{u}) :=
  Scheme.etaleConstantModuleFunctor X A ⋙
    SheafOfModules.restrictScalars (realizationRingIso X.smallEtaleTopology A).hom

/-- Scalar realization is additive because its underlying maps of sections are unchanged.
Source: Stacks 03CV (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable instance ringedRealizationAdditive (X : Scheme.{u}) :
    (ringedRealization A X).Additive where
  map_add := by intros; ext W x; rfl

/-- Apply canonical scalar realization degreewise, retaining the full ringed-site complex.
Source: Stacks 03CV and 0A8X (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def ringedComplex (X : Scheme.{u}) :=
  (ringedRealization A X).mapHomologicalComplex (.up ℤ)

/-- Regard a coefficient module as a module sheaf on the one-point site with its
trivial topology. This is the existing exact constant realization, not a new tensor.
Source: Stacks 03CV (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev pointRealization :=
  commutativeSiteConstantModuleFunctor
    (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) A

/-- Realize a coefficient complex on the one-point site to apply the recorded K-flat
predicate to ordinary A-complexes without substituting another flatness notion.
Source: Stacks 06YN (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev pointComplex :=
  (pointRealization A).mapHomologicalComplex (.up ℤ)

/-- Bounded flat complexes, with flatness tested in the dependency's ringed-site
module realization. No bound is fixed in advance.
Source: Stacks 06YQ (blueprint: lem-pur-external-rhom-cone-pairing). -/
def IsBoundedFlat {X : Scheme.{u}} (E : Complexes A X) : Prop :=
  (∃ lo hi : ℤ, ∀ q : ℤ, q < lo ∨ hi < q → IsZero (E.X q)) ∧
  ∀ q : ℤ, SheafOfModules.IsFlatOnSite
    (J := X.smallEtaleTopology)
    (R := realizationRing X.smallEtaleTopology A)
    ((ringedRealization A X).obj (E.X q))

/-- The ordinary-complex counit for constant sheaves.
Source: Stacks 07A6 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def constantModel (X : Scheme.{u})
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    (constant A X).obj
      ((moduleQ A).obj U) ⟶ (siteQ A X).obj ((constantComplex A X).obj U) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).leftDerivedFunctorCounit.app
    ((HomotopyCategory.quotient _ _).obj U)

/-- The ordinary-complex counit for exact inverse image.
Source: Stacks 0G7E (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def pullModel {X P : Scheme.{u}} (a : P ⟶ X) (E : Complexes A X) :
    (pull A a).obj ((siteQ A X).obj E) ⟶
      (siteQ A P).obj
        (((upperStar (ModuleCat.{u + 1} A) a).mapHomologicalComplex (.up ℤ)).obj E) :=
  (upperStar (ModuleCat.{u + 1} A) a).leftDerivedFunctorCounit.app
    ((HomotopyCategory.quotient _ _).obj E)

/-- The evaluation-normalized comparison with global Hom cochains. Its universal
component identity fixes the comparison rather than allowing arbitrary automorphisms.
Source: Stacks 08JA and 08J9 (blueprint: lem-pur-external-rhom-cone-pairing). -/
def IsHomModel {X : Scheme.{u}} (E I : Complexes A X)
    (iso : (moduleQ A).obj (homComplex A E I) ≅
      ((globalHom A X).obj (op ((siteQ A X).obj E))).obj ((siteQ A X).obj I)) : Prop :=
  ∀ (U : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (f : U ⟶ homComplex A E I) (t : chainEvaluationSource A X U E ⟶ I),
    IsChainEvaluation A E I U f t →
    (moduleQ A).map f ≫ iso.hom =
      chainModelTransposeOf (siteQ A X) (constant A X) (globalHom A X)
        (transpose A (X := X)) ((moduleQ A).obj U) E I ((constantComplex A X).obj U)
        (constantModel A X U) t

/-- An isomorphism satisfying the universal chain-evaluation normalization.
Source: Stacks 08JA and 08J9 (blueprint: lem-pur-external-rhom-cone-pairing). -/
def HomModel {X : Scheme.{u}} (E I : Complexes A X) :=
  { iso : (moduleQ A).obj (homComplex A E I) ≅
    ((globalHom A X).obj (op ((siteQ A X).obj E))).obj ((siteQ A X).obj I) //
    IsHomModel A E I iso }

/-- The comparison isomorphism of an evaluation-normalized Hom model.
Source: Stacks 08JA and 08J9 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def HomModel.iso {X : Scheme.{u}} {E I : Complexes A X}
    (m : HomModel A E I) :
    (moduleQ A).obj (homComplex A E I) ≅
      ((globalHom A X).obj (op ((siteQ A X).obj E))).obj ((siteQ A X).obj I) :=
  m.val

/-- Pulling global morphisms back is the transpose of pulled-back evaluation.
For an open immersion this is the ordinary restriction map.
Source: Stacks 08JB (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def restriction {X P : Scheme.{u}} (a : P ⟶ X)
    (E K : DerivedCategoryModule A X) :
    ((globalHom A X).obj (op E)).obj K ⟶
      ((globalHom A P).obj (op ((pull A a).obj E))).obj
        ((pull A a).obj K) :=
  transpose A _ _ _ (pulledEvaluation A a E K)

/-- The ordinary pulled-back complex, with no derived replacement.
Source: Stacks 0G7E (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev pullComplex {X P : Scheme.{u}} (a : P ⟶ X) :=
  (upperStar (ModuleCat.{u + 1} A) a).mapHomologicalComplex (.up ℤ)

/-- The source coefficient complex on P in the chain normalization.
Source: Stacks 0A90 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev externalComplex {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (E : Complexes A X) (H : Complexes A Y) : Complexes A P :=
  (pullComplex A a).obj E ⊗ (pullComplex A b).obj H

/-- The canonical comparison from the derived external coefficient to its ordinary model.
Source: Stacks 06YS and 0G7E (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def externalModel {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (E : Complexes A X) (H : Complexes A Y) :=
  tensorModelOf (siteQ A P) ((pullComplex A a).obj E) ((pullComplex A b).obj H)
    ((pull A a).obj ((siteQ A X).obj E)) ((pull A b).obj ((siteQ A Y).obj H))
    (pullModel A a E) (pullModel A b H)

/-- Pull back a lifted evaluation into its K-flat target, with canonical comparisons.
Source: Stacks 0G7D and 0G7E (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def pulledChainEvaluation {X P : Scheme.{u}} (a : P ⟶ X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (E N : Complexes A X)
    (u : chainEvaluationSource A X U E ⟶ N) :
    chainEvaluationSource A P U ((pullComplex A a).obj E) ⟶ (pullComplex A a).obj N :=
  pullComplexEvaluationOf (upperStar (ModuleCat.{u + 1} A) a)
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (constantSheaf P.smallEtaleTopology (ModuleCat.{u + 1} A))
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) a).symm E N U u

/-- The honest uncurried evaluation into J. The middle interchange on complexes
contributes exactly (-1)^(s*q) on U^r,V^s,E^q,H^t.
Source: Stacks 0A90, 0G7D and 08J9 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def chainPairEvaluation {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (U V : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (E N : Complexes A X) (H M : Complexes A Y) (J : Complexes A P)
    (u : chainEvaluationSource A X U E ⟶ N)
    (v : chainEvaluationSource A Y V H ⟶ M)
    (i : externalComplex A a b N M ⟶ J) :
    chainEvaluationSource A P (U ⊗ V) (externalComplex A a b E H) ⟶ J :=
  externalComplexEvaluationOf (constantSheaf P.smallEtaleTopology (ModuleCat.{u + 1} A))
    U V ((pullComplex A a).obj E) ((pullComplex A b).obj H)
    ((pullComplex A a).obj N) ((pullComplex A b).obj M) J
    (pulledChainEvaluation A a U E N u) (pulledChainEvaluation A b V H M v) i

/-- The target representative map uses the inverses of the K-flat resolution maps,
then the ordinary K-flat tensor and its K-injective resolution. It never tensors
K-injective representatives as an ordinary tensor.
Source: Stacks 0G7D and 0G7E (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def targetModel {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (N I : Complexes A X) (M I' : Complexes A Y) (J : Complexes A P)
    (c : N ⟶ I) (c' : M ⟶ I') [QuasiIso c] [QuasiIso c']
    (i : externalComplex A a b N M ⟶ J) :
    (pull A a).obj ((siteQ A X).obj I) ⊗
      (pull A b).obj ((siteQ A Y).obj I') ⟶ (siteQ A P).obj J :=
  tensorThenOf ((pull A a).map (inv ((siteQ A X).map c)))
    ((pull A b).map (inv ((siteQ A Y).map c')))
    (externalModel A a b N M) ((siteQ A P).map i)

/-- The complex-model normalization, quantified over every choice in the node.
The cochain equation is IsChainEvaluation for the explicit Koszul composite.
Source: Stacks 08JA, 0A90 and 0G7D (blueprint: lem-pur-external-rhom-cone-pairing). -/
def HasChainNormalization {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (E : Complexes A X) (H : Complexes A Y) (I : Complexes A X) (I' : Complexes A Y) : Prop :=
  ∀ (U V : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (f : U ⟶ homComplex A E I) (g : V ⟶ homComplex A H I')
    [QuasiIso f] [QuasiIso g],
    CochainComplex.IsKFlatIndependentCoefficients
      (J := (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})))
      (R := realizationRing (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) A)
      ((pointComplex A).obj U) →
    CochainComplex.IsKFlatIndependentCoefficients
      (J := (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})))
      (R := realizationRing (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) A)
      ((pointComplex A).obj V) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite
      (J := (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})))
      (R := realizationRing (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) A)
      ((pointRealization A).obj (U.X n))) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite
      (J := (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})))
      (R := realizationRing (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) A)
      ((pointRealization A).obj (V.X n))) →
    ∀ (t : chainEvaluationSource A X U E ⟶ I)
      (t' : chainEvaluationSource A Y V H ⟶ I'),
    IsChainEvaluation A E I U f t → IsChainEvaluation A H I' V g t' →
    ∀ (N : Complexes A X) (M : Complexes A Y)
      (u : chainEvaluationSource A X U E ⟶ N)
      (v : chainEvaluationSource A Y V H ⟶ M)
      (c : N ⟶ I) (c' : M ⟶ I') [QuasiIso c] [QuasiIso c'],
    CochainComplex.IsKFlatIndependentCoefficients
      (J := X.smallEtaleTopology) (R := realizationRing X.smallEtaleTopology A)
      ((ringedComplex A X).obj N) →
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Y.smallEtaleTopology) (R := realizationRing Y.smallEtaleTopology A)
      ((ringedComplex A Y).obj M) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite
      (J := X.smallEtaleTopology) (R := realizationRing X.smallEtaleTopology A)
      ((ringedRealization A X).obj (N.X n))) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite
      (J := Y.smallEtaleTopology) (R := realizationRing Y.smallEtaleTopology A)
      ((ringedRealization A Y).obj (M.X n))) →
    Nonempty (Homotopy (u ≫ c) t) → Nonempty (Homotopy (v ≫ c') t') →
    ∀ (J : Complexes A P) (i : externalComplex A a b N M ⟶ J)
      [QuasiIso i] [J.IsKInjective]
      (mE : HomModel A E I) (mH : HomModel A H I')
      (mG : HomModel A (externalComplex A a b E H) J),
    ∃ κ : U ⊗ V ⟶ homComplex A (externalComplex A a b E H) J,
      IsChainEvaluation A _ J (U ⊗ V) κ
        (chainPairEvaluation A a b U V E N H M J u v i) ∧
      (((moduleQ A).map f ≫ mE.iso.hom) ⊗ₘ ((moduleQ A).map g ≫ mH.iso.hom)) ≫
          pairing A a b ((siteQ A X).obj E) ((siteQ A X).obj I)
            ((siteQ A Y).obj H) ((siteQ A Y).obj I') ≫
          ((globalHom A P).obj (op ((pull A a).obj ((siteQ A X).obj E) ⊗
            (pull A b).obj ((siteQ A Y).obj H)))).map
              (targetModel A a b N I M I' J c c' i) =
        Functor.LaxMonoidal.μ (moduleQ A) U V ≫ (moduleQ A).map κ ≫
          mG.iso.hom ≫ ((globalHom A P).map (externalModel A a b E H).op).app
            ((siteQ A P).obj J)

/-- The morphism on global derived Hom, with both variances explicit.
Source: Stacks 08J9 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def homMap {X : Scheme.{u}} {E E' K K' : DerivedCategoryModule A X}
    (f : E' ⟶ E) (g : K ⟶ K') :
    ((globalHom A X).obj (op E)).obj K ⟶ ((globalHom A X).obj (op E')).obj K' :=
  ((globalHom A X).map f.op).app K ≫ ((globalHom A X).obj (op E')).map g

/-- The external tensor of two derived objects via the recorded inverse images.
Source: Stacks 06YS (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev external {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (K : DerivedCategoryModule A X) (L' : DerivedCategoryModule A Y) :=
  (pull A a).obj K ⊗ (pull A b).obj L'

/-- Bounded below in the ambient unbounded derived category.
Source: Stacks 05RR (blueprint: lem-pur-external-rhom-cone-pairing). -/
def IsPlus {X : Scheme.{u}} (K : DerivedCategoryModule A X) : Prop :=
  ∃ n : ℤ, _root_.DerivedCategory.IsGE K n

/-- A coefficient object with a bounded flat complex representative.
Source: Stacks 06YQ (blueprint: lem-pur-external-rhom-cone-pairing). -/
def HasBoundedFlatModel {X : Scheme.{u}} (E : DerivedCategoryModule A X) : Prop :=
  ∃ C : Complexes A X, IsBoundedFlat A C ∧ Nonempty ((siteQ A X).obj C ≅ E)

/-- Simultaneous naturality in both coefficient and both target variables.
Source: Stacks 08J9 (blueprint: lem-pur-external-rhom-cone-pairing). -/
def IsNatural : Prop :=
  ∀ (X Y P : Scheme.{u}) (a : P ⟶ X) (b : P ⟶ Y)
    (E E' K K' : DerivedCategoryModule A X) (H H' L' L'' : DerivedCategoryModule A Y),
    HasBoundedFlatModel A E → HasBoundedFlatModel A E' →
    HasBoundedFlatModel A H → HasBoundedFlatModel A H' →
    IsPlus A K → IsPlus A K' → IsPlus A L' → IsPlus A L'' →
    IsPlus A (external A a b K L') → IsPlus A (external A a b K' L'') →
    ∀ (f : E' ⟶ E) (g : H' ⟶ H) (k : K ⟶ K') (l : L' ⟶ L''),
      (homMap A f k ⊗ₘ homMap A g l) ≫ pairing A a b E' K' H' L'' =
        pairing A a b E K H L' ≫
          homMap A ((pull A a).map f ⊗ₘ (pull A b).map g)
            ((pull A a).map k ⊗ₘ (pull A b).map l)

/-- The comparison of inverse images around a commuting square.
Source: Stacks 03D8 (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def squarePullIso {X X' P P' : Scheme.{u}}
    (a : P ⟶ X) (j : X' ⟶ X) (p : P' ⟶ P) (a' : P' ⟶ X')
    (h : p ≫ a = a' ≫ j) (E : DerivedCategoryModule A X) :
    (pull A p).obj ((pull A a).obj E) ≅ (pull A a').obj ((pull A j).obj E) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p a).symm.app E ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a' j (p ≫ a) h).app E

/-- The canonical coefficient comparison in an open-restriction square.
Source: Stacks 08JB and 0G7E (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def restrictionTensorIso {X X' Y Y' P P' : Scheme.{u}}
    (a : P ⟶ X) (b : P ⟶ Y) (j : X' ⟶ X) (k : Y' ⟶ Y)
    (p : P' ⟶ P) (a' : P' ⟶ X') (b' : P' ⟶ Y')
    (ha : p ≫ a = a' ≫ j) (hb : p ≫ b = b' ≫ k)
    (E : DerivedCategoryModule A X) (H : DerivedCategoryModule A Y) :
    (pull A p).obj (external A a b E H) ≅
      external A a' b' ((pull A j).obj E) ((pull A k).obj H) :=
  (pullTensorIso A p _ _).symm ≪≫
    (squarePullIso A a j p a' ha E ⊗ᵢ squarePullIso A b k p b' hb H)

/-- The canonical restriction square for a commuting diagram of inverse images.
Source: Stacks 08JB (blueprint: lem-pur-external-rhom-cone-pairing). -/
def RestrictionSquare {X X' Y Y' P P' : Scheme.{u}}
    (a : P ⟶ X) (b : P ⟶ Y) (j : X' ⟶ X) (k : Y' ⟶ Y)
    (p : P' ⟶ P) (a' : P' ⟶ X') (b' : P' ⟶ Y')
    (ha : p ≫ a = a' ≫ j) (hb : p ≫ b = b' ≫ k)
    (E K : DerivedCategoryModule A X) (H L' : DerivedCategoryModule A Y) : Prop :=
  (restriction A j E K ⊗ₘ restriction A k H L') ≫
      pairing A a' b' ((pull A j).obj E) ((pull A j).obj K)
        ((pull A k).obj H) ((pull A k).obj L') =
    pairing A a b E K H L' ≫ restriction A p (external A a b E H)
      (external A a b K L') ≫
      homMap A (restrictionTensorIso A a b j k p a' b' ha hb E H).inv
        (restrictionTensorIso A a b j k p a' b' ha hb K L').hom

/-- Open restriction of X or Y, with the induced pullback open of P.
Identity and empty open immersions are allowed.
Source: Stacks 08JB (blueprint: lem-pur-external-rhom-cone-pairing). -/
def CommutesWithOpenRestriction : Prop :=
  (∀ (X X' Y P P' : Scheme.{u})
    (a : P ⟶ X) (b : P ⟶ Y) (j : X' ⟶ X) (p : P' ⟶ P) (a' : P' ⟶ X')
    [IsOpenImmersion j] (sq : IsPullback p a' a j)
    (E K : DerivedCategoryModule A X) (H L' : DerivedCategoryModule A Y),
    HasBoundedFlatModel A E → HasBoundedFlatModel A H →
    IsPlus A K → IsPlus A L' → IsPlus A (external A a b K L') →
    RestrictionSquare A a b j (𝟙 Y) p a' (p ≫ b) sq.w (by simp) E K H L') ∧
  (∀ (X Y Y' P P' : Scheme.{u})
    (a : P ⟶ X) (b : P ⟶ Y) (k : Y' ⟶ Y) (p : P' ⟶ P) (b' : P' ⟶ Y')
    [IsOpenImmersion k] (sq : IsPullback p b' b k)
    (E K : DerivedCategoryModule A X) (H L' : DerivedCategoryModule A Y),
    HasBoundedFlatModel A E → HasBoundedFlatModel A H →
    IsPlus A K → IsPlus A L' → IsPlus A (external A a b K L') →
    RestrictionSquare A a b (𝟙 X) k p (p ≫ a) b' (by simp) sq.w E K H L')

open CategoryTheory.Pretriangulated.Opposite

/-- Contravariant global derived Hom with fixed target.
Source: Stacks 08JC (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev homFirst (X : Scheme.{u}) (K : DerivedCategoryModule A X) :
    (DerivedCategoryModule A X)ᵒᵖ ⥤ DerivedCategory (ModuleCat.{u + 1} A) :=
  (globalHom A X).flip.obj K

/-- Exact inverse image carries the shift comparison transported from termwise inverse image.
Source: Stacks 0G7E (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable instance pullCommShift {X P : Scheme.{u}} (a : P ⟶ X) :
    (pull A a).CommShift ℤ :=
  Functor.CommShift.ofIso
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) a).symm ℤ

variable [homShift : ∀ (X : Scheme.{u}) (K : DerivedCategoryModule A X),
  (homFirst A X K).CommShift ℤ]

/-- The negative shift of contravariant Hom, with the canonical opposite-shift
comparison written explicitly. Source: Stacks 08JC
(blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable def negativeHomShiftIsoOf
    {C : Type uC} [Category.{vC} C] [HasShift C ℤ]
    {D : Type uD} [Category.{vD} D] [HasShift D ℤ]
    (F : Cᵒᵖ ⥤ D) [F.CommShift ℤ] (E : C) :
    F.obj (op (E⟦(1 : ℤ)⟧)) ≅ (F.obj (op E))⟦(-1 : ℤ)⟧ :=
  (F.mapIso ((Pretriangulated.shiftFunctorOpIso C (-1) 1 (by decide)).app (op E)).symm) ≪≫
    (F.commShiftIso (-1 : ℤ)).app (op E)

/-- The signed Hom shift is natural in every target morphism and is fixed on
all K-injective cochain models. Naturality transports the normalization along every
isomorphism to a K-injective representative, including the external tensor target.
Source: Stacks 0A8X and 08JC (blueprint: lem-pur-external-rhom-cone-pairing). -/
def HasSignedHomShift : Prop :=
  (∀ (X : Scheme.{u}) (K K' : DerivedCategoryModule A X) (k : K ⟶ K'),
    NatTrans.CommShift ((globalHom A X).flip.map k) ℤ) ∧
  ∀ (X : Scheme.{u}) (E I : Complexes A X) [I.IsKInjective],
    IsPlus A ((siteQ A X).obj I) →
    ∀ (m : HomModel A E I) (m' : HomModel A (E⟦(1 : ℤ)⟧) I),
    ∃ θ : homComplex A (E⟦(1 : ℤ)⟧) I ≅ (homComplex A E I)⟦(-1 : ℤ)⟧,
      (∀ (n : ℤ) (f : (homComplex A (E⟦(1 : ℤ)⟧) I).X n),
        ((homComplex A E I).shiftFunctorObjXIso (-1) n (n + -1) rfl).hom
          (θ.hom.f n f) =
        f.leftUnshift (n + -1) (by omega)) ∧
      m'.iso.hom ≫
          homMap A ((((siteQ A X).commShiftIso (1 : ℤ)).app E).inv) (𝟙 _) ≫
          (negativeHomShiftIsoOf (homFirst A X ((siteQ A X).obj I))
            ((siteQ A X).obj E)).hom =
        (moduleQ A).map θ.hom ≫
          (((moduleQ A).commShiftIso (-1 : ℤ)).app (homComplex A E I)).hom ≫
          m.iso.hom⟦(-1 : ℤ)⟧'

/-- The source functor in the first coefficient.
The native tensorRight shift has no sign on homogeneous tensors.
Source: Stacks 08JC (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev leftSource {X Y : Scheme.{u}} (K : DerivedCategoryModule A X)
    (H L' : DerivedCategoryModule A Y) :=
  homFirst A X K ⋙ tensorRight (((globalHom A Y).obj (op H)).obj L')

/-- The target functor in the first coefficient.
Source: Stacks 08JC (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev leftTarget {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (K : DerivedCategoryModule A X) (H L' : DerivedCategoryModule A Y) :=
  (pull A a ⋙ tensorRight ((pull A b).obj H)).op ⋙ homFirst A P (external A a b K L')

/-- The source functor in the second coefficient.
The native tensorLeft shift is multiplication by (-1)^deg(x).
Source: Stacks 08JC (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev rightSource {X Y : Scheme.{u}} (E K : DerivedCategoryModule A X)
    (L' : DerivedCategoryModule A Y) :=
  homFirst A Y L' ⋙ tensorLeft (((globalHom A X).obj (op E)).obj K)

/-- The target functor in the second coefficient.
Source: Stacks 08JC (blueprint: lem-pur-external-rhom-cone-pairing). -/
noncomputable abbrev rightTarget {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
    (E K : DerivedCategoryModule A X) (L' : DerivedCategoryModule A Y) :=
  (pull A b ⋙ tensorLeft ((pull A a).obj E)).op ⋙ homFirst A P (external A a b K L')

/-- The native braiding is normalized by the Koszul braiding on all K-flat models.
Source: Stacks 0A90 (blueprint: lem-pur-external-rhom-cone-pairing). -/
def HasKoszulBraiding : Prop :=
  ∀ (X : Scheme.{u}) (E H : Complexes A X),
    CochainComplex.IsKFlatIndependentCoefficients
      (J := X.smallEtaleTopology) (R := realizationRing X.smallEtaleTopology A)
      ((ringedComplex A X).obj E) →
    CochainComplex.IsKFlatIndependentCoefficients
      (J := X.smallEtaleTopology) (R := realizationRing X.smallEtaleTopology A)
      ((ringedComplex A X).obj H) →
    IsBraidedAt (siteQ A X) E H

/-- Both coefficient-cone assertions, including each prescribed third component and
therefore the connecting square. Opposite distinguished triangles encode the
contravariant Hom triangle with its canonical rotation sign.
Source: Stacks 08JC (blueprint: lem-pur-external-rhom-cone-pairing). -/
def PreservesCoefficientCones : Prop :=
  ∀ (X Y P : Scheme.{u}) (a : P ⟶ X) (b : P ⟶ Y)
    (K : DerivedCategoryModule A X) (L' : DerivedCategoryModule A Y),
    IsPlus A K → IsPlus A L' → IsPlus A (external A a b K L') →
    (∀ (H : DerivedCategoryModule A Y), HasBoundedFlatModel A H →
      ∀ (T : Pretriangulated.Triangle (DerivedCategoryModule A X)ᵒᵖ),
      T ∈ Pretriangulated.distinguishedTriangles →
      HasBoundedFlatModel A T.obj₁.unop → HasBoundedFlatModel A T.obj₂.unop →
      HasBoundedFlatModel A T.obj₃.unop →
      (leftSource A K H L').mapTriangle.obj T ∈ Pretriangulated.distinguishedTriangles ∧
      (leftTarget A a b K H L').mapTriangle.obj T ∈ Pretriangulated.distinguishedTriangles ∧
      ∃ τ : (leftSource A K H L').mapTriangle.obj T ⟶
        (leftTarget A a b K H L').mapTriangle.obj T,
        τ.hom₁ = pairing A a b T.obj₁.unop K H L' ∧
        τ.hom₂ = pairing A a b T.obj₂.unop K H L' ∧
        τ.hom₃ = pairing A a b T.obj₃.unop K H L') ∧
    (∀ (E : DerivedCategoryModule A X), HasBoundedFlatModel A E →
      ∀ (T : Pretriangulated.Triangle (DerivedCategoryModule A Y)ᵒᵖ),
      T ∈ Pretriangulated.distinguishedTriangles →
      HasBoundedFlatModel A T.obj₁.unop → HasBoundedFlatModel A T.obj₂.unop →
      HasBoundedFlatModel A T.obj₃.unop →
      (rightSource A E K L').mapTriangle.obj T ∈ Pretriangulated.distinguishedTriangles ∧
      (rightTarget A a b E K L').mapTriangle.obj T ∈ Pretriangulated.distinguishedTriangles ∧
      ∃ τ : (rightSource A E K L').mapTriangle.obj T ⟶
        (rightTarget A a b E K L').mapTriangle.obj T,
        τ.hom₁ = pairing A a b E K T.obj₁.unop L' ∧
        τ.hom₂ = pairing A a b E K T.obj₂.unop L' ∧
        τ.hom₃ = pairing A a b E K T.obj₃.unop L')

/-- External global derived Hom evaluation, with its chain normalization and both
coefficient-cone compatibilities.

Source: Stacks 08J9, 08JA, 08JB, 08JC, 0A90, 0G7D and 0G7E;
blueprint main-20261015, lem-pur-kunneth-supported proof paragraphs 1 and 3
(blueprint: lem-pur-external-rhom-cone-pairing).

Proof: Use the existing derived constant/sections and tensor/Hom adjunctions to
transpose the tensor of the two pulled evaluations. Resolve the targets by
K-injectives and their global Hom complexes by flat-term K-flat complexes.
The evaluation identity identifies their localized evaluations with the
adjunction counits. Factor each chain evaluation through a flat-term K-flat
complex by Stacks 0G7D. Pull these two complexes to P, tensor them, and resolve
that tensor by J. The Koszul interchange of the second Hom factor of degree s
with the first coefficient of degree q supplies (-1)^(s*q). The two homotopies
to the original evaluations become equalities after localization, proving
that every such chain map is the same transpose. Evaluation naturality proves
all four naturalities and the open-restriction square. Hom into K-injectives,
derived sections, pullback and tensor carry distinguished triangles to
triangles. The first-variable Hom shift sends a degree n cochain f to
(-1)^n f with its coefficient index shifted by -1. For the E shift the two
chain evaluation composites have sign (-1)^(s*q+s); for the H shift they
have sign (-1)^(s*q+q+r). These give the shift squares with, respectively,
the unsigned right-tensor comparison and the (-1)^r left-tensor comparison.
Naturality at the connecting morphism together with these shift squares
proves the third square for the specified cone component in both variables.
The braiding is the existing derived Koszul braiding. The Hom-shift witness
is natural in every target morphism; its representative normalization therefore
transports to the external tensor target as well as K-injective objects. -/
theorem external_rhom_cone_pairing :
    ∃ S : ∀ (X : Scheme.{u}) (K : DerivedCategoryModule A X),
        (homFirst A X K).CommShift ℤ,
      HasKoszulBraiding A ∧
      HasSignedHomShift (homShift := S) A ∧
      (∀ (X : Scheme.{u}) (E I : Complexes A X) [I.IsKInjective],
        IsPlus A ((siteQ A X).obj I) → Nonempty (HomModel A E I)) ∧
      (∀ (X Y P : Scheme.{u}) (a : P ⟶ X) (b : P ⟶ Y)
        (E : Complexes A X) (H : Complexes A Y)
        (I : Complexes A X) (I' : Complexes A Y) [I.IsKInjective] [I'.IsKInjective],
        IsBoundedFlat A E → IsBoundedFlat A H →
        IsPlus A ((siteQ A X).obj I) → IsPlus A ((siteQ A Y).obj I') →
        IsPlus A (external A a b ((siteQ A X).obj I) ((siteQ A Y).obj I')) →
        HasChainNormalization A a b E H I I') ∧
      IsNatural A ∧ CommutesWithOpenRestriction A ∧
      PreservesCoefficientCones (homShift := S) A := by
  sorry

end AlgebraicGeometry.Etale.ExternalRHom
