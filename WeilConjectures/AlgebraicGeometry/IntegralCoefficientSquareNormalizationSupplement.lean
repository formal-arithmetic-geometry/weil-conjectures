/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.HomologicalComplex
public import WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealizationExactSupplement
public import WeilConjectures.AlgebraicGeometry.CartesianCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat
import WeilConjectures.Algebra.Homology.FlatTermKFlatFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.CategoryTheory.ExtensionIsoQuotientFormula

/-! # Normalized constant-to-integral coefficient pullback

Source: blueprint main-20261015, det-lem-int-tensor-pullback, first paragraph and
Comparison with the Stacks Project; Stacks Tags 093M and 0G7E
(blueprint: lem-sfb-integral-coefficient-square-normalization).

Constant coefficients are represented by their canonical pullback from the point;
constantSchemeIso identifies them with ordinary constant sheaves. All complexes are
integer-indexed and unrestricted. The quotient clause is the pushout description
R tensor_C (C/pi^n) = R/pi^n, including the prescribed quotient projection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralCoefficientSquare

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The discrete constant ring on the point, with its existing monoidal ring structure.
Source: Stacks 093J (blueprint: lem-sfb-integral-coefficient-square-normalization). -/
abbrev constantPoint :=
  (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} A))

/-- Internal modules over the specified coefficients pulled back to a scheme.
Source: blueprint, pulled-back coefficients
(blueprint: lem-sfb-integral-coefficient-square-normalization). -/
abbrev Modules (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (T : Scheme.{u}) := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)

/-- The constant-to-continuous map pulled back from the point; no completion choice.
Source: blueprint, constant-function map
(blueprint: lem-sfb-integral-coefficient-square-normalization). -/
abbrev scalar (T : Scheme.{u}) := AdmissibleScalarRealization.scalarMap A T

/-- Restriction along the specified constant-function map, on all modules.
Source: Stacks 03CS (blueprint: lem-sfb-integral-coefficient-square-normalization). -/
abbrev restriction (T : Scheme.{u}) :
    Modules (Profinite.continuousCoefficientRingObj A) T ⥤ Modules (constantPoint A) T :=
  Mod.comap (scalar A T)

/-- Termwise restriction, retaining the original differential.
Source: Stacks 06YN (blueprint: lem-sfb-integral-coefficient-square-normalization). -/
abbrev restrictComplex (T : Scheme.{u}) :=
  (restriction A T).mapHomologicalComplex (.up ℤ)

/-- The tensor-defined module pullback, applied in every degree.
Source: blueprint, module pullback
(blueprint: lem-sfb-integral-coefficient-square-normalization). -/
abbrev pullComplex (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  (CondensedRing.upperStar Λ g).mapHomologicalComplex (.up ℤ)

/-- The specified extension-to-inverse-image identification on underlying abelian sheaves.
Source: blueprint, Cartesian coefficients
(blueprint: lem-sfb-integral-coefficient-square-normalization). -/
def underlyingIso (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Modules Λ Y) :
    ((CondensedRing.upperStar Λ g).obj M).X ≅
      (upperStar Ab.{u + 1} g).obj M.X :=
  (Mod.forget (condensedRingObj Λ X)).mapIso
    ((cartesianCoefficientPullbackIso Λ g).app M)

/-- Both generator formulas fixing the underlying Cartesian scalar-extension isomorphism.
The first sends r tensor h to alpha inverse(r)h; the second sends h to 1 tensor h.
Source: blueprint, scalar-extension calculation
(blueprint: lem-sfb-integral-coefficient-square-normalization). -/
def GeneratorNormalization (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) : Prop :=
  ∀ M : Modules Λ Y,
    Mod.extendπ (condensedPullbackHom Λ g)
        (((upperStar Ab.{u + 1} g).mapMod _).obj M) ≫ (underlyingIso Λ g M).hom =
      inv (condensedPullbackHom Λ g) ▷ (upperStar Ab.{u + 1} g).obj M.X ≫
        γ[(upperStar Ab.{u + 1} g).obj (condensedRingObj Λ Y),
          (upperStar Ab.{u + 1} g).obj M.X] ∧
    (underlyingIso Λ g M).inv = Mod.extendUnitHom (condensedPullbackHom Λ g)
      (((upperStar Ab.{u + 1} g).mapMod _).obj M)

/-- K-flatness and flat terms in the existing section-module presentation.
This uses the recorded predicates, rather than another definition of K-flatness or flatness.
Source: Stacks 06YN and 03ER
(blueprint: lem-sfb-integral-coefficient-square-normalization). -/
def FlatKFlat (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    (P : CochainComplex (Modules Λ T) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
    (((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
      (condensedRingObj Λ T)).functor.mapHomologicalComplex (.up ℤ)).obj P) ∧
  ∀ q : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
    ((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
      (condensedRingObj Λ T)).functor.obj (P.X q))

/-- The actual completed ring, identified by its constant scalar projections, with its
normalized quotient squares. The pushout is precisely the ring quotient by pi^(n+1).
Source: Stacks 093M; blueprint integral-limit paragraph
(blueprint: lem-sfb-integral-coefficient-square-normalization). -/
def RingAssertions (p : A) (T : Scheme.{u}) : Prop :=
  ∃ e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T)
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) T) ≅
      Scheme.adicLisseCompletedRing T
        (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))),
    (∀ (U : T.ProEtᵒᵖ) (a : A) (n : ℕ),
      ((limit.π (Scheme.adicLisseRingSystem T
        (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)))) (op n)).hom.app U)
        ((e.hom.hom.app U)
          ((FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app U
            ((toSheafify (D := Ab.{u + 1}) (Scheme.ProEt.topology T)
              ((Functor.const T.ProEtᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{u + 1} A)))).app U (ULift.up a)))) =
      (toSheafify (D := CommRingCat.{u + 1}) (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
          (ULift.{u + 1} A ⧸
            Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)) ^ (n + 1))))).app U
        (Ideal.Quotient.mk
          (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)) ^ (n + 1)) (ULift.up a))) ∧
    ∀ n : ℕ, IsPushout
      (Scheme.CompletedConstantReduction.base T
        (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))) ≫ e.inv)
      ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)) ^ (n + 1)))))
      (e.hom ≫ limit.π (Scheme.adicLisseRingSystem T
        (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)))) (op n)) (𝟙 _)

/-- All clauses for the actual coefficient ring, square, chain comparison and flat K-flat
pullbacks. The natural isomorphism is on whole cochain complexes, with normalization in
all integer degrees; there is no boundedness, completeness or constructibility condition.
Source: blueprint det-lem-int-tensor-pullback; Stacks 093M and 0G7E
(blueprint: lem-sfb-integral-coefficient-square-normalization). -/
def Assertions (p : A) {X Y : Scheme.{u}} (g : X ⟶ Y) : Prop :=
  RingAssertions A p X ∧ RingAssertions A p Y ∧
  (∀ T : Scheme.{u}, T = X ∨ T = Y → SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
    ((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
      (condensedRingObj (constantPoint A) T)).functor.obj
      ((restriction A T).obj
        (Mod.regular (condensedRingObj (Profinite.continuousCoefficientRingObj A) T))))) ∧
  (upperStar Ab.{u + 1} g).map (scalar A Y) ≫
      condensedPullbackHom (Profinite.continuousCoefficientRingObj A) g =
    condensedPullbackHom (constantPoint A) g ≫ scalar A X ∧
  GeneratorNormalization (Profinite.continuousCoefficientRingObj A) g ∧
  GeneratorNormalization (constantPoint A) g ∧
  (∃ d : pullComplex (Profinite.continuousCoefficientRingObj A) g ⋙ restrictComplex A X ≅
      restrictComplex A Y ⋙ pullComplex (constantPoint A) g,
    ∀ (H : CochainComplex (Modules (Profinite.continuousCoefficientRingObj A) Y) ℤ)
      (q : ℤ),
      ((d.hom.app H).f q).hom ≫
          (underlyingIso (constantPoint A) g ((restriction A Y).obj (H.X q))).hom =
        (underlyingIso (Profinite.continuousCoefficientRingObj A) g (H.X q)).hom) ∧
  exactFunctor _ _ (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A) g) ∧
  exactFunctor _ _ (CondensedRing.upperStar (constantPoint A) g) ∧
  ∀ P : CochainComplex (Modules (Profinite.continuousCoefficientRingObj A) Y) ℤ,
    FlatKFlat (Profinite.continuousCoefficientRingObj A) Y P →
    FlatKFlat (constantPoint A) Y ((restrictComplex A Y).obj P) ∧
    FlatKFlat (Profinite.continuousCoefficientRingObj A) X
      ((pullComplex (Profinite.continuousCoefficientRingObj A) g).obj P) ∧
    FlatKFlat (constantPoint A) X
      ((pullComplex (constantPoint A) g).obj ((restrictComplex A Y).obj P))

/-- Specialize to the chosen finite extension and its chosen uniformizer, with the
spectral absolute-value topology, without adding topological hypotheses.
Source: blueprint coefficient-extension setting
(blueprint: lem-sfb-integral-coefficient-square-normalization). -/
def IntegralAssertions (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) : Prop :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Assertions (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E) g

attribute [local irreducible] Mod.extendScalarsObj Mod.extendScalarsIsoComapInv
attribute [local irreducible] upperStarFromPoint upperStarFromPointComp upperStar
attribute [local irreducible] FiniteConstantModel.scalarToContinuous
set_option backward.isDefEq.respectTransparency.types false

private theorem completed_quotient_pushout (T : Scheme.{u})
    {B : Type (u + 1)} [CommRing B] [IsNoetherianRing B] (I : Ideal B) (n : ℕ) :
    IsPushout (Scheme.CompletedConstantReduction.base T I)
      ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
      (limit.π (Scheme.adicLisseRingSystem T I) (op n)) (𝟙 _) := by
  classical
  let c := Scheme.CompletedConstantReduction.base T I
  let q := (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))
  let π := limit.π (Scheme.adicLisseRingSystem T I) (op n)
  have hc : ∀ m : ℕ, c ≫ limit.π (Scheme.adicLisseRingSystem T I) (op m) =
      (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (m + 1)))) :=
    (Scheme.CompletedConstantReduction.base_exists T I).choose_spec.1
  have hw : c ≫ π = q ≫ 𝟙 _ := (hc n).trans (Category.comp_id q).symm
  have hπ := Scheme.CompletedConstantAlgebra.projection_surjective_and_kernel T I
    (Iso.refl _) c (by simpa only [Iso.refl_inv, Category.id_comp] using hc)
    n (Iso.refl _) π (by
      change π = π ≫ 𝟙 _
      exact (Category.comp_id _).symm)
  apply IsPushout.of_isColimit
    (c := PushoutCocone.mk π (𝟙 _) hw)
  apply PushoutCocone.isColimitAux'
  intro s
  have hker (U : T.ProEtᵒᵖ) :
      RingHom.ker (π.hom.app U).hom ≤ RingHom.ker (s.inl.hom.app U).hom := by
    let : Algebra ((Scheme.adicLisseCompletedRing T I).obj.obj U)
        (s.pt.obj.obj U) := (s.inl.hom.app U).hom.toAlgebra
    let f : (Scheme.adicLisseCompletedRing T I).obj.obj U →ₗ[
        (Scheme.adicLisseCompletedRing T I).obj.obj U] s.pt.obj.obj U :=
      { toFun := s.inl.hom.app U
        map_add' := (s.inl.hom.app U).hom.map_add
        map_smul' := fun r x ↦ (s.inl.hom.app U).hom.map_mul r x }
    intro b hb
    apply (hπ U).2 _ f ?_ b hb
    intro a
    have h := congrArg (fun t ↦ t.hom.app U
      ((Scheme.adicLisseConstantUnit T B).app U (a : B))) s.condition
    have hqa : q.hom.app U ((Scheme.adicLisseConstantUnit T B).app U (a : B)) = 0 := by
      have hnat := ConcreteCategory.congr_hom
        (congr_app (toSheafify_naturality (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).map
            (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) U) (a : B)
      change (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (B ⧸ I ^ (n + 1))))).app U
          (Ideal.Quotient.mk (I ^ (n + 1)) (a : B)) =
        q.hom.app U ((Scheme.adicLisseConstantUnit T B).app U (a : B)) at hnat
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr a.property] at hnat
      exact hnat.symm.trans (map_zero _)
    exact h.trans ((congrArg (s.inr.hom.app U) hqa).trans (map_zero _))
  let d (U : T.ProEtᵒᵖ) : ((Scheme.adicLisseRingSystem T I).obj (op n)).obj.obj U →+*
      s.pt.obj.obj U :=
    (π.hom.app U).hom.liftOfSurjective (hπ U).1 ⟨(s.inl.hom.app U).hom, hker U⟩
  have hd (U : T.ProEtᵒᵖ) (b : (Scheme.adicLisseCompletedRing T I).obj.obj U) :
      d U (π.hom.app U b) = s.inl.hom.app U b :=
    RingHom.liftOfSurjective_comp_apply _ _ _ _
  let δ : (Scheme.adicLisseRingSystem T I).obj (op n) ⟶ s.pt :=
    ⟨{ app := fun U ↦ CommRingCat.ofHom (d U)
       naturality := by
        intro U V f
        ext x
        obtain ⟨b, rfl⟩ := (hπ U).1 x
        change d V (((Scheme.adicLisseRingSystem T I).obj (op n)).obj.map f
          (π.hom.app U b)) = s.pt.obj.map f (d U (π.hom.app U b))
        rw [← NatTrans.naturality_apply, hd, hd, NatTrans.naturality_apply] }⟩
  have hleft : π ≫ δ = s.inl := by ext U b; exact hd U b
  have hright : δ = s.inr := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (Scheme.ProEt.topology T) _ _ s.pt.property
    ext U x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hn := ConcreteCategory.congr_hom
      (congr_app (toSheafify_naturality (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) U) a
    have h := congrArg (fun t ↦ t.hom.app U
      ((Scheme.adicLisseConstantUnit T B).app U a)) s.condition
    have he := congrArg (fun t ↦ t.hom.app U
      ((Scheme.adicLisseConstantUnit T B).app U a)) hw
    change (toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (B ⧸ I ^ (n + 1))))).app U
        (Ideal.Quotient.mk (I ^ (n + 1)) a) =
      q.hom.app U ((Scheme.adicLisseConstantUnit T B).app U a) at hn
    change s.inl.hom.app U (c.hom.app U
      ((Scheme.adicLisseConstantUnit T B).app U a)) =
        s.inr.hom.app U (q.hom.app U
          ((Scheme.adicLisseConstantUnit T B).app U a)) at h
    change π.hom.app U (c.hom.app U
      ((Scheme.adicLisseConstantUnit T B).app U a)) =
        q.hom.app U ((Scheme.adicLisseConstantUnit T B).app U a) at he
    change d U ((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (B ⧸ I ^ (n + 1))))).app U
        (Ideal.Quotient.mk (I ^ (n + 1)) a)) =
      s.inr.hom.app U ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (B ⧸ I ^ (n + 1))))).app U
          (Ideal.Quotient.mk (I ^ (n + 1)) a))
    calc
      _ = d U (q.hom.app U ((Scheme.adicLisseConstantUnit T B).app U a)) :=
        congrArg (d U) hn
      _ = d U (π.hom.app U (c.hom.app U
          ((Scheme.adicLisseConstantUnit T B).app U a))) := congrArg (d U) he.symm
      _ = s.inl.hom.app U (c.hom.app U
          ((Scheme.adicLisseConstantUnit T B).app U a)) := hd U _
      _ = s.inr.hom.app U (q.hom.app U
          ((Scheme.adicLisseConstantUnit T B).app U a)) := h
      _ = _ := congrArg (s.inr.hom.app U) hn.symm
  refine ⟨δ, hleft, ?_, ?_⟩
  · exact (Category.id_comp δ).trans hright
  · intro m _ hm
    exact (Category.id_comp m).symm.trans (hm.trans hright.symm)


private theorem generators
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    GeneratorNormalization Λ g := by
  intro M
  have h := Mod.extensionIso_quotient_formula (condensedPullbackHom Λ g)
    (((upperStar Ab.{u + 1} g).mapMod (condensedRingObj Λ Y)).obj M)
  exact ⟨h.2.1, h.2.2.2.1⟩

private def pointScalar : constantPoint A ⟶ Profinite.continuousCoefficientRingObj A :=
  FiniteConstantModel.scalarToContinuous A

private instance pointScalar_isMonHom : IsMonHom (pointScalar A) :=
  inferInstanceAs (IsMonHom (FiniteConstantModel.scalarToContinuous A))

private theorem scalar_square_general
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (upperStar Ab.{u + 1} g).map ((upperStarFromPoint Y).map a) ≫
        condensedPullbackHom Λ' g =
      condensedPullbackHom Λ g ≫ (upperStarFromPoint X).map a :=
  (upperStarFromPointComp g).hom.naturality a

section Comparison
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (g : X ⟶ Y)

omit [IsCommMonObj Λ] [IsCommMonObj Λ'] [IsMonHom a] in
private theorem inverse_square_general :
    (upperStarFromPoint X).map a ≫ inv (condensedPullbackHom Λ' g) =
      inv (condensedPullbackHom Λ g) ≫
        (upperStar Ab.{u + 1} g).map ((upperStarFromPoint Y).map a) := by
  apply (cancel_epi (condensedPullbackHom Λ g)).mp
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [← scalar_square_general a g, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private def comparisonGeneral :
    CondensedRing.upperStar Λ' g ⋙ Mod.comap ((upperStarFromPoint X).map a) ≅
      Mod.comap ((upperStarFromPoint Y).map a) ⋙ CondensedRing.upperStar Λ g :=
  Functor.isoWhiskerRight (cartesianCoefficientPullbackIso Λ' g)
      (Mod.comap ((upperStarFromPoint X).map a)) ≪≫
    Mod.comapMapModComapIso (upperStar Ab.{u + 1} g)
      ((upperStarFromPoint Y).map a) ((upperStarFromPoint X).map a)
      (inv (condensedPullbackHom Λ g)) (inv (condensedPullbackHom Λ' g))
      (inverse_square_general a g) ≪≫
    Functor.isoWhiskerLeft (Mod.comap ((upperStarFromPoint Y).map a))
      (cartesianCoefficientPullbackIso Λ g).symm

private theorem comparisonGeneral_normalization (M : Modules Λ' Y) :
    ((comparisonGeneral a g).hom.app M).hom ≫
        (underlyingIso Λ g ((Mod.comap ((upperStarFromPoint Y).map a)).obj M)).hom =
      (underlyingIso Λ' g M).hom := by
  dsimp only [comparisonGeneral, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Mod.comp_hom', Mod.comap_map_hom]
  rw [Mod.comapMapModComapIso_hom_app_hom]
  change ((underlyingIso Λ' g M).hom ≫ 𝟙 _) ≫
    (underlyingIso Λ g ((Mod.comap ((upperStarFromPoint Y).map a)).obj M)).inv ≫
    (underlyingIso Λ g ((Mod.comap ((upperStarFromPoint Y).map a)).obj M)).hom =
      (underlyingIso Λ' g M).hom
  rw [Category.comp_id, Iso.inv_hom_id, Category.comp_id]
end Comparison

private theorem scalar_square {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (upperStar Ab.{u + 1} g).map (scalar A Y) ≫
        condensedPullbackHom (Profinite.continuousCoefficientRingObj A) g =
      condensedPullbackHom (constantPoint A) g ≫ scalar A X :=
  scalar_square_general (pointScalar A) g

private def moduleComparison {X Y : Scheme.{u}} (g : X ⟶ Y) :
    CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A) g ⋙ restriction A X ≅
      restriction A Y ⋙ CondensedRing.upperStar (constantPoint A) g :=
  comparisonGeneral (pointScalar A) g

private theorem moduleComparison_normalization {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Modules (Profinite.continuousCoefficientRingObj A) Y) :
    ((moduleComparison A g).hom.app M).hom ≫
        (underlyingIso (constantPoint A) g ((restriction A Y).obj M)).hom =
      (underlyingIso (Profinite.continuousCoefficientRingObj A) g M).hom :=
  comparisonGeneral_normalization (pointScalar A) g M

private theorem flat_restricted_regular
    (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [PreservesFiniteLimits (Mod.extendScalars φ)] :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      ((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
        R).functor.obj ((Mod.comap φ).obj (Mod.regular S))) := by
  let N := (Mod.comap φ).obj (Mod.regular S)
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft N ⋙ Mod.forget R) :=
    preservesFiniteLimits_of_natIso (Mod.extendForgetTensorIso φ)
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft N) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (Mod.forget R)
  exact (InternalAbelianSheafModule.flat_iff_sectionModule
    (Scheme.ProEt.topology T) R N).mp
      ((ObjectProperty.flat_iff_preservesFiniteLimits N).mpr inferInstance)

private theorem restriction_flatKFlat
    (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ]
    (hB : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      ((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
        R).functor.obj ((Mod.comap φ).obj (Mod.regular S))))
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) S) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
        S).functor.mapHomologicalComplex (.up ℤ)).obj P))
    (hf : ∀ q, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      ((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
        S).functor.obj (P.X q))) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
        R).functor.mapHomologicalComplex (.up ℤ)).obj
          (((Mod.comap φ).mapHomologicalComplex (.up ℤ)).obj P)) ∧
    ∀ q, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      ((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
        R).functor.obj ((Mod.comap φ).obj (P.X q))) := by
  let J := Scheme.ProEt.topology T
  let eR := InternalAbelianSheafModule.sectionModuleEquivalence J R
  let eS := InternalAbelianSheafModule.sectionModuleEquivalence J S
  let α := CondensedRing.sectionRingMap T φ
  let U := SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)
  let β := CondensedRing.sectionModuleComapIso T φ
  let b := β.app (Mod.regular S) ≪≫ U.mapIso (CondensedRing.sectionModuleRegularIso T S)
  have hb := SheafOfModules.flatOnSite_of_iso _ b hB
  have h := SheafOfModules.isKFlat_restrictScalars_of_flat α hb
    ((eS.functor.mapHomologicalComplex (.up ℤ)).obj P) hP
  let d := (NatIso.mapHomologicalComplex β (.up ℤ)).app P
  exact ⟨SheafOfModules.kFlat_iso_independent _ d.symm h.1,
    fun q ↦ SheafOfModules.flatOnSite_of_iso _ (β.app (P.X q)).symm (h.2 hf q)⟩

universe v w

private theorem internal_kflat_iff
    {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    (K : CochainComplex C ℤ) :
    (∀ P : CochainComplex C ℤ, P.Acyclic →
      (CochainComplex.mapBifunctor P K (curriedTensor C)).Acyclic) ↔
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff, HomotopyCategory.kFlat_iff_preserves_acyclic]
  constructor
  · intro h Z hZ
    obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hZ
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor Z K (curriedTensor C))).2 (h Z hZ)
    exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hr, hr⟩
  · intro h P hP
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
      (h _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic P).2 hP)).2

private theorem pull_flatKFlat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (Modules Λ Y) ℤ) (hP : FlatKFlat Λ Y P) :
    FlatKFlat Λ X ((pullComplex Λ g).obj P) := by
  let F := CondensedRing.upperStar Λ g
  have hK (T : Scheme.{u}) := InternalAbelianSheafModule.comparison_kflat
    (Scheme.ProEt.topology T) (condensedRingObj Λ T)
  have : (cartesianCoefficientLift Λ g).PreservesFlat :=
    inverseImageModule_preservesFlat g (condensedRingObj Λ Y) (condensedRingObj Λ X)
      (inv (condensedPullbackHom Λ g))
  have : F.PreservesFlat := ⟨fun {M} hM ↦ ObjectProperty.prop_of_iso _
    ((cartesianCoefficientPullbackIso Λ g).app M).symm
      (Functor.PreservesFlat.flat_obj (F := cartesianCoefficientLift Λ g) hM)⟩
  have hp := (internal_kflat_iff P).mp ((hK Y P).mpr hP.1)
  have hf (q : ℤ) : ObjectProperty.flat (P.X q) :=
    (InternalAbelianSheafModule.flat_iff_sectionModule
      (Scheme.ProEt.topology Y) (condensedRingObj Λ Y) _).mpr (hP.2 q)
  have hk := F.kFlat_map_of_flat_terms P hp hf
  exact ⟨(hK X _).mp ((internal_kflat_iff _).mpr hk),
    fun q ↦ (InternalAbelianSheafModule.flat_iff_sectionModule
      (Scheme.ProEt.topology X) (condensedRingObj Λ X) _).mp
        (Functor.PreservesFlat.flat_obj (F := F) (hf q))⟩

private theorem ring_assertions_of_completed [IsNoetherianRing A] (p : A)
    (T : Scheme.{u}) (h : AdmissibleScalarRealization.CompletedIdentification A T p) :
    RingAssertions A p T := by
  obtain ⟨e, he, _⟩ := h
  refine ⟨e, he, ?_⟩
  have : IsNoetherianRing (ULift.{u + 1} A) :=
    isNoetherianRing_of_ringEquiv A ULift.ringEquiv.symm
  intro n
  exact (completed_quotient_pushout T
    (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))) n).of_iso
      (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)

private theorem assertions_of_completed [IsNoetherianRing A] (π : A)
    (hcompleted : ∀ T : Scheme.{u}, AdmissibleScalarRealization.CompletedAssertions A T π)
    {X Y : Scheme.{u}} (g : X ⟶ Y) : Assertions A π g := by
  refine ⟨ring_assertions_of_completed A π X (hcompleted X).1,
    ring_assertions_of_completed A π Y (hcompleted Y).1,
    ?_, scalar_square A g, generators _ _, generators _ _, ?_,
    (exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩,
    (exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩, ?_⟩
  · intro T _
    have := (hcompleted T).2.1
    exact flat_restricted_regular T (scalar A T)
  · let d := NatIso.mapHomologicalComplex (moduleComparison A g) (.up ℤ)
    refine ⟨d, ?_⟩
    intro H q
    exact moduleComparison_normalization A g (H.X q)
  · intro P hP
    have hflat := (hcompleted Y).2.1
    have hres : FlatKFlat (constantPoint A) Y ((restrictComplex A Y).obj P) :=
      restriction_flatKFlat Y (scalar A Y)
        (flat_restricted_regular Y (scalar A Y)) P hP.1 hP.2
    exact ⟨hres, pull_flatKFlat _ g P hP,
      pull_flatKFlat _ g ((restrictComplex A Y).obj P) hres⟩

/-- The normalized constant-to-integral square and flat K-flat pullback assertions.
Source: blueprint main-20261015, det-lem-int-tensor-pullback, first paragraph and
Comparison with the Stacks Project; Stacks 093M and 0G7E
(blueprint: lem-sfb-integral-coefficient-square-normalization).

Proof:
1. Use lem-sfb-integers-profinite-tower and lem-sfb-integers-coset-basis for the compact
Hausdorff integers and finite quotient fibres. Apply
lem-sfb-compact-adic-continuous-identification separately on X and Y; its constant
projection equation identifies the scalar map with the completion base map.
2. Apply lem-sfb-admissible-scalar-realization-exact for Noetherian scalars and
lem-weil-pbc-completed-constant-algebra-flat-quotients for flatness and each quotient.
The balanced inverse maps r tensor a-bar to i(a)r modulo pi^n and r-bar to r tensor 1
identify the pushout with R/pi^n, carrying the quotient map to the specified projection.
3. Naturality of sk-def-sfb-coefficient-morphisms at the discrete-to-adic map gives
alpha_R g-inverse(i_Y) = i_X alpha_C. The constant comparison is the canonical
scalar-preserving comparison of def-sfb-constant-sheaf-scheme-pullback-comparison.
4. On scalar-extension generators put m_R(r tensor h)=alpha_R inverse(r)h and
u_R(h)=1 tensor h. Balancing and the two inverse identities follow from the tensor
relations; the same calculation applies to C. This normalizes underlyingIso.
5. The square makes d=u_C m_R C_X-linear. The generator formulas commute with every
module map and hence every differential; they define a natural chain isomorphism in
all integer degrees, including unbounded complexes.
6. Exactness follows from sk-prop-sfb-cartesian-coefficients and
lem-pe-constant-left-module-inverse-image, through the normalized identifications.
7. Apply lem-weil-pbc-flat-scalar-restriction-kflat to the flat map i_Y and P.
8. Apply lem-weil-pbc-ringed-topos-kflat-pullback twice, to P over R and to its scalar
restriction over C. Both give K-flatness and flat terms with no boundedness assumption.
-/
theorem integral_coefficient_square_normalization
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (_hp : p ≠ l) (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (g : X ⟶ Y) : IntegralAssertions l E g.left := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  have had (T : Scheme.{u}) :=
    ((AdmissibleScalarRealization.admissible_scalar_realization_exact l T).2.2.1 E).1
  have hdvr := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hπ : Ideal.span ({π} : Set A) = Padic.coefficientExtensionMaximalIdeal l E :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hcompleted (T : Scheme.{u}) := (had T).2 π hπ
  have : IsNoetherianRing A := (had Y.left).1.1
  exact assertions_of_completed A π hcompleted g.left


end AlgebraicGeometry.ProEtale.IntegralCoefficientSquare
