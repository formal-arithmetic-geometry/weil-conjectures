/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteDualitySiteComparison
public import WeilConjectures.AlgebraicGeometry.FinitePointInternalHomEvaluation
public import WeilConjectures.AlgebraicGeometry.CoefficientDuality
public import WeilConjectures.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.AlgebraicGeometry.EtaleConstantProjectionMap
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientPoint
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor

/-! # Shared canonical maps for the finite mapping adjunction

Source: the finite-level adjunction in paragraph 2 of the integral-dualizing proof.
(blueprint: def-sf-finite-mapping-adjunction-data).

These are the existing arrow-list presentations, moved without changing their bodies
so that descent, invertibility and transpose compatibility can be proved separately.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- A list of fully specified arrows has the specified composite. Endpoints are
carried by Arrow, so the definition expresses ordinary composition in a category.
Source: blueprint integral-dualizing proof, paragraph 2
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def FiniteMappingComposite {C : Type v} [Category.{u} C] :
    List (Arrow C) → Arrow C → Prop
  | [], result => ∃ V : C, result = Arrow.mk (𝟙 V)
  | first :: rest, result =>
    ∃ (V W Z : C) (f : V ⟶ W) (g : W ⟶ Z),
      first = Arrow.mk f ∧ FiniteMappingComposite rest (Arrow.mk g) ∧
        result = Arrow.mk (f ≫ g)

/-- Two specified arrow lists have the same composite, including their endpoints.
Source: blueprint integral-dualizing proof, paragraph 2
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def FiniteMappingSameComposite {C : Type v} [Category.{u} C]
    (left right : List (Arrow C)) : Prop :=
  ∃ result : Arrow C, FiniteMappingComposite left result ∧
    FiniteMappingComposite right result

/-- Map an arrow by a specified functor, retaining its endpoints.
Source: blueprint integral-dualizing proof, paragraph 2
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def finiteMappingArrowMap {C : Type v} [Category.{u} C]
    {B : Type w} [Category.{t} B] (F : C ⥤ B) (f : Arrow C) : Arrow B :=
  Arrow.mk (F.map f.hom)

/-- The ordinary global comparison, with its derived-unit normalization. It is defined
before asserting invertibility, so no boundedness assumption enters the construction.
Source: blueprint finite site/global comparison, paragraph 2
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def finiteMappingGlobalComparison (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u})
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} A) X).map
      ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app K) ≫
    (ProEtale.comparisonLowerStarCompRightDerivedGlobalSectionsIso
      (ModuleCat.{u + 1} A) X).hom.app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)

/-- The geometric-point Hom comparison is the internal-Hom comparison of the actual
constant-sheaf equivalence. Thus it is the evaluation-defined comparison, with no
arbitrary choice of a point duality isomorphism.
Source: blueprint finite point evaluation, paragraph 2
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def finiteMappingEtalePointDual
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (S : Scheme.{u})
    [(constantSheaf S.smallEtaleTopology A).IsEquivalence]
    (C : DerivedCategory (Sheaf S.smallEtaleTopology A)) :=
  let e := Etale.rightDerivedGlobalSectionsIsoMapDerivedCategoryInv A S
  e.app ((Etale.DerivedCategory.coefficientDual A S).obj (op C)) ≪≫
    DerivedCategory.mapDerivedCategoryInvIhomUnitIso _ C ≪≫
      (MonoidalClosed.internalHom.mapIso (e.app C).op).app (𝟙_ _)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  (c : Compactification (X ↘ Spec (.of D.k)))

/-- Global derived Hom into the prescribed finite comparison-class dualizing object.
The internal Hom is the published sheaf derived Hom; ordinary RΓ retains its A action.
Source: blueprint finite mapping-complex display, paragraph 2
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def finiteMappingGlobalHom :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  (finiteTorConstructibleProEtaleModule l E (n + 1) (Nat.succ_pos n) X).ι.op ⋙
    (ProEtale.derivedHom
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      X).flip.obj
        (ProEtale.finiteDualityProEtaleObject (Padic.coefficientExtensionRing l E (n + 1)) c) ⋙
    ProEtale.rightDerivedGlobalSections
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X

/-- C_n is compact support for the one specified compactification, followed by point
sections. At the algebraically closed point ordinary derived sections are exact sections
on the finite constructible class, as in the recorded coefficient-point functor.
Source: blueprint definition of C_n(M), paragraph 2
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def finiteMappingCompactSections :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  (finiteTorConstructibleProEtaleModule l E (n + 1) (Nat.succ_pos n) X).ι ⋙
    ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) c ⋙
    ProEtale.rightDerivedGlobalSections
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      (Spec (.of D.k))

/-- The canonical site-Hom arrow and the dualizing-object arrow, separately bundled.
This retains their precise types without unfolding the derived closed structures.
Source: blueprint finite-duality comparison, paragraph 2
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def finiteMappingHomComparisonArrows
    (A : Type u) [CommRing A] [Finite A]
    {T S : Scheme.{u}} {a : T ⟶ S} (compactification : Compactification a)
    (J : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T) :
    List (Arrow (DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :=
  [Arrow.mk (finiteMappingGlobalComparison (ULift.{u + 1, u} A) T
      (((Etale.derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).obj (op J)).obj
        (ProEtale.finiteDualityEtaleObject A compactification))),
    finiteMappingArrowMap (ProEtale.rightDerivedGlobalSections
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T)
        (Arrow.mk (ProEtale.siteComparisonEvaluationHom
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T J
          (ProEtale.finiteDualityEtaleObject A compactification))),
    finiteMappingArrowMap (ProEtale.rightDerivedGlobalSections
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T)
        (Arrow.mk (((ProEtale.derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).obj
          (op ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            T).mapDerivedCategory.obj J))).map
              (ProEtale.finiteDualityObjectMap A compactification)))]

/-- The ordinary etale adjunction, global sections and the point evaluation comparison.
The compact-support independence map converts the chosen adjunction compactification to
exactly the compactification fixed in the statement, contravariantly in internal Hom.
Source: blueprint ordinary etale mapping adjunction, paragraph 2
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def finiteMappingEtaleGammaArrows
    (A : Type u) [CommRing A] [Finite A] (k : Type u) [Field k] [IsSepClosed k]
    {T : Scheme.{u}} {a : T ⟶ Spec (.of k)} [QuasiCompact a] (compactification : Compactification a)
    (J : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T) :
    List (Arrow (DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :=
  letI := compactification.hasCompactification
  [Arrow.mk ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) a).inv.app
        (((Etale.derivedHom _ T).obj (op J)).obj
          (ProEtale.finiteDualityEtaleObject A compactification))),
    finiteMappingArrowMap (Etale.rightDerivedGlobalSections
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (Spec (.of k)))
        (Arrow.mk (((Etale.derivedHomRightDerivedLowerShriekIsoOfFinite
          (ULift.{u + 1, u} A) a).hom.app (op J)).app (𝟙_ _))),
    finiteMappingArrowMap (Etale.rightDerivedGlobalSections
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (Spec (.of k)))
        (Arrow.mk (((Etale.derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (Spec (.of k))).map
            ((Etale.rightDerivedLowerShriekIso (ULift.{u + 1, u} A)
              compactification).hom.app J).op).app (𝟙_ _))),
    Arrow.mk ((finiteMappingEtalePointDual (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (Spec (.of k))
      ((Etale.rightDerivedLowerShriekOfCompactification _ compactification).obj J)).hom)]

/-- Coefficient dual of an arrow, retaining its precise source and target.
Source: blueprint finite adjunction, paragraph 2
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def finiteMappingDualArrow (A : Type (u + 1)) [CommRing A]
    (f : Arrow (DerivedCategory (ModuleCat.{u + 1} A))) :
    Arrow (DerivedCategory (ModuleCat.{u + 1} A)) :=
  Arrow.mk ((coefficientDerivedDual A).map f.hom.op)

/-- The coefficient-dual compact-support comparison followed by dual global comparison.
Both maps are the published canonical maps, including their derived-unit normalization.
Source: blueprint compact-support comparison, paragraph 2
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def finiteMappingDualTransportArrows
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} {a : T ⟶ S} (compactification : Compactification a)
    (J : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    List (Arrow (DerivedCategory (ModuleCat.{u + 1} A))) :=
  [finiteMappingDualArrow A (finiteMappingArrowMap
      (ProEtale.rightDerivedGlobalSections (ModuleCat.{u + 1} A) S)
      (Arrow.mk ((ProEtale.compactSupportSiteComparison A compactification).inv.app J))),
    finiteMappingDualArrow A (Arrow.mk (finiteMappingGlobalComparison A S
      ((Etale.rightDerivedLowerShriekOfCompactification _ compactification).obj J.obj)))]

/-- The canonical global tensor comparison on the etale site, expressed as its two
factors to retain the published derived tensor presentations.
Source: blueprint integral-dualizing proof, paragraph 2
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def finiteMappingEtaleSectionsTensor (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] (S : Scheme.{u})
    [(constantSheaf S.smallEtaleTopology A).Monoidal]
    [(constantSheaf S.smallEtaleTopology A).PreservesFlat]
    (K L : DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    List (Arrow (DerivedCategory A)) :=
  [Arrow.mk (Etale.constantDerivedProjectionMap A S K
      ((Etale.rightDerivedGlobalSections A S).obj L)),
    Arrow.mk ((Etale.rightDerivedGlobalSections A S).map
      (((Etale.derivedTensor A S).obj K).map
        ((Etale.derivedConstantGlobalSectionsAdjunction A S).counit.app L)))]
/-- The canonical lax tensor comparison of comparison direct image: its adjunction
unit, pullback tensor comparison, and the tensor product of its two counits.
Source: blueprint finite site comparison, paragraph 2
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def finiteMappingComparisonTensorArrows (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (S : Scheme.{u}) [(ProEtale.comparisonUpperStar A S).PreservesFlat]
    (K L : DerivedCategory (Sheaf (Scheme.ProEt.topology S) (A))) :
    List (Arrow (DerivedCategory (Sheaf S.smallEtaleTopology A))) :=
  let adj := ProEtale.derivedComparisonAdjunction (A) S
  let R := (ProEtale.comparisonLowerStar (A) S).rightDerivedFunctor
  [Arrow.mk (adj.unit.app (((Etale.derivedTensor A S).obj (R.obj K)).obj (R.obj L))),
    Arrow.mk (R.map ((ProEtale.siteComparisonTensorIso
      (A) S (R.obj K)).hom.app (R.obj L))),
    Arrow.mk (R.map (((ProEtale.derivedTensor A S).map (adj.counit.app K)).app
      ((ProEtale.comparisonUpperStar A S).mapDerivedCategory.obj (R.obj L)))),
    Arrow.mk (R.map (((ProEtale.derivedTensor A S).obj K).map (adj.counit.app L)))]

/-- The global tensor comparison on the pro-etale site, with the canonical Leray
identifications and the counit-defined lax comparison on the comparison direct image.
Source: blueprint integral-dualizing proof, paragraph 2
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def finiteMappingSectionsTensorArrows (A : Type (u + 1)) [CommRing A] [Finite A] (S : Scheme.{u})
    (K L : DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))) :
    List (Arrow (DerivedCategory (ModuleCat.{u + 1} A))) :=
  let e := ProEtale.comparisonLowerStarCompRightDerivedGlobalSectionsIso
    (ModuleCat.{u + 1} A) S
  let R := (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) S).rightDerivedFunctor
  [Arrow.mk (e.inv.app K ⊗ₘ e.inv.app L)] ++
    finiteMappingEtaleSectionsTensor (ModuleCat.{u + 1} A) S (R.obj K) (R.obj L) ++
    (finiteMappingComparisonTensorArrows (ModuleCat.{u + 1} A) S K L).map
      (finiteMappingArrowMap (Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} A) S)) ++
    [Arrow.mk (e.hom.app (K ⊗ L))]

/-- The scalar unit into point sections, including the degree-zero constant-unit
identification. Each factor is a prescribed localization or monoidal-unit map.
Source: blueprint integral-dualizing proof, paragraph 2
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def finiteMappingScalarUnitArrows (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    List (Arrow (DerivedCategory (ModuleCat.{u + 1} A))) :=
  let F := constantSheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)
  let G := ProEtale.rightDerivedGlobalSections (ModuleCat.{u + 1} A) S
  [Arrow.mk ((constantSheafΓAdj (Scheme.ProEt.topology S)
      (ModuleCat.{u + 1} A)).derivedAdjunction.unit.app (𝟙_ _)),
    Arrow.mk (G.map (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (𝟙_ _))),
    Arrow.mk (G.map (F.mapDerivedCategory.map
      (DerivedCategory.singleFunctorObjUnitIso _).inv)),
    Arrow.mk (G.map ((F.mapDerivedCategorySingleFunctor 0).hom.app (𝟙_ _))),
    Arrow.mk (G.map ((DerivedCategory.singleFunctor _ 0).map (Functor.Monoidal.εIso F).inv)),
    Arrow.mk (G.map (DerivedCategory.singleFunctorObjUnitIso _).hom)]

/-- The etale exceptional value whose comparison pullback is the prescribed omega.
The compactification is exactly the specified c.
Source: blueprint integral-dualizing proof, paragraph 2
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def finiteMappingCounitInput (A : Type u) [CommRing A] [Finite A]
    {T S : Scheme.{u}} {a : T ⟶ S} (compactification : Compactification a) :=
  letI := compactification.hasCompactification
  (Etale.rightDerivedUpperShriek (ULift.{u + 1, u} A) a).obj
    ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      S).rightDerivedFunctor.obj (𝟙_ _))

/-- The pro-etale exceptional counit for c: support comparison, compactification
independence, the etale exceptional counit, and the comparison adjunction counit.
Source: blueprint integral-dualizing proof, paragraph 2, proof step 5
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def finiteMappingCounit (A : Type u) [CommRing A] [Finite A]
    {T S : Scheme.{u}} {a : T ⟶ S} [QuasiCompact a] (compactification : Compactification a)
    (h : DerivedCategory.TStructure.t.plus (finiteMappingCounitInput A compactification)) :
    List (Arrow (DerivedCategory (Sheaf (Scheme.ProEt.topology S)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))) :=
  letI := compactification.hasCompactification
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let P := (ProEtale.comparisonUpperStar B S).mapDerivedCategory
  [Arrow.mk ((ProEtale.compactSupportSiteComparison (ULift.{u + 1, u} A)
      compactification).hom.app ⟨finiteMappingCounitInput A compactification, h⟩),
    Arrow.mk (P.map ((Etale.rightDerivedLowerShriekIso
      (ULift.{u + 1, u} A) compactification).hom.app
        (finiteMappingCounitInput A compactification))),
    Arrow.mk (P.map ((Etale.rightDerivedUpperShriekAdjunction (ULift.{u + 1, u} A) a).counit.app
      ((ProEtale.comparisonLowerStar B S).rightDerivedFunctor.obj (𝟙_ _)))),
    Arrow.mk ((ProEtale.derivedComparisonAdjunction B S).counit.app (𝟙_ _))]

/-- Tensor-Hom transpose in Hom-first order: the standard Koszul braiding followed
by the ordinary closed-category uncurry. Both arrows are specified, with no chosen map.
Source: blueprint integral-dualizing proof, paragraph 2
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def finiteMappingTransposeArrows (A : Type (u + 1)) [CommRing A]
    {H C : DerivedCategory (ModuleCat.{u + 1} A)}
    (f : H ⟶ (coefficientDerivedDual A).obj (op C)) :
    List (Arrow (DerivedCategory (ModuleCat.{u + 1} A))) :=
  [Arrow.mk ((DerivedMonoidal.braiding' (DerivedCategory.Qh (C := ModuleCat.{u + 1} A))
      (HomotopyCategory.quasiIso (ModuleCat.{u + 1} A) (ComplexShape.up ℤ)) H C).hom),
    Arrow.mk (MonoidalClosed.uncurry f)]

/-- The projection/evaluation/counit pairing, in Hom-first tensor order.
It uses inverse Leray, global tensor, the projection for c, pullback counit,
sheaf evaluation, the exceptional counit for c, and inverse point scalar unit.
Source: blueprint integral-dualizing proof, paragraph 2, proof step 5
(blueprint: def-sf-finite-mapping-adjunction-data). -/
def finiteMappingPairing (A : Type u) [CommRing A] [Finite A]
    {T S : Scheme.{u}} {a : T ⟶ S} [QuasiCompact a] (compactification : Compactification a)
    (h : DerivedCategory.TStructure.t.plus (finiteMappingCounitInput A compactification))
    (scalar : 𝟙_ (DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ≅
      (ProEtale.rightDerivedGlobalSections
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) S).obj (𝟙_ _))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    List (Arrow (DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :=
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let H := ((ProEtale.derivedHom B T).obj (op M)).obj
    (ProEtale.finiteDualityProEtaleObject A compactification)
  letI : ProEtale.UpperStarPreservesFlat B :=
    ProEtale.upperStarPreservesFlat_moduleCat (ULift.{u + 1, u} A)
  let F := ProEtale.rightDerivedLowerShriekOfCompactification B compactification
  let R := (ProEtale.lowerStar B a).rightDerivedFunctor
  let G := ProEtale.rightDerivedGlobalSections B S
  letI := (ProEtale.upperStarLowerStarAdjunction B a).preservesKInjectiveComplexes
  let leray := Functor.rightDerivedFunctorCompIso' (ProEtale.lowerStar B a)
    (Sheaf.Γ (Scheme.ProEt.topology S) B) (ProEtale.globalSectionsLowerStarIso B a)
  [Arrow.mk (T := DerivedCategory B) ((DerivedMonoidal.braiding' (DerivedCategory.Qh (C := B))
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
      ((ProEtale.rightDerivedGlobalSections B T).obj H) (G.obj (F.obj M))).hom),
    Arrow.mk (𝟙 (G.obj (F.obj M)) ⊗ₘ leray.inv.app H)] ++
    finiteMappingSectionsTensorArrows (ULift.{u + 1, u} A) S (F.obj M) (R.obj H) ++
    [finiteMappingArrowMap G (Arrow.mk
      (((ProEtale.projectionMapOfCompactification B compactification).app M).app (R.obj H))),
      finiteMappingArrowMap G (Arrow.mk (F.map (((ProEtale.derivedTensor B T).obj M).map
        ((ProEtale.derivedUpperStarLowerStarAdjunction B a).counit.app H)))),
      finiteMappingArrowMap G (Arrow.mk (F.map
        ((ProEtale.derivedTensorHomAdjunction B M).counit.app
          (ProEtale.finiteDualityProEtaleObject A compactification))))] ++
    (finiteMappingCounit A compactification h).map (finiteMappingArrowMap G) ++
    [Arrow.mk scalar.inv]

end WeilConjectures
