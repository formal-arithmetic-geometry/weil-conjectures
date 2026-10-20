/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.SixFunctors.FiniteDualitySiteComparison
public import Sheaf.Paper.FinitePointInternalHomEvaluation
public import Sheaf.Paper.CoefficientDuality
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Mathlib.CategoryTheory.Comma.Arrow
public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
import Sheaf.SmoothPurity.InternalAdjunctionEvaluation
import Sheaf.Paper.BoundedSiteAdjunctionTranspose
import Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin
import Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalTransport

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.SixFunctors.CtfStabilityDirectImages
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
import Sheaf.Paper.FiniteStageVerdierBiduality
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit

/-!
# Finite-level mapping-complex adjunction

Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-tower,
prop-coef-integral-dualizing.proof.md, paragraph 2
(blueprint: lem-coef-finite-mapping-adjunction).

We use the published fixed-scalar presentation of ordinary constant-ring module sheaves.
Two equations fix the map: agreement with ordinary etale internal exceptional adjunction,
and equality of its tensor-Hom transpose with projection, evaluation and the exceptional
counit for the fixed compactification. The point scalar isomorphism is uniquely normalized
by the derived constant-sheaf adjunction unit. All global comparison arrows are derived
comparison units followed by the canonical Leray comparison.
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
(blueprint: lem-coef-finite-mapping-adjunction). -/
def FiniteMappingComposite {C : Type v} [Category.{u} C] :
    List (Arrow C) → Arrow C → Prop
  | [], result => ∃ V : C, result = Arrow.mk (𝟙 V)
  | first :: rest, result =>
    ∃ (V W Z : C) (f : V ⟶ W) (g : W ⟶ Z),
      first = Arrow.mk f ∧ FiniteMappingComposite rest (Arrow.mk g) ∧
        result = Arrow.mk (f ≫ g)

/-- Two specified arrow lists have the same composite, including their endpoints.
Source: blueprint integral-dualizing proof, paragraph 2
(blueprint: lem-coef-finite-mapping-adjunction). -/
def FiniteMappingSameComposite {C : Type v} [Category.{u} C]
    (left right : List (Arrow C)) : Prop :=
  ∃ result : Arrow C, FiniteMappingComposite left result ∧
    FiniteMappingComposite right result

/-- Map an arrow by a specified functor, retaining its endpoints.
Source: blueprint integral-dualizing proof, paragraph 2
(blueprint: lem-coef-finite-mapping-adjunction). -/
def finiteMappingArrowMap {C : Type v} [Category.{u} C]
    {B : Type w} [Category.{t} B] (F : C ⥤ B) (f : Arrow C) : Arrow B :=
  Arrow.mk (F.map f.hom)

/-- The ordinary global comparison, with its derived-unit normalization. It is defined
before asserting invertibility, so no boundedness assumption enters the construction.
Source: blueprint finite site/global comparison, paragraph 2
(blueprint: lem-coef-finite-mapping-adjunction). -/
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
(blueprint: lem-coef-finite-mapping-adjunction). -/
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
(blueprint: lem-coef-finite-mapping-adjunction). -/
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
(blueprint: lem-coef-finite-mapping-adjunction). -/
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
(blueprint: lem-coef-finite-mapping-adjunction). -/
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
(blueprint: lem-coef-finite-mapping-adjunction). -/
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
(blueprint: lem-coef-finite-mapping-adjunction). -/
def finiteMappingDualArrow (A : Type (u + 1)) [CommRing A]
    (f : Arrow (DerivedCategory (ModuleCat.{u + 1} A))) :
    Arrow (DerivedCategory (ModuleCat.{u + 1} A)) :=
  Arrow.mk ((coefficientDerivedDual A).map f.hom.op)

/-- The coefficient-dual compact-support comparison followed by dual global comparison.
Both maps are the published canonical maps, including their derived-unit normalization.
Source: blueprint compact-support comparison, paragraph 2
(blueprint: lem-coef-finite-mapping-adjunction). -/
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
(blueprint: lem-coef-finite-mapping-adjunction). -/
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
(blueprint: lem-coef-finite-mapping-adjunction). -/
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
(blueprint: lem-coef-finite-mapping-adjunction). -/
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
(blueprint: lem-coef-finite-mapping-adjunction). -/
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
(blueprint: lem-coef-finite-mapping-adjunction). -/
def finiteMappingCounitInput (A : Type u) [CommRing A] [Finite A]
    {T S : Scheme.{u}} {a : T ⟶ S} (compactification : Compactification a) :=
  letI := compactification.hasCompactification
  (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) a).obj
    ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      S).rightDerivedFunctor.obj (𝟙_ _))

/-- The pro-etale exceptional counit for c: support comparison, compactification
independence, the etale exceptional counit, and the comparison adjunction counit.
Source: blueprint integral-dualizing proof, paragraph 2, proof step 5
(blueprint: lem-coef-finite-mapping-adjunction). -/
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
    Arrow.mk (P.map ((Etale.rightDerivedUpperShriekAdjunction B a).counit.app
      ((ProEtale.comparisonLowerStar B S).rightDerivedFunctor.obj (𝟙_ _)))),
    Arrow.mk ((ProEtale.derivedComparisonAdjunction B S).counit.app (𝟙_ _))]

/-- Tensor-Hom transpose in Hom-first order: the standard Koszul braiding followed
by the ordinary closed-category uncurry. Both arrows are specified, with no chosen map.
Source: blueprint integral-dualizing proof, paragraph 2
(blueprint: lem-coef-finite-mapping-adjunction). -/
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
(blueprint: lem-coef-finite-mapping-adjunction). -/
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

/-- The finite mapping-complex adjunction is a natural isomorphism, characterized on
EVERY etale representative by the canonical comparison square. Its tensor-Hom transpose
is explicitly required, for EVERY M in the full intrinsic domain, to equal the compact-support
projection/evaluation/exceptional-counit pairing. The point scalar isomorphism has the
specified derived constant-unit normalization. Both arrow-list equations are ordinary
equality of composites, with endpoints included.
No ambient unbounded pro-etale exceptional adjunction is assumed.
Source: main-20261015, prop-coef-integral-dualizing.proof.md, paragraph 2
(blueprint: lem-coef-finite-mapping-adjunction).

Proof plan:
1. Finite type over the geometric field makes a compactifiable Noetherian morphism.
General biduality puts both dualizing objects in D^b_ctf by dualizing the constant unit.
2. Choose a bounded constructible etale origin of M. Tor-amplitude comparison reflects
its finite Tor interval. Finite duality site comparison identifies its internal Hom and
its dualizing object, and preserves evaluation.
3. Direct-image finite-Tor stability makes F_n M bounded constructible of finite Tor
amplitude. Compact-support comparison gives its etale origin. Full faithfulness and
Tor-amplitude reflection show that the etale compact-support object is also D^b_ctf.
The evaluation-defined finite point internal-Hom theorem consequently applies.
4. Apply prop-asd-internal-adjunction to the etale origin and the base coefficient unit.
Take ordinary global sections using Leray. Transport by the derived-unit global
comparison, finite duality comparison, and compact-support comparison. The point
comparison is evaluation-defined, giving exactly finiteMappingEtaleGammaArrows.
5. InternalAdjunctionEvaluation identifies the transpose with projection, evaluation and
the etale exceptional counit. Projection comparison on etale origins and bounded-site
adjunction-transpose compatibility transport this counit to the comparison-class
exceptional counit. Point evaluation compatibility therefore gives the stated canonical
transpose, with no scalar ambiguity. The etale exceptional value on the comparison direct
image of the constant unit is bounded below, supplying homega. At the algebraically closed
point, finite comparison and exact point sections identify the derived constant adjunction
unit with an isomorphism; its normalized composite is scalar. Consequently the transpose
is exactly finiteMappingPairing, with its final scalar inverse.
6. Every constituent comparison is natural and the origin functor is fully faithful.
Thus the square descends independently of the chosen origin to the displayed natural
isomorphism. Its equation holds for every etale representative and every morphism.
-/
theorem finiteMappingAdjunction (hl : l ≠ D.p)
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    ∃ γ : finiteMappingGlobalHom D l E n X c ≅
        (finiteMappingCompactSections D l E n X c).op ⋙
          coefficientDerivedDual
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))),
      (∀ (J : Etale.DerivedCategoryModule
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) X)
        (hJ : finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X J),
        ∃ (hplus : DerivedCategory.TStructure.t.plus J)
          (hpro : finiteTorConstructibleProEtaleModule l E (n + 1) (Nat.succ_pos n) X
            ((ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u}
                (Padic.coefficientExtensionRing l E (n + 1)))) X).mapDerivedCategory.obj J)),
          FiniteMappingSameComposite
            (finiteMappingHomComparisonArrows
                (Padic.coefficientExtensionRing l E (n + 1)) c J ++
              [Arrow.mk (γ.hom.app (op ⟨_, hpro⟩))] ++
                finiteMappingDualTransportArrows
                  (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
                  c ⟨J, hplus⟩)
            (finiteMappingEtaleGammaArrows
              (Padic.coefficientExtensionRing l E (n + 1)) D.k c J)) ∧
      ∃ (homega : DerivedCategory.TStructure.t.plus
          (finiteMappingCounitInput (Padic.coefficientExtensionRing l E (n + 1)) c))
        (scalar :
          𝟙_ (DerivedCategory (ModuleCat.{u + 1}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ≅
          (ProEtale.rightDerivedGlobalSections
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
            (Spec (.of D.k))).obj (𝟙_ _)),
        FiniteMappingComposite
          (finiteMappingScalarUnitArrows
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
            (Spec (.of D.k))) (Arrow.mk scalar.hom) ∧
        ∀ M : (finiteTorConstructibleProEtaleModule
            l E (n + 1) (Nat.succ_pos n) X).FullSubcategory,
          FiniteMappingSameComposite
            (finiteMappingTransposeArrows
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
              (γ.hom.app (op M)))
            (finiteMappingPairing (Padic.coefficientExtensionRing l E (n + 1))
              c homega scalar M.obj) := by
  sorry

end WeilConjectures
