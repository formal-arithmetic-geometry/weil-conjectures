/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedHomData
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.WeilSheaf.StrictWeilComplexNotFaithful
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobenius
public import WeilConjectures.AlgebraicGeometry.SixFunctors.AbsoluteFrobeniusSite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Monoidal.Braided.Transport
public import WeilConjectures.WeilObject.Sheaf.StalkFrobenius
public import WeilConjectures.SixFunctors.ProEtale.AbsoluteFrobenius
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobeniusNaturality
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.TraceFormula.CompactCohomology
public import WeilConjectures.TraceFormula.Statement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence

/-! # Model and semilinear Frobenius operators

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/
sk-p-dl-a1-some-weight/lem-fd-realness-pushforward.proof.md, Step 1
(blueprint: lem-fd-condensed-model-frobenius-operators).

The helpers write the canonical maps on the ordinary derived module categories.
Compact-support operators are compared through the published compactification independence
isomorphism, before taking cohomology or traces.

## Main definitions and statement

* `kappa`, `modelStructure`: the canonical linearized model structures.
* `compactReturn`, `stalkReturn`: the semilinear global and local returns.
* `condensed_model_frobenius_operators`: equality with the published model operators.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison

open CondensedOpenProper

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Iteration with the actual pullback compositors, including the identity unitor.
Source: source Step 1, iteration of theta
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def iterateStructure {T : Scheme.{u}} (f : End T) {K : D Λ T}
    (θ : (P Λ f).obj K ≅ K) : (m : ℕ) → (P Λ (f ^ m)).obj K ≅ K
  | 0 => (pId Λ T).app K
  | m + 1 =>
    (eqToIso (congrArg (fun h : End T ↦ (P Λ h).obj K) (pow_succ f m))) ≪≫
      (pComp Λ f (f ^ m)).app K ≪≫ (P Λ f).mapIso (iterateStructure f θ m) ≪≫ θ

/-- The specified module-linear kappa, using the equality of scheme maps and the
termwise absolute-Frobenius trivialization; its data involve no choice of an isomorphism.
Source: source Step 1, displayed kappa
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def kappa {T : Scheme.{u}} (p : ℕ) (hp : p.Prime) (hT : (p : Γ(T, ⊤)) = 0)
    (b : ℕ) (g φ : T ⟶ T) (w : φ = T.iterateFrobenius hp hT b ≫ g) :
    P Λ φ ≅ P Λ g :=
  eqToIso (congrArg (P Λ) w) ≪≫
    pComp Λ (T.iterateFrobenius hp hT b) g ≪≫
    Functor.isoWhiskerLeft (P Λ g)
      (Functor.mapDerivedCategoryNatIso (upperStarIterateFrobeniusIso Λ hp hT b) ≪≫
        Functor.mapDerivedCategoryIdIso _) ≪≫ Functor.rightUnitor _

/-- Canonical point reparametrization on modules, localized termwise.
Source: source Step 1, point normalization
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def pointReparametrization {k : Type u} [Field k] [IsSepClosed k]
    (g : Spec (.of k) ⟶ Spec (.of k)) : P Λ g ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (upperStarIsoIdOfIsSepClosed Λ g) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The proper exchange is the mate of the specified pullback square comparison.
Source: source Step 1, proper-mate calculation
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def properExchange {Z S : Scheme.{u}} (p : Z ⟶ S) (gZ : Z ⟶ Z) (gS : S ⟶ S)
    (w : gZ ≫ p = p ≫ gS) : R Λ p ⋙ P Λ gS ⟶ P Λ gZ ⋙ R Λ p :=
  Adjunction.exchangeRight
    (upperStarLowerStarAdjunction Λ p).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ p).mapDerivedCategoryRightDerivedAdjunction
    ((pComp Λ p gS).symm ≪≫ eqToIso (congrArg (P Λ) w.symm) ≪≫ pComp Λ gZ p)

/-- The canonical compact exchange in a Frobenius-stable compactification is proper
exchange followed by inverse open mate. The total inverse is the existing operation;
the open mate is invertible on the present Cartesian automorphism squares.
Source: source Step 1, compactification recipe e_m
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def compactExchange {X Z S : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (p : Z ⟶ S) (gX : X ⟶ X) (gZ : Z ⟶ Z) (gS : S ⟶ S)
    (wj : gX ≫ j = j ≫ gZ) (wp : gZ ≫ p = p ≫ gS) :
    (J Λ j ⋙ R Λ p) ⋙ P Λ gS ⟶ P Λ gX ⋙ (J Λ j ⋙ R Λ p) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (J Λ j) (properExchange Λ p gZ gS wp) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (comparisonInverse (openMap Λ (CommSq.mk wj))) (R Λ p) ≫
    (Functor.associator _ _ _).hom

/-- Semilinear compact-support return, with point reparametrization first.
Source: source Step 1, definition of F_g,c
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def compactReturn {X Z : Scheme.{u}} {k : Type u} [Field k] [IsSepClosed k]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Spec (.of k))
    (gX : X ⟶ X) (gZ : Z ⟶ Z) (gS : Spec (.of k) ⟶ Spec (.of k))
    (wj : gX ≫ j = j ≫ gZ) (wp : gZ ≫ p = p ≫ gS)
    {K : D Λ X} (θ : (P Λ gX).obj K ⟶ K) :
    End ((J Λ j ⋙ R Λ p).obj K) :=
  (pointReparametrization Λ gS).inv.app ((J Λ j ⋙ R Λ p).obj K) ≫
    (compactExchange Λ j p gX gZ gS wj wp).app K ≫ (J Λ j ⋙ R Λ p).map θ

end AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison

namespace AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison

open CondensedOpenProper

/-- The recorded model Frobenius, bundled as an endomorphism over the geometric point.
Source: source Step 1, Phi_X (blueprint: lem-fd-condensed-model-frobenius-operators). -/
@[irreducible] def modelEnd (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    End (D.geometricFiber X₀) :=
  Over.homMk (D.schemeFrobenius X₀) (D.relativeFrobenius_projections X₀).2

/-- A model compactification, base changed to the geometric point.
Source: source Step 1, compactification paragraph
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def geometricCompactification (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (c₀ : Compactification X₀.hom) : Compactification (D.geometricFiber X₀).hom :=
  c₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

section ModelOperators

variable (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- Restriction of the specified ambient model structure through the full inclusion.
The exact-to-total-derived comparison is inserted before u.
Source: source Step 1, model Weil object
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def modelObject (φ : X ⟶ X)
    (B : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
    (uφ : (P (Profinite.padicAlgClRingObj ell) φ.left).obj B.obj ≅ B.obj) :
    WeilBoundedConstructible ell φ :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk B
    (ObjectProperty.isoMk _
      ((boundedConstructibleUpperStarCompatibility
        (Profinite.padicAlgClRingObj ell) ell φ).app B ≪≫
        (leftDerivedUpperStarIsoMapDerivedCategory
          (Profinite.padicAlgClRingObj ell) φ.left).app B.obj ≪≫ uφ))

/-- The model globalOperator of degree one for the pair with structure u_m, in the
ambient category. Its existing definition uses the relative unit and shriek composition.
Source: source Step 1, model globalOperator
(blueprint: lem-fd-condensed-model-frobenius-operators). -/
def modelGlobal (φ : X ⟶ X) (hfin : IsFinite φ.left)
    (huh : IsUniversalHomeomorphism φ.left) (B : WeilBoundedConstructible ell φ) :=
  letI := hfin
  letI := huh
  letI : IsFinite (frobeniusIterate φ 1).left :=
    (congrArg (fun f : X ⟶ X ↦ IsFinite f.left) (frobeniusIterate_one φ)).symm ▸ hfin
  letI : IsUniversalHomeomorphism (frobeniusIterate φ 1).left :=
    (congrArg (fun f : X ⟶ X ↦ IsUniversalHomeomorphism f.left)
      (frobeniusIterate_one φ)).symm ▸ huh
  (B.globalOperator 1).hom

end ModelOperators

end AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison

namespace AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison

open CondensedOpenProper

variable (D₀ : WeilConjectures.FiniteFieldDatum.{u})
  (X₀ : Over (Spec (.of D₀.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

end AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison
