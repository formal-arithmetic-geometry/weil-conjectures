/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactSections
public import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
public import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.AdjunctionSquareExchange
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import WeilConjectures.Compactification.BaseChange
import WeilConjectures.AlgebraicGeometry.ProEtaleClopenUnboundedDerivedLocalization
import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.Compactification.Dense
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.ProperCoproduct
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.AlgebraicGeometry.CondensedModulePullbackExact
import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactCohomology
import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
import WeilConjectures.SixFunctors.DetSfCompBaseChangeDefs
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Finite clopen decomposition of condensed compact-support complexes

Source: latest blueprint, sec-deligne-laumon-general/sk-p-dl-general-relative-line/
lem-zl-affine-curve-hc2-purity.proof.md, second paragraph and empty-curve clause
(blueprint: lem-zl-condensed-clopen-compact-decomposition).

## Main definitions

`componentInclusion` and `boundedInclusion` give the canonical component maps.
`PointTransport` and `OpenTransport` specify the actual geometric exchange;
`compactTransport` and `action` compose the proper mate, open exchange and Weil map.

## Main statements

`condensed_clopen_compact_decomposition` states the natural biproduct decomposition,
its geometric Frobenius compatibility and its empty-index case.

The component maps are normalized by the open adjunction counit. The transport
records below specify the point-section comparison and the open adjunction mate;
they never supply an unconstrained endomorphism called Frobenius.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedClopenCompact

/-- Ordinary unbounded derived modules over the recorded pulled-back condensed Qbar ring.
Source: the node's coefficient convention
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev DMod (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ell) X))

/-- Exact pullback, with the canonical condensed scalar comparison.
Source: the node's restriction convention
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev pull (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (ProEtale.CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) f).mapDerivedCategory

/-- Total derived proper direct image, computed on K-injective resolutions.
Source: the compact-support construction in the node's proof, step 4
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev push (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (ProEtale.CondensedRing.lowerStar (Profinite.padicAlgClRingObj ell) f).rightDerivedFunctor

/-- Exact extension by zero on all integer-indexed complexes.
Source: the node's proof, step 3
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev extension (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] :=
  (ProEtale.CondensedRing.openImmersionLowerShriek
    (Profinite.padicAlgClRingObj ell) j).mapDerivedCategory

/-- Composition of exact derived pullbacks, retaining the published scalar normalization.
Source: the node's proof, steps 3 and 6
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def pullComp (ell : ℕ) [Fact ell.Prime] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull ell (f ≫ g) ≅ pull ell g ⋙ pull ell f :=
  Functor.mapDerivedCategoryNatIso
    (ProEtale.CondensedRing.upperStarComp (Profinite.padicAlgClRingObj ell) f g) ≪≫
  Functor.mapDerivedCategoryCompIso _ _

/-- The exact-derived open adjunction is the published levelwise adjunction.
Source: the node's proof, step 3
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev openAdj (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] : extension ell j ⊣ pull ell j :=
  ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj ell) j

/-- Open-extension composition is the unique adjunction conjugate of pullback composition.
Source: the node's proof, steps 3 and 5, retaining the open units
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def extensionComp (ell : ℕ) [Fact ell.Prime] {U X Z : Scheme.{u}}
    (j : U ⟶ X) (i : X ⟶ Z) [IsOpenImmersion j] [IsOpenImmersion i] :
    extension ell j ⋙ extension ell i ≅ extension ell (j ≫ i) :=
  (conjugateIsoEquiv (openAdj ell (j ≫ i)) ((openAdj ell j).comp (openAdj ell i))).symm
    (pullComp ell j i)

/-- The component inclusion is the normalized extension counit, followed by Rp_* and sections.
Source: the node's proof, step 5
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def componentInclusion (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k] {U X : Scheme.{u}}
    {a : X ⟶ Spec (.of k)} (c : Compactification a)
    (j : U ⟶ X) [IsOpenImmersion j] :
    pull ell j ⋙ condensedQbarCompactSections ell k (c.precomp j) ⟶
      condensedQbarCompactSections ell k c :=
  Functor.whiskerRight
    (Functor.whiskerLeft (pull ell j) (extensionComp ell j c.i).inv ≫
      Functor.whiskerRight (openAdj ell j).counit (extension ell c.i))
    (push ell c.g ⋙ condensedQbarDerivedPointSections ell k)

/-- The square comparison is induced by the two composition isomorphisms.
Source: the node's proof, step 6
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def pullSquare (ell : ℕ) [Fact ell.Prime] {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h : g' ≫ f = f' ≫ g) :
    pull ell g ⋙ pull ell f' ≅ pull ell f ⋙ pull ell g' :=
  (pullComp ell f' g).symm ≪≫
    eqToIso (congrArg (fun a ↦ pull ell a) h.symm) ≪≫ pullComp ell g' f

/-- The exact-derived pullback/total-derived pushforward adjunction.
Source: the node's proof, steps 4 and 6
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def pullPushAdj (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull ell f ⊣ push ell f :=
  (ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction
    (Profinite.padicAlgClRingObj ell) f).ofNatIsoLeft
      (ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.padicAlgClRingObj ell) f)

/-- The proper exchange is precisely the unit--square--counit mate.
Source: the node's proof, step 6
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def properExchange (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (gx : X ⟶ X) (gy : Y ⟶ Y) (h : gx ≫ f = f ≫ gy) :
    push ell f ⋙ pull ell gy ⟶ pull ell gx ⋙ push ell f :=
  Adjunction.squareExchange (pullPushAdj ell f) (pullPushAdj ell f)
    (pull ell gy) (pull ell gx) (pullSquare ell h)

/-- A point transport in the fixed Qbar coordinates is the actual section comparison.
The equality specifies its underlying additive map after the canonical scalar cancellation.
Source: the node's proof, step 7; geometric-field evaluation and its scalar-linearity theorem
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
structure PointTransport (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k] (sigma : k ≃+* k) where
  ordinary : ProEtale.CondensedQbarGeometricEvaluation.fieldFiber k ell ≅
    ProEtale.CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
      (Spec.map (CommRingCat.ofHom sigma.toRingHom)) ⋙
        ProEtale.CondensedQbarGeometricEvaluation.fieldFiber k ell
  normalization : ∀ M,
    ((ordinary.hom.app M ≫
      (ProEtale.CondensedQbarGeometricEvaluation.fieldFiber k ell).map
        ((Mod.extendScalarsIsoComapInv (ProEtale.condensedPullbackHom
          (Profinite.padicAlgClRingObj ell) (Spec.map (CommRingCat.ofHom sigma.toRingHom)))).hom.app
            (((ProEtale.upperStar Ab.{u + 1} (Spec.map (CommRingCat.ofHom sigma.toRingHom))).mapMod
              (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ell)
                (Spec (.of k)))).obj M)))).hom.toAddMonoidHom =
      ((ProEtale.geometricFieldEvaluationComparison
        (Spec.map (CommRingCat.ofHom sigma.toRingHom)) Ab.{u + 1}).app M.X).hom

/-- Point transport is induced term by term on ordinary unbounded derived categories.
Source: the node's proof, step 7
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def PointTransport.derived {ell : ℕ} [Fact ell.Prime]
    {k : Type u} [Field k] [IsAlgClosed k] {sigma : k ≃+* k}
    (t : PointTransport ell k sigma) :
    condensedQbarDerivedPointSections ell k ≅
      pull ell (Spec.map (CommRingCat.ofHom sigma.toRingHom)) ⋙
        condensedQbarDerivedPointSections ell k := by
  letI := comp_preservesFiniteLimits
    (ProEtale.CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
      (Spec.map (CommRingCat.ofHom sigma.toRingHom)))
    (ProEtale.CondensedQbarGeometricEvaluation.fieldFiber k ell)
  letI := comp_preservesFiniteColimits
    (ProEtale.CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
      (Spec.map (CommRingCat.ofHom sigma.toRingHom)))
    (ProEtale.CondensedQbarGeometricEvaluation.fieldFiber k ell)
  exact Functor.mapDerivedCategoryNatIso t.ordinary ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The open exchange is fixed by its mate under the actual open adjunction.
Source: the node's proof, step 6; the mate equality includes its unit/counit normalization
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
structure OpenTransport (ell : ℕ) [Fact ell.Prime]
    {X Z : Scheme.{u}} (i : X ⟶ Z) [IsOpenImmersion i]
    (gx : X ⟶ X) (gz : Z ⟶ Z) (h : gx ≫ i = i ≫ gz) where
  exchange : extension ell i ⋙ pull ell gz ≅ pull ell gx ⋙ extension ell i
  normalization : Adjunction.squareExchange (openAdj ell i) (openAdj ell i)
    (pull ell gx) (pull ell gz) exchange.symm = (pullSquare ell h).inv

/-- The compact-support transport is point transport, the proper mate, then open exchange.
Source: the node's proof, steps 6--7
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def compactTransport {ell : ℕ} [Fact ell.Prime]
    {k : Type u} [Field k] [IsAlgClosed k] {sigma : k ≃+* k}
    (t : PointTransport ell k sigma) {X : Scheme.{u}}
    {a : X ⟶ Spec (.of k)} (c : Compactification a)
    (gx : X ⟶ X) (gz : c.Z ⟶ c.Z)
    (hg : gz ≫ c.g = c.g ≫ Spec.map (CommRingCat.ofHom sigma.toRingHom))
    {hi : gx ≫ c.i = c.i ≫ gz} (e : OpenTransport ell c.i gx gz hi) :
    condensedQbarCompactSections ell k c ⟶ pull ell gx ⋙ condensedQbarCompactSections ell k c :=
  Functor.whiskerLeft (extension ell c.i ⋙ push ell c.g) t.derived.hom ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (extension ell c.i)
        (properExchange ell c.g gz (Spec.map (CommRingCat.ofHom sigma.toRingHom)) hg))
          (condensedQbarDerivedPointSections ell k) ≫
    Functor.whiskerRight (Functor.whiskerRight e.exchange.hom (push ell c.g))
      (condensedQbarDerivedPointSections ell k)

/-- Geometric Frobenius on compact cohomology is induced by the specified Weil isomorphism.
Source: the node's displayed definition of F_X and its proof, step 7
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def action {ell : ℕ} [Fact ell.Prime] {k : Type u} [Field k] [IsAlgClosed k]
    {sigma : k ≃+* k} (t : PointTransport ell k sigma) {X : Scheme.{u}}
    {a : X ⟶ Spec (.of k)} (c : Compactification a)
    (gx : X ⟶ X) (gz : c.Z ⟶ c.Z)
    (hg : gz ≫ c.g = c.g ≫ Spec.map (CommRingCat.ofHom sigma.toRingHom))
    {hi : gx ≫ c.i = c.i ≫ gz} (e : OpenTransport ell c.i gx gz hi)
    (K : DMod ell X) (theta : (pull ell gx).obj K ≅ K) :
    End ((condensedQbarCompactSections ell k c).obj K) :=
  (compactTransport t c gx gz hg e).app K ≫ (condensedQbarCompactSections ell k c).map theta.hom

/-- Restriction of compact sections to the recorded bounded-constructible full category.
Source: the node's bounded-constructible hypothesis
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev boundedSections (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    {a : X ⟶ Spec (.of k)} (c : Compactification a) :=
  (ProEtale.boundedConstructible
    (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ell) X)).ι ⋙
      condensedQbarCompactSections ell k c

/-- Component compact sections use actual pullback and the restricted compactification.
Source: the node's definition K_i = j_i^* K and proof, step 5
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev componentSections (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k] {U X : Scheme.{u}}
    {a : X ⟶ Spec (.of k)} (c : Compactification a) (j : U ⟶ X)
    [IsOpenImmersion j] :=
  (ProEtale.boundedConstructible
    (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ell) X)).ι ⋙
      pull ell j ⋙ condensedQbarCompactSections ell k (c.precomp j)

/-- The canonical inclusion on the full bounded-constructible category.
Source: the node's component-inclusion normalization
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def boundedInclusion (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k] {U X : Scheme.{u}}
    {a : X ⟶ Spec (.of k)} (c : Compactification a) (j : U ⟶ X)
    [IsOpenImmersion j] : componentSections ell k c j ⟶ boundedSections ell k c :=
  Functor.whiskerLeft _ (componentInclusion ell k c j)

/-- The fixed geometric field automorphism used by the recorded scheme Frobenius.
Source: def-weil-frobenius-detailed, geometric Frobenius convention
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def fieldFrobenius (D : FiniteFieldDatum.{u}) : D.k ≃+* D.k := by
  letI := Fintype.ofFinite D.k₀
  exact (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingEquiv

/-- The same geometric Frobenius map, using the recorded Galois construction directly.
This presentation also applies before installing the inherited finite-type instances.
Source: def-weil-frobenius-detailed, formula for geometricFrobenius.hom
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev schemeFrobenius (D : FiniteFieldDatum.{u}) (X : Over (Spec (.of D.k₀))) :=
  D.galoisMap X.hom (by
    letI := Fintype.ofFinite D.k₀
    exact FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)

/-- The canonical inclusion of the geometric base change of an arithmetic component.
Source: the node's X_i and j_i conventions
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def geometricInclusion (D : FiniteFieldDatum.{u})
    {U X : Over (Spec (.of D.k₀))} (j : U ⟶ X) :
    pullback U.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ⟶
      pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j).left

/-- Open immersions remain open under the indicated geometric base change.
Source: the node's component geometry, proof step 1
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
instance geometricInclusionOpen (D : FiniteFieldDatum.{u})
    {U X : Over (Spec (.of D.k₀))} (j : U ⟶ X) [IsOpenImmersion j.left] :
    IsOpenImmersion (geometricInclusion D j) := by
  exact MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j inferInstance

/-- The common compactification obtained by base changing the arithmetic one.
Source: the node's proof, steps 1--2
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev geometricCompactification (D : FiniteFieldDatum.{u})
    {X : Over (Spec (.of D.k₀))} (c : Compactification X.hom) :=
  c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- Frobenius on the compactification is the actual base-change Galois map.
Source: the node's proof, step 6
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev compactificationFrobenius (D : FiniteFieldDatum.{u})
    {X : Over (Spec (.of D.k₀))} (c : Compactification X.hom) :=
  D.galoisMap c.g (by
    letI := Fintype.ofFinite D.k₀
    exact FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)

/-- The finite clopen decomposition of ordinary condensed compact-support complexes,
natural in K and compatible with the geometric Frobenius and all biproduct maps.

Source: latest blueprint, sec-deligne-laumon-general/sk-p-dl-general-relative-line/
lem-zl-affine-curve-hc2-purity.proof.md, paragraph two and empty-curve clause
(blueprint: lem-zl-condensed-clopen-compact-decomposition).

Proof plan (the eight steps of the node):

1. Open and closed base change preserve the clopen partition
(lem-weil-pbc-open-immersion-base-change, lem-weil-pbc-closed-immersion-base-change).
Nagata compactification (sk-thm-nagata-compactification) on
its finitely many components gives compactifications, including empty pieces.
2. The finite disjoint union (lem-weil-pbc-scheme-coproduct-family and
lem-weil-pbc-proper-coproduct), with proper base change
(lem-weil-pbc-proper-base-change), gives a common
compactification over k₀.
3. Finite-clopen unbounded localization (lem-pur-clopen-unbounded-derived-localization)
identifies module derived categories with products, with actual restriction and
zero insertion. The open adjunction makes extension by zero componentwise, with
its original units (sk-def-sfb-module-lower-shriek, det-def-sfb-derived-categories).
4. Pullback is exact (det-prop-sfb-module-pullback-exact-main). The proper derived
adjunction (sk-def-sfb-module-derived-pushpull) identifies direct image with the
finite product of the component images; its projections are transposes of the
component counits, and computes compact support (sk-def-sfb-module-derived-lower-shriek).
5. Finite products in the additive derived category are biproducts.
Exact point sections preserve their identities. The open-compactification comparisons
(lem-zl-condensed-compactification-open-comparison)
identify these maps with those for any common compactification, preserving units
and counits. Restriction preserves bounded constructibility by intersecting the
finite stratifications and retaining the same finite cohomology interval.
6. The arithmetic compactification's geometric Galois map preserves its components
(def-weil-frobenius-detailed).
The unit--square--counit formula for proper exchange restricts to each component;
the open mate does too (def-sfb-compact-support-base-change-maps,
def-weil-pbc-adjunction-mate).
7. Point transport is natural on sections and hence after
termwise localization. Combining these two naturalities and that of theta gives
the displayed Frobenius equation.
8. On the empty scheme the source derived category
is zero; exact extension, proper right adjoint and exact point sections send zero
to zero. The empty sum and every empty component therefore satisfy the same identities.
-/
theorem condensed_clopen_compact_decomposition
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (X : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (I : Type w) [Fintype I] [DecidableEq I]
    (U : I → Over (Spec (.of D.k₀))) (j : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (j i).left] [∀ i, IsClosedImmersion (j i).left]
    (hdisjoint : Pairwise fun i k ↦ Disjoint (Set.range (j i).left) (Set.range (j k).left))
    (hcover : (⋃ i, Set.range (j i).left) = Set.univ)
    (c : Compactification X.hom) :
    ∃ (t : PointTransport ell D.k (fieldFrobenius D))
      (hg : compactificationFrobenius D c ≫ (geometricCompactification D c).g =
        (geometricCompactification D c).g ≫
          Spec.map (CommRingCat.ofHom (fieldFrobenius D).toRingHom))
      (hi : (D.geometricFrobenius X).hom ≫ (geometricCompactification D c).i =
        (geometricCompactification D c).i ≫ compactificationFrobenius D c)
      (e : OpenTransport ell (geometricCompactification D c).i
        (D.geometricFrobenius X).hom (compactificationFrobenius D c) hi)
      (hj : ∀ i, (schemeFrobenius D (U i)) ≫ geometricInclusion D (j i) =
        geometricInclusion D (j i) ≫ (D.geometricFrobenius X).hom)
      (hci : ∀ i, (schemeFrobenius D (U i)) ≫
          ((geometricCompactification D c).precomp (geometricInclusion D (j i))).i =
        ((geometricCompactification D c).precomp (geometricInclusion D (j i))).i ≫
          compactificationFrobenius D c)
      (ei : ∀ i, OpenTransport ell
        ((geometricCompactification D c).precomp (geometricInclusion D (j i))).i
        (schemeFrobenius D (U i)) (compactificationFrobenius D c) (hci i))
      (pi : ∀ i, boundedSections ell D.k (geometricCompactification D c) ⟶
        componentSections ell D.k (geometricCompactification D c) (geometricInclusion D (j i))),
      (∀ i k, boundedInclusion ell D.k (geometricCompactification D c)
          (geometricInclusion D (j i)) ≫ pi k =
        if h : i = k then eqToHom (congrArg
          (fun i ↦ componentSections ell D.k (geometricCompactification D c)
            (geometricInclusion D (j i))) h) else 0) ∧
      (∑ i, pi i ≫ boundedInclusion ell D.k (geometricCompactification D c)
        (geometricInclusion D (j i))) = 𝟙 _ ∧
      (∀ K : ProEtale.BoundedConstructible
          (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ell)
            (D.geometricFiber X).left),
        (∀ i, ProEtale.boundedConstructible
          (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ell)
            (pullback (U i).hom
              (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
          ((pull ell (geometricInclusion D (j i))).obj K.obj)) ∧
        IsIso (biproduct.desc (fun i ↦
          (boundedInclusion ell D.k (geometricCompactification D c)
            (geometricInclusion D (j i))).app K)) ∧
        (∀ theta : (pull ell (D.geometricFrobenius X).hom).obj K.obj ≅ K.obj,
          ∃ theta_i : ∀ i,
            (pull ell (schemeFrobenius D (U i))).obj
                ((pull ell (geometricInclusion D (j i))).obj K.obj) ≅
              (pull ell (geometricInclusion D (j i))).obj K.obj,
            (∀ i, theta_i i = ((pullSquare ell (hj i)).app K.obj).symm ≪≫
              (pull ell (geometricInclusion D (j i))).mapIso theta) ∧
            biproduct.desc (fun i ↦
                (boundedInclusion ell D.k (geometricCompactification D c)
                  (geometricInclusion D (j i))).app K) ≫
              action t (geometricCompactification D c) (D.geometricFrobenius X).hom
                (compactificationFrobenius D c) hg e K.obj theta =
            biproduct.map (fun i ↦
              action t ((geometricCompactification D c).precomp (geometricInclusion D (j i)))
                (schemeFrobenius D (U i)) (compactificationFrobenius D c) hg
                  (ei i) ((pull ell (geometricInclusion D (j i))).obj K.obj) (theta_i i)) ≫
              biproduct.desc (fun i ↦
                (boundedInclusion ell D.k (geometricCompactification D c)
                  (geometricInclusion D (j i))).app K))) ∧
      (IsEmpty I → IsEmpty (D.geometricFiber X).left ∧
        ∀ K : ProEtale.BoundedConstructible
          (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ell)
            (D.geometricFiber X).left),
          IsZero ((boundedSections ell D.k (geometricCompactification D c)).obj K)) := by
  sorry

end WeilConjectures.CondensedClopenCompact
