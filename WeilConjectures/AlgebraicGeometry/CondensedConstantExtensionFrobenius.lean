/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantExtensionWeilHeartData
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.ConstantExtensionPunctualWeights
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions

public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactSections
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.AlgebraicGeometry.FrobeniusDetailed
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
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.TraceFormula.FrobeniusIterate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree

import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.SixFunctors.FrobeniusSquareCartesian
import WeilConjectures.AlgebraicGeometry.ClosedPointField

/-! # Finite constant extension of ordinary condensed Weil sheaves

Source: latest blueprint, sec-deligne-laumon-general/sk-p-dl-general-relative-line/
lem-zl-affine-curve-hc2-purity.proof.md, second paragraph
(blueprint: lem-zl-condensed-constant-extension-frobenius).

The geometric fibre is identified by constantExtensionFiberIso; its Frobenius identity
is constantExtensionFiber_return. The extended Weil structure is the ordered pullback
iterate in extend. The compact-support operators below are constructed directly from
the powered scheme automorphisms. They act directly on the recorded compact-support
coefficient complex condensedQbarCompactSections of def-weil-ordinary-compact-cohomology,
with values in the ordinary derived category of Qbar_ell-modules.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The pullback equivalence with its specified inverse pullback. Its coherence maps
are precisely the identity and composition comparisons of module inverse image.
Source: latest blueprint, canonical pullback compositors
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
def constantExtensionPullEquivalence {X Y : Scheme.{u}} (a : X ≅ Y) :=
  CategoryTheory.Equivalence.mk (upperStar Λ a.hom) (upperStar Λ a.inv)
    ((upperStarId Λ Y).symm ≪≫ upperStarCongr Λ a.inv_hom_id.symm ≪≫
      upperStarComp Λ a.inv a.hom)
    ((upperStarComp Λ a.hom a.inv).symm ≪≫ upperStarCongr Λ a.hom_inv_id ≪≫
      upperStarId Λ X)

/-- The open exchange, computed as conjugation of the inverse-automorphism pullback
square. This is the inverse of the left-adjoint mate of the forward pullback square.
Source: latest blueprint, compactification transport in the second paragraph
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
def constantExtensionOpenExchange {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (aX : X ≅ X) (aZ : Z ≅ Z) (hj : CommSq aX.hom j j aZ.hom) :
    openImmersionLowerShriek Λ j ⋙ upperStar Λ aZ.hom ≅
      upperStar Λ aX.hom ⋙ openImmersionLowerShriek Λ j :=
  (conjugateIsoEquiv
    ((constantExtensionPullEquivalence Λ aX).toAdjunction.comp
      (openImmersionLowerShriekUpperStarAdjunction Λ j))
    ((openImmersionLowerShriekUpperStarAdjunction Λ j).comp
      (constantExtensionPullEquivalence Λ aZ).toAdjunction)).symm
        (upperStarSquareComparison Λ hj.horiz_inv).symm

/-- The derived pullback square, with the termwise localization compositors retained.
Source: latest blueprint, canonical pullback composition
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
def constantExtensionDerivedSquare {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' f' f g) :
    (upperStar Λ g).mapDerivedCategory ⋙ (upperStar Λ f').mapDerivedCategory ≅
      (upperStar Λ f).mapDerivedCategory ⋙ (upperStar Λ g').mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarSquareComparison Λ sq) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The direct proper-image exchange: unit, pullback-square comparison, then counit.
Source: latest blueprint, compactification transport
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
def constantExtensionProperExchange {Z S : Scheme.{u}} (p : Z ⟶ S)
    (aZ : Z ≅ Z) (aS : S ≅ S) (hp : CommSq aZ.hom p p aS.hom) :
    (lowerStar Λ p).rightDerivedFunctor ⋙ (upperStar Λ aS.hom).mapDerivedCategory ⟶
      (upperStar Λ aZ.hom).mapDerivedCategory ⋙ (lowerStar Λ p).rightDerivedFunctor :=
  Adjunction.exchangeRight
    ((upperStarLowerStarAdjunction Λ p).mapDerivedCategoryRightDerivedAdjunction)
    ((upperStarLowerStarAdjunction Λ p).mapDerivedCategoryRightDerivedAdjunction)
    (constantExtensionDerivedSquare Λ hp)

/-- The direct exchange on the compactification composite, before taking sections.
Source: latest blueprint, compact-support transport
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
def constantExtensionCompactExchange {X S : Scheme.{u}} {f : X ⟶ S}
    (c : Compactification f) (aX : X ≅ X) (aZ : c.Z ≅ c.Z) (aS : S ≅ S)
    (hj : CommSq aX.hom c.i c.i aZ.hom) (hp : CommSq aZ.hom c.g c.g aS.hom) :
    rightDerivedLowerShriekOfCompactification Λ c ⋙
        (upperStar Λ aS.hom).mapDerivedCategory ⟶
      (upperStar Λ aX.hom).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification Λ c :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (constantExtensionProperExchange Λ c.g aZ aS hp) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).inv ≫
        (Functor.mapDerivedCategoryNatIso
          (constantExtensionOpenExchange Λ c.i aX aZ hj)).hom ≫
        (Functor.mapDerivedCategoryCompIso _ _).hom) _ ≫
    (Functor.associator _ _ _).hom

end AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.CondensedWeil

/-- Direct geometric-point insertion in the ordinary derived coefficient category.
It derives the specified point trivialization and applies a given functor out of the
derived category of the point (below: derived geometric evaluation).
Source: latest blueprint, second proof paragraph
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
def derivedPointInsertion (l : ℕ) [Fact l.Prime]
    (K : Type u) [Field K] [IsAlgClosed K] (d : Spec (.of K) ⟶ Spec (.of K))
    {C : Type v} [Category.{w} C]
    (F : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of K)))) ⥤ C) :
    F ≅ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) d).mapDerivedCategory ⋙ F :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
        (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) d) ≪≫
          Functor.mapDerivedCategoryIdIso _).symm F

/-- Direct compact-support transport: geometric-point insertion, then the open/proper mates.
Source: latest blueprint, second proof paragraph
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
def compactTransport (l : ℕ) [Fact l.Prime]
    (K : Type u) [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of K)} (c : Compactification f)
    (a : X ≅ X) (b : c.Z ≅ c.Z) (d : Spec (.of K) ≅ Spec (.of K))
    (hj : CommSq a.hom c.i c.i b.hom) (hp : CommSq b.hom c.g c.g d.hom) :
    condensedQbarCompactSections l K c ⟶
      (AlgebraicGeometry.ProEtale.CondensedRing.upperStar
        (Profinite.padicAlgClRingObj l) a.hom).mapDerivedCategory ⋙
          condensedQbarCompactSections l K c :=
  Functor.whiskerLeft _ (derivedPointInsertion l K d.hom _).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (AlgebraicGeometry.ProEtale.CondensedRing.constantExtensionCompactExchange
        (Profinite.padicAlgClRingObj l) c a b d hj hp) _ ≫
    (Functor.associator _ _ _).hom

/-- The proper compactification model, with a named Over presentation.
Source: compactification of the finite-field structure map
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
def compactModel (D : FiniteFieldDatum.{u}) (X₀ : Over (Spec (.of D.k₀)))
    (c₀ : Compactification X₀.hom) : Over (Spec (.of D.k₀)) :=
  Over.mk c₀.g

/-- Finite type of the proper compactification model, in its Over presentation.
Source: definition of compactification
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
instance compactModel_lft (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) (c₀ : Compactification X₀.hom) :
    LocallyOfFiniteType (compactModel D X₀ c₀).hom :=
  inferInstanceAs (LocallyOfFiniteType c₀.g)

/-- Quasi-compactness of the proper compactification model in its Over presentation.
Source: definition of compactification
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
instance compactModel_qc (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) (c₀ : Compactification X₀.hom) :
    QuasiCompact (compactModel D X₀ c₀).hom :=
  inferInstanceAs (QuasiCompact c₀.g)

/-- Base change of an actual compactification of the finite-field model.
Source: latest blueprint, compactification paragraph
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
def compactBase (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (c₀ : Compactification X₀.hom) : Compactification (D.geometricFiber X₀).hom :=
  { Z := (D.geometricFiber (compactModel D X₀ c₀)).left
    g := (D.geometricFiber (compactModel D X₀ c₀)).hom
    i := zlFiberMap D (Over.homMk c₀.i c₀.comm.symm : X₀ ⟶ compactModel D X₀ c₀)
    comm := ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
        (Over.homMk c₀.i c₀.comm.symm : X₀ ⟶ compactModel D X₀ c₀)).w.symm
    isProper := inferInstanceAs (IsProper (pullback.snd c₀.g
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    isOpenImmersion := MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
      (Over.homMk c₀.i c₀.comm.symm : X₀ ⟶ compactModel D X₀ c₀) c₀.isOpenImmersion }

/-- A positive power is invertible by iterated composition of the given inverse.
Source: latest blueprint, geometric Frobenius powers
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
instance positiveIso {X : Scheme.{u}} (a : X ≅ X) :
    (n : ℕ) → IsIso (localPositivePower a.hom n)
  | 0 => a.isIso_hom
  | n + 1 => IsIso.comp_isIso' (positiveIso a n) a.isIso_hom

/-- The automorphism with the literal positive-power morphism as its hom.
Source: latest blueprint, geometric Frobenius powers
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
def positiveAut {X : Scheme.{u}} (a : X ≅ X) (n : ℕ) : X ≅ X :=
  @asIso _ _ _ _ (localPositivePower a.hom n) (positiveIso a n)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

set_option maxHeartbeats 2000000 in
-- Check the two definitionally equal presentations of the base-changed open immersion.
/-- The open factor commutes with Frobenius by the existing naturality theorem.
Source: latest blueprint, compactification transport
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
abbrev compactOpenSquare (c₀ : Compactification X₀.hom) :
    CommSq (D.geometricFrobenius X₀).hom (compactBase D X₀ c₀).i
      (compactBase D X₀ c₀).i (D.geometricFrobenius (compactModel D X₀ c₀)).hom :=
  ⟨zlFrobenius_naturality D
    (Over.homMk c₀.i c₀.comm.symm : X₀ ⟶ compactModel D X₀ c₀)⟩

/-- The proper factor commutes with Frobenius by its second projection identity.
Source: latest blueprint, compactification transport
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
abbrev compactProperSquare (c₀ : Compactification X₀.hom) :
    CommSq (D.geometricFrobenius (compactModel D X₀ c₀)).hom (compactBase D X₀ c₀).g
      (compactBase D X₀ c₀).g (frobeniusPointIso D).hom :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  ⟨(D.galoisMap_projections c₀.g
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)).2⟩

/-- Direct Frobenius for exponent n+1, recomputed from powered scheme maps, open and
proper exchanges, and geometric-point insertion; followed by the iterated Weil map.
Source: latest blueprint, constant-extension paragraph
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
def compactFrobenius (c₀ : Compactification X₀.hom)
    (M : WeilModule D l X₀) (n : ℕ) : End ((condensedQbarCompactSections l D.k
      (compactBase D X₀ c₀)).obj ((DerivedCategory.singleFunctor _ 0).obj M.carrier)) :=
  (compactTransport l D.k (compactBase D X₀ c₀)
    (positiveAut (D.geometricFrobenius X₀) n)
    (positiveAut (D.geometricFrobenius (compactModel D X₀ c₀)) n)
    (positiveAut (frobeniusPointIso D) n)
    (Nat.rec (motive := fun r ↦ CommSq
        (localPositivePower (D.geometricFrobenius X₀).hom r) (compactBase D X₀ c₀).i
        (compactBase D X₀ c₀).i
        (localPositivePower (D.geometricFrobenius (compactModel D X₀ c₀)).hom r))
      (compactOpenSquare D X₀ c₀)
      (fun _ ih ↦ ih.horiz_comp (compactOpenSquare D X₀ c₀)) n)
    (Nat.rec (motive := fun r ↦ CommSq
        (localPositivePower (D.geometricFrobenius (compactModel D X₀ c₀)).hom r)
        (compactBase D X₀ c₀).g (compactBase D X₀ c₀).g
        (localPositivePower (frobeniusPointIso D).hom r))
      (compactProperSquare D X₀ c₀)
      (fun _ ih ↦ ih.horiz_comp (compactProperSquare D X₀ c₀)) n)).app
      ((DerivedCategory.singleFunctor _ 0).obj M.carrier) ≫
    (condensedQbarCompactSections l D.k (compactBase D X₀ c₀)).map
      (derivedTheta (Profinite.padicAlgClRingObj l) _ M.carrier
        (iterate (Profinite.padicAlgClRingObj l) _ M.carrier M.str n)).hom

end WeilConjectures.CondensedWeil

namespace WeilConjectures.CondensedWeil

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [hsep : IsSeparated X₀.hom] (M : WeilModule D l X₀)
    (hc : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (hlis : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (e : ℕ) (he : 1 ≤ e)

/-- Actual constant extension, along the canonical geometric-fibre identification.
Source: blueprint constant-extension paragraph, theta^[e]
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
@[irreducible] def extend (e : ℕ) (he : 1 ≤ e)
    (M : WeilModule D l X₀) :
    WeilModule (constantExtensionDatum D e he) l (constantExtensionModel D e he X₀) :=
  (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    (CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj l)
      (CommSq.mk (constantExtensionFiber_return D e he X₀))).symm).obj
        (CategoryTheory.Endofunctor.IsoAlgebra.mk M.carrier
          (iterate (Profinite.padicAlgClRingObj l) _ M.carrier M.str (e - 1)))

/-- Restriction of the actual Weil module along a morphism of models.
Source: blueprint restriction to open and closed constant-field components
(blueprint: lem-zl-condensed-constant-extension-frobenius). -/
@[irreducible] def restrict {U₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] (j : U₀ ⟶ X₀)
    (M : WeilModule D l X₀) : WeilModule D l U₀ :=
  (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    (CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj l)
      (CommSq.mk (zlFrobenius_naturality D j))).symm).obj M

include hsep hl hc hlis he

/-- The directly induced q^e-Frobenius on ordinary derived compact support is the
eth power of q-Frobenius, before passing to individual cohomology groups.
Source: latest blueprint, second paragraph
(blueprint: lem-zl-condensed-constant-extension-frobenius).

Proof: base-change a compactification over k₀. The three Frobenius automorphisms
commute with its open and proper maps. Proper base change and the inverse open mate
compose, and the canonical geometric-point insertion composes with them. Their
naturality gives tau_(r+1) = tau_r followed by the transport on the rth pullback.
Writing u_r for the ordered Weil iterate, naturality moves u_r through tau; hence
H(u_(r+1)) tau_(r+1) = F_q (H(u_r) tau_r). Induct from u_1 = theta to obtain
F_(q^e) = F_q^e. All arrows are in the ordinary derived module category. -/
theorem constantExtension_compactFrobenius_power (c₀ : Compactification X₀.hom) :
    compactFrobenius D l X₀ c₀ M (e - 1) =
      compactFrobenius D l X₀ c₀ M 0 ^ e := by sorry

/-- Constant extension retains lissity on the same geometrically identified module.
Source: latest blueprint, second paragraph
(blueprint: lem-zl-condensed-constant-extension-frobenius).

Proof: the canonical fibre isomorphism identifies the two underlying sheaves.
Pull back a pro-etale finite-free trivializing cover along that isomorphism.
The ordered composite of theta and its pullbacks is invertible, including rank zero. -/
theorem constantExtension_lisse :
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      (extend D l X₀ e he M).carrier := by sorry

/-- The local operator after extension is conjugate to the residue-degree power,
for every compatible geometric lift on each side.
Source: latest blueprint, second paragraph
(blueprint: lem-zl-condensed-constant-extension-frobenius).

Proof: write d=[kappa(x):k₀], t=[kappa(z):k_e] and f=[kappa(z):kappa(x)].
Finite-field degree multiplicativity gives et=df. The t-fold return of the new
structure is the et-fold return of theta, including point reparametrization.
The local return formula identifies this with F_x^f. Changing either geometric
lift conjugates the operator, so the conclusion holds for all choices. -/
theorem constantExtension_local_conjugacy
    (z : {z : (constantExtensionModel D e he X₀).left //
      z ∈ closedPoints (constantExtensionModel D e he X₀).left})
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (hx : (constantExtensionProjection D e he X₀).left z.val = x.val)
    (iz : (constantExtensionModel D e he X₀).left.residueField z.val →+* D.k)
    (hiz : iz.comp ((constantExtensionModel D e he X₀).hom.residueFieldAlgebraMap z.val) =
      @algebraMap (constantExtensionDatum D e he).k₀ (constantExtensionDatum D e he).k
        (constantExtensionDatum D e he).field_base.toCommSemiring
        (constantExtensionDatum D e he).field_closure.toSemiring
        (constantExtensionDatum D e he).algebra_closure)
    (ix : X₀.left.residueField x.val →+* D.k)
    (hix : ix.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    ∃ b : closedFiber (constantExtensionDatum D e he) l (constantExtensionModel D e he X₀)
        (extend D l X₀ e he M) z iz hiz ≅ closedFiber D l X₀ M x ix hix,
      closedOperator (constantExtensionDatum D e he) l (constantExtensionModel D e he X₀)
          (extend D l X₀ e he M) z iz hiz ≫ b.hom =
        b.hom ≫ closedOperator D l X₀ M x ix hix ^
          constantExtensionResidueDegree D e he X₀ z.val := by sorry

/-- Punctual purity is preserved for every field embedding and every real weight.
Source: latest blueprint, second paragraph
(blueprint: lem-zl-condensed-constant-extension-frobenius).

Proof: stalks are finite-dimensional and the spectrum of F_x^f consists of the
fth powers of its eigenvalues, without semisimplicity. Conjugacy preserves spectra.
For each embedding iota, |iota(alpha^f)| = |iota(alpha)|^f and q_z=q_x^f;
therefore the weight remains w. The zero stalk contributes no eigenvalue. -/
theorem constantExtension_pure (iota : PadicAlgCl l →+* ℂ) (w : ℝ) :
    Pure D l X₀ M iota w →
      Pure (constantExtensionDatum D e he) l (constantExtensionModel D e he X₀)
        (extend D l X₀ e he M) iota w := by sorry

/-- Restriction to an open and closed subscheme over the extended finite field
preserves lissity and every specified punctual weight.
Source: latest blueprint, second paragraph
(blueprint: lem-zl-condensed-constant-extension-frobenius).

Proof: restrict a finite-free pro-etale trivializing cover. A clopen subscheme is
Frobenius-stable. Its closed points are closed in the ambient model with identical
residue fields. Pullback composition identifies their local returns, so the purity
equations are unchanged. The empty subscheme and rank zero have zero stalks. -/
theorem constantExtension_clopen_restriction
    (V₀ : Over (Spec (.of (constantExtensionDatum D e he).k₀)))
    [LocallyOfFiniteType V₀.hom] [QuasiCompact V₀.hom]
    (j : V₀ ⟶ constantExtensionModel D e he X₀)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ) :
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      (restrict (constantExtensionDatum D e he) l (constantExtensionModel D e he X₀)
        j (extend D l X₀ e he M)).carrier ∧
      (Pure (constantExtensionDatum D e he) l (constantExtensionModel D e he X₀)
          (extend D l X₀ e he M) iota w →
        Pure (constantExtensionDatum D e he) l V₀
          (restrict (constantExtensionDatum D e he) l (constantExtensionModel D e he X₀)
            j (extend D l X₀ e he M)) iota w) := by sorry

end WeilConjectures.CondensedWeil
