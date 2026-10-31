/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
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
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans

import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull

/-!
# Direct condensed compactification transport under automorphisms

Source: latest blueprint, sec-deligne-laumon-general,
sk-p-dl-general-relative-line/lem-zl-affine-curve-hc2-purity.proof.md, second paragraph
(blueprint: lem-zl-condensed-compactification-automorphism-transport).

The section datum below is normalized by equality on every section, and the open exchange
by its inverse mate. Thus the existential conclusion specifies the direct constructions;
it does not posit an arbitrary action or define transport by recursion. All categories
are ordinary unbounded derived categories. Section rings and section modules are the
existing internal-module/sectionwise-module equivalence, with their actual tensor actions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedCompactificationTransport

open CondensedRing
open CategoryTheory.InternalAbelianSheafModule

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing module-object category, only abbreviated for the transport signature.
Source: latest blueprint, ordinary condensed transport, coefficient paragraph
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
abbrev Modules (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)

/-- The actual singleton section ring of the condensed coefficient object.
Source: latest blueprint, ordinary condensed transport, definition of V
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
abbrev Scalars :=
  (sectionRings (coherentTopology Profinite.{u}) Λ).obj
    (op (Profinite.of (ULift.{u, 0} PUnit.{1})))

/-- The actual final-object section ring of the pulled-back coefficient object.
Source: latest blueprint, ordinary condensed transport, definition of V
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
abbrev SectionScalars (T : Scheme.{u}) :=
  (sectionRings (Scheme.ProEt.topology T) (condensedRingObj Λ T)).obj
    (op (Scheme.ProEt.mk (𝟙 T)))

/-- Final-object module sections, followed by the displayed restriction of scalars.
Source: latest blueprint, ordinary condensed transport, definition of V
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
def sections (T : Scheme.{u}) (σ : Scalars Λ →+* SectionScalars Λ T) :
    Modules Λ T ⥤ ModuleCat.{u + 1} (Scalars Λ) :=
  sectionModuleFunctor (Scheme.ProEt.topology T) (condensedRingObj Λ T) ⋙
    SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation _ (op (Scheme.ProEt.mk (𝟙 T))) ⋙
    ModuleCat.restrictScalars σ

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- The canonical point-unit scalar insertion, as an additive map on sections.
The singleton test object is identified with the final object by its structural map.
Source: latest blueprint, ordinary condensed transport, definition of V
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
def scalarInsertion :
    Λ.obj.obj (op (Profinite.of (ULift.{u, 0} PUnit.{1}))) ⟶
      (condensedRingObj Λ (Spec (.of k))).obj.obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) := by
  letI : IsIso (geometricFieldTestFinalMap (Spec (.of k))) :=
    (geometric_field_proetale_evaluation k).2.2.2.2.2.2.2.1
  exact ((geometricFieldAbelianPointAdjunction (Spec (.of k))).unit.app Λ).hom.app
      (op (Profinite.of (ULift.{u, 0} PUnit.{1}))) ≫
    (condensedRingObj Λ (Spec (.of k))).obj.map
      (inv (geometricFieldTestFinalMap (Spec (.of k)))).op

/-- Restriction/inverse-image insertion followed by tensor scalar insertion.
The inverse of extendScalarsIsoComapInv is exactly x mapped to 1 tensor x.
Source: latest blueprint, ordinary condensed transport, definition of i
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
def sectionInsertion (h : Spec (.of k) ≅ Spec (.of k)) (M : Modules Λ (Spec (.of k))) :
    M.X.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) ⟶
      ((CondensedRing.upperStar Λ h.hom).obj M).X.obj.obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) :=
  (geometricFieldEvaluationComparison h.hom Ab.{u + 1}).app M.X ≫
    (((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ h.hom)).app
      (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} h.hom).mapMod
        (condensedRingObj Λ (Spec (.of k)))).obj M)).inv.hom.hom.app
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))

/-- The point-section construction with its canonical scalar and insertion normalizations.
Each arrow is fixed on every section, so this datum contains no free choice of transport.
Its existence, exactness, and all derived transport laws are asserted together below.
Source: latest blueprint, ordinary condensed transport, definition of V and i
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
structure PointSections where
  scalar : Scalars Λ →+* SectionScalars Λ (Spec (.of k))
  scalar_eq (x : Scalars Λ) : scalar x = scalarInsertion Λ k x
  additive : (sections Λ (Spec (.of k)) scalar).Additive
  limits : PreservesFiniteLimits (sections Λ (Spec (.of k)) scalar)
  colimits : PreservesFiniteColimits (sections Λ (Spec (.of k)) scalar)
  insertion (h : Spec (.of k) ≅ Spec (.of k)) :
    sections Λ (Spec (.of k)) scalar ⟶
      CondensedRing.upperStar Λ h.hom ⋙ sections Λ (Spec (.of k)) scalar
  insertion_eq (h : Spec (.of k) ≅ Spec (.of k)) (M : Modules Λ (Spec (.of k)))
      (x : M.X.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) :
    (insertion h).app M x = sectionInsertion Λ k h M x

/-- The exact section functor derived termwise, with the exactness proofs stored explicitly.
Source: latest blueprint, ordinary condensed transport, definition of V
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
def PointSections.derived (S : PointSections Λ k) :
    DerivedCategory (Modules Λ (Spec (.of k))) ⥤
      DerivedCategory (ModuleCat.{u + 1} (Scalars Λ)) := by
  letI := S.additive
  letI := S.limits
  letI := S.colimits
  exact (sections Λ (Spec (.of k)) S.scalar).mapDerivedCategory

/-- Termwise localization of the specified insertion, with the canonical composition comparison.
Source: latest blueprint, ordinary condensed transport, definition of i
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
def PointSections.derivedInsertion (S : PointSections Λ k)
    (h : Spec (.of k) ≅ Spec (.of k)) :
    PointSections.derived Λ k S ⟶
      (CondensedRing.upperStar Λ h.hom).mapDerivedCategory ⋙ PointSections.derived Λ k S := by
  letI := S.additive
  letI := S.limits
  letI := S.colimits
  exact Functor.mapDerivedCategoryNatTrans (S.insertion h) ≫
    (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ h.hom)
      (sections Λ (Spec (.of k)) S.scalar)).hom

/-- The canonical termwise pullback compositor, induced from the recorded module compositor.
Source: latest blueprint, ordinary condensed transport, c_(a,b)
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
def pullbackComp {T U V : Scheme.{u}} (f : T ⟶ U) (g : U ⟶ V) :
    (CondensedRing.upperStar Λ (f ≫ g)).mapDerivedCategory ≅
      (CondensedRing.upperStar Λ g).mapDerivedCategory ⋙ (CondensedRing.upperStar Λ
      f).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ f g) ≪≫
    Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ g) (CondensedRing.upperStar Λ f)

variable {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  (c : Compactification.BoundaryCompactification f)

/-- A componentwise scheme automorphism of the given compactification.
Source: latest blueprint, ordinary condensed transport, automorphism paragraph
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
structure Automorphism where
  onX : X ≅ X
  onZ : c.obj.obj.Z ≅ c.obj.obj.Z
  onS : Spec (.of k) ≅ Spec (.of k)
  open_comm : onX.hom ≫ c.obj.obj.i = c.obj.obj.i ≫ onZ.hom
  proper_comm : onZ.hom ≫ c.obj.obj.g = c.obj.obj.g ≫ onS.hom

/-- Componentwise identity automorphism.
Source: latest blueprint, ordinary condensed transport, identity clause
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
def Automorphism.identity : Automorphism k c where
  onX := Iso.refl _
  onZ := Iso.refl _
  onS := Iso.refl _
  open_comm := by simp
  proper_comm := by simp

/-- Componentwise b after a; no commutativity of automorphisms is assumed.
Source: latest blueprint, ordinary condensed transport, composition clause
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
def Automorphism.then (a b : Automorphism k c) : Automorphism k c where
  onX := a.onX ≪≫ b.onX
  onZ := a.onZ ≪≫ b.onZ
  onS := a.onS ≪≫ b.onS
  open_comm := by
    simp only [Iso.trans_hom]
    rw [Category.assoc, b.open_comm, ← Category.assoc, a.open_comm, Category.assoc]
  proper_comm := by
    simp only [Iso.trans_hom]
    rw [Category.assoc, b.proper_comm, ← Category.assoc, a.proper_comm, Category.assoc]

set_option maxHeartbeats 1000000 in
-- The two derived adjunction structures in this comparison require more elaboration heartbeats.
/-- The canonical pullback comparison used in the proper exchange mate.
Source: latest blueprint, ordinary condensed transport, definition of e;
def-weil-pbc-ambient-ringed-exchange, unit--comparison--counit formula
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
def properComparison (a : Automorphism k c) :
    (CondensedRing.upperStar Λ a.onS.hom).mapDerivedCategory ⋙
        (CondensedRing.upperStar Λ c.obj.obj.g).leftDerivedFunctor ≅
      (CondensedRing.upperStar Λ c.obj.obj.g).leftDerivedFunctor ⋙
        (CondensedRing.upperStar Λ a.onZ.hom).mapDerivedCategory :=
  Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ a.onS.hom).symm _ ≪≫
    (leftDerivedUpperStarComp Λ c.obj.obj.g a.onS.hom).symm ≪≫
    eqToIso (congrArg (fun h ↦ (CondensedRing.upperStar Λ h).leftDerivedFunctor)
      a.proper_comm.symm) ≪≫
    leftDerivedUpperStarComp Λ a.onZ.hom c.obj.obj.g ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory Λ a.onZ.hom)

/-- The actual unit--comparison--counit proper exchange, transported to termwise pullbacks.
Source: latest blueprint, ordinary condensed transport, definition of e;
def-weil-pbc-ambient-ringed-exchange
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
def properExchange (a : Automorphism k c) :
    (CondensedRing.lowerStar Λ c.obj.obj.g).rightDerivedFunctor ⋙
        (CondensedRing.upperStar Λ a.onS.hom).mapDerivedCategory ⟶
      (CondensedRing.upperStar Λ a.onZ.hom).mapDerivedCategory ⋙
        (CondensedRing.lowerStar Λ c.obj.obj.g).rightDerivedFunctor :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction Λ c.obj.obj.g)
    (derivedUpperStarLowerStarAdjunction Λ c.obj.obj.g)
    (TwoSquare.mk _ _ _ _ (properComparison Λ k c a).hom)).natTrans

/-- The open pullback comparison, in the direction whose inverse mate is the open exchange.
Source: latest blueprint, ordinary condensed transport, definition of the open exchange
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
def openComparison (a : Automorphism k c) :
    (CondensedRing.upperStar Λ c.obj.obj.i).mapDerivedCategory ⋙
        (CondensedRing.upperStar Λ a.onX.hom).mapDerivedCategory ≅
      (CondensedRing.upperStar Λ a.onZ.hom).mapDerivedCategory ⋙
        (CondensedRing.upperStar Λ c.obj.obj.i).mapDerivedCategory :=
  (pullbackComp Λ a.onX.hom c.obj.obj.i).symm ≪≫
    eqToIso (congrArg (fun h ↦ (CondensedRing.upperStar Λ h).mapDerivedCategory) a.open_comm) ≪≫
    pullbackComp Λ c.obj.obj.i a.onZ.hom

/-- The left-adjoint mate before inversion, using D(j_!) adjoint to j^*.
Source: latest blueprint, ordinary condensed transport, definition of the open exchange
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
def openMate (a : Automorphism k c) :
    (CondensedRing.upperStar Λ a.onX.hom).mapDerivedCategory ⋙
        (CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory ⟶
      (CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory ⋙
        (CondensedRing.upperStar Λ a.onZ.hom).mapDerivedCategory :=
  ((mateEquiv (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i)).symm
      (TwoSquare.mk _ _ _ _ (openComparison Λ k c a).hom)).natTrans

/-- Open exchange objects with the exact endpoints required by the statement.
Their inverses are required to equal openMate in the theorem, so no exchange is chosen freely.
Source: latest blueprint, ordinary condensed transport, definition of e
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
abbrev OpenExchange (a : Automorphism k c) :=
  (CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory ⋙
      (CondensedRing.upperStar Λ a.onZ.hom).mapDerivedCategory ≅
    (CondensedRing.upperStar Λ a.onX.hom).mapDerivedCategory ⋙
      (CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory

/-- The specified composite e: proper mate followed by the image of the open exchange.
Source: latest blueprint, ordinary condensed transport, definition of e
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
def exchange (a : Automorphism k c) (O : OpenExchange Λ k c a) :
    rightDerivedLowerShriekOfCompactification Λ c.obj.obj ⋙
        (CondensedRing.upperStar Λ a.onS.hom).mapDerivedCategory ⟶
      (CondensedRing.upperStar Λ a.onX.hom).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification Λ c.obj.obj :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (properExchange Λ k c a) ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight O.hom _ ≫
    (Functor.associator _ _ _).hom

/-- Direct transport: insertion at CK followed by V(e_K), with no recursive definition.
Source: latest blueprint, ordinary condensed transport, displayed definition of tau
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
def transport (S : PointSections Λ k) (a : Automorphism k c) (O : OpenExchange Λ k c a) :
    rightDerivedLowerShriekOfCompactification Λ c.obj.obj ⋙ (PointSections.derived Λ k S) ⟶
      (CondensedRing.upperStar Λ a.onX.hom).mapDerivedCategory ⋙
        (rightDerivedLowerShriekOfCompactification Λ c.obj.obj ⋙ (PointSections.derived Λ k S)) :=
  Functor.whiskerLeft _ (PointSections.derivedInsertion Λ k S a.onS) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (exchange Λ k c a O) (PointSections.derived Λ k S) ≫
    (Functor.associator _ _ _).hom

/-- The specified direct automorphism transport is invertible, composes in order b after a,
and is the identity under the canonical identity-pullback comparison.
Source: latest blueprint, sec-deligne-laumon-general, sk-p-dl-general-relative-line,
lem-zl-affine-curve-hc2-purity.proof.md, second paragraph
(blueprint: lem-zl-condensed-compactification-automorphism-transport).

Proof: (1) Isomorphism-square exchange gives invertibility of the proper and open mates.
Point sections are exact for every ring sheaf over the algebraically closed field;
restriction of scalars is exact, so derive V termwise. (2) The direct-image compositor
is induced by iterated fibre products; their universal property gives associativity
and units. Adjunction conjugation gives the same laws for pullback and the coefficient
identifications. (3) Inverse image along an isomorphism is reindexing by postcomposition;
the graph insertion identifies its sections. Extension along the coefficient isomorphism
sends x to 1 tensor x. (4) Compatibility of the point-adjunction unit with the coefficient
comparison proves Lambda(*)-linearity of insertion, without assuming constant coefficients.
(5) In these coordinates the insertion composite is restriction along b_s a_s. Exactness
and the localization universal property descend this equality to unbounded complexes.
(6) Mate pasting applied to the proper pullback comparisons gives proper-exchange pasting.
(7) The same argument for j_! adjoint to j^*, followed by inversion, gives open-exchange
pasting. (8) Naturality of the proper mate moves the open exchange across it and proves
pasting for e. (9) Naturality of insertion at e_b, followed by these two pasting equations,
gives tau_d = H(c_(a,b)) tau_(a,P_b K) tau_b. Identity mates and identity restriction give
the last clause. The dependencies are the mate-pasting, conjugation and localization nodes,
the module pullback compositors, and lem-weil-point-proetale-sections-exact. -/
theorem automorphism_transport :
    ∃ S : PointSections Λ k,
      ∃ O : ∀ a : Automorphism k c, OpenExchange Λ k c a,
        (∀ a, (O a).inv = openMate Λ k c a) ∧
        (∀ a, IsIso (exchange Λ k c a (O a))) ∧
        (∀ a, IsIso (transport Λ k c S a (O a))) ∧
        (∀ (a b : Automorphism k c) (K : DerivedCategory (Modules Λ X)),
          (transport Λ k c S (Automorphism.then k c a b) (O (Automorphism.then k c a b))).app K =
            (transport Λ k c S b (O b)).app K ≫
              (transport Λ k c S a (O a)).app
                ((CondensedRing.upperStar Λ b.onX.hom).mapDerivedCategory.obj K) ≫
              (rightDerivedLowerShriekOfCompactification Λ c.obj.obj ⋙
                PointSections.derived Λ k S).map
                ((pullbackComp Λ a.onX.hom b.onX.hom).inv.app K)) ∧
        (∀ K : DerivedCategory (Modules Λ X),
          (transport Λ k c S (Automorphism.identity k c)
            (O (Automorphism.identity k c))).app K ≫
            (rightDerivedLowerShriekOfCompactification Λ c.obj.obj ⋙
              PointSections.derived Λ k S).map
              ((Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ X) ≪≫
                Functor.mapDerivedCategoryIdIso (Modules Λ X)).hom.app K) = 𝟙 _) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedCompactificationTransport
