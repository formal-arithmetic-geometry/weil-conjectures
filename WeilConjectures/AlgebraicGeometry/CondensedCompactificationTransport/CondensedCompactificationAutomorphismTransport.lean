/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull

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

/-- Open exchange objects with the exact endpoints required by the statement.
Their inverses are required to equal openMate in the theorem, so no exchange is chosen freely.
Source: latest blueprint, ordinary condensed transport, definition of e
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
abbrev OpenExchange (a : Automorphism k c) :=
  (CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory ⋙
      (CondensedRing.upperStar Λ a.onZ.hom).mapDerivedCategory ≅
    (CondensedRing.upperStar Λ a.onX.hom).mapDerivedCategory ⋙
      (CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory

end AlgebraicGeometry.ProEtale.CondensedCompactificationTransport
