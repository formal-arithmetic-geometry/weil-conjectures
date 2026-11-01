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
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.InverseMateEquivalence
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapUnit
public import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointTrivializationComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.WeilObject.Sheaf.StalkFrobenius

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

private theorem point_from_test
    {C : Type*} [Category C] {A B A' B' : C}
    (f : A ⟶ B) (g : B ⟶ A) (q : A ⟶ A') (q' : B ⟶ B')
    (r : A' ⟶ B') (s : B' ⟶ A') [Mono q]
    (hf : q ≫ r = f ≫ q') (hg : q' ≫ s = g ≫ q) (h : r ≫ s = 𝟙 _) :
    f ≫ g = 𝟙 _ := by
  apply (cancel_mono q).1
  calc
    (f ≫ g) ≫ q = f ≫ (q' ≫ s) := by rw [Category.assoc, hg]
    _ = (q ≫ r) ≫ s := by rw [hf, Category.assoc]
    _ = 𝟙 _ ≫ q := by rw [Category.assoc, h, Category.comp_id, Category.id_comp]

private theorem normalize_square
    {C D : Type*} [Category C] [Category D]
    {S S' : C ⥤ C} {P P' : C ⥤ D} {Z Z' : D ⥤ D}
    {U U' V V' : C ⥤ D}
    (s : S ≅ S') (p : P ≅ P') (z : Z ≅ Z')
    (u : U ≅ U') (v : V ≅ V')
    (a : U' ≅ S' ⋙ P') (b : V' ≅ P' ⋙ Z') (e : U' ≅ V') :
    Functor.isoWhiskerRight s.symm P ≪≫
      (u ≪≫ a ≪≫ Functor.isoWhiskerRight s.symm P' ≪≫
        Functor.isoWhiskerLeft S p.symm).symm ≪≫
      (u ≪≫ e ≪≫ v.symm) ≪≫
      (v ≪≫ b ≪≫ Functor.isoWhiskerRight p.symm Z' ≪≫
        Functor.isoWhiskerLeft P z.symm) ≪≫
      Functor.isoWhiskerLeft P z =
    Functor.isoWhiskerLeft S' p ≪≫ a.symm ≪≫ e ≪≫ b ≪≫
      Functor.isoWhiskerRight p.symm Z' := by
  apply Iso.ext
  ext N
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rw [reassoc_of% p.hom.naturality (s.inv.app N)]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Functor.comp_obj,
    Category.id_comp, Category.comp_id]

private theorem exactTrivialization_comp
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F G H : C ⥤ C) [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (c : H ≅ F ⋙ G) (a : F ≅ 𝟭 C) (b : G ≅ 𝟭 C)
    (d : H ≅ 𝟭 C)
    (hd : c ≪≫ Functor.isoWhiskerRight a G ≪≫ Functor.leftUnitor G ≪≫ b = d)
    (K : DerivedCategory C) :
    (Functor.mapDerivedCategoryNatIso c).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso F G).hom.app K ≫
        G.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso a).hom.app K ≫
          (Functor.mapDerivedCategoryIdIso C).hom.app K) ≫
        (Functor.mapDerivedCategoryNatIso b).hom.app K ≫
        (Functor.mapDerivedCategoryIdIso C).hom.app K =
      (Functor.mapDerivedCategoryNatIso d).hom.app K ≫
        (Functor.mapDerivedCategoryIdIso C).hom.app K := by
  have hn := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight a G) K
  have hu := NatTrans.congr_app (Functor.mapDerivedCategoryCompIso_id_comp G) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hn hu
  have ht := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom.app K) hd
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at ht
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  rw [reassoc_of% hu]
  have hi : (Functor.mapDerivedCategoryNatIso (Functor.leftUnitor G)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  rw [hi] at ht
  simp only [NatTrans.id_app] at ht
  erw [Category.id_comp] at ht
  erw [Category.id_comp]
  simpa only [Category.assoc] using
    congrArg (· ≫ (Functor.mapDerivedCategoryIdIso C).hom.app K) ht

private theorem exchange_slide
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (P : C ⥤ C) (Q : D ⥤ D) (e : F ⋙ Q ⟶ P ⋙ F)
    {A B T U : C} {V : D} (c : T ≅ P.obj A)
    (b : A ⟶ B) (d : P.obj B ⟶ U) (a : V ⟶ Q.obj (F.obj A)) :
    (a ≫ e.app A ≫ F.map c.inv) ≫ F.map (c.hom ≫ P.map b ≫ d) =
      a ≫ Q.map (F.map b) ≫ e.app B ≫ F.map d := by
  have hn := e.naturality b
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc, c.inv_hom_id, F.map_id, Category.id_comp]
  rw [← reassoc_of% hn]

private def joinedExchange
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J : C ⥤ D) (R : D ⥤ E) (A : C ⥤ C) (B : D ⥤ D) (Q : E ⥤ E)
    (e : R ⋙ Q ⟶ B ⋙ R) (b : J ⋙ B ⟶ A ⋙ J) :
    (J ⋙ R) ⋙ Q ⟶ A ⋙ (J ⋙ R) :=
  (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft J e ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight b R ≫
    (Functor.associator _ _ _).hom

private theorem joinedExchange_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J : C ⥤ D) (R : D ⥤ E)
    (A₁ A₂ A₁₂ : C ⥤ C) (B₁ B₂ B₁₂ : D ⥤ D) (Q₁ Q₂ Q₁₂ : E ⥤ E)
    (cA : A₁₂ ≅ A₁ ⋙ A₂) (cB : B₁₂ ≅ B₁ ⋙ B₂) (cQ : Q₁₂ ≅ Q₁ ⋙ Q₂)
    (e₁ : R ⋙ Q₁ ⟶ B₁ ⋙ R) (e₂ : R ⋙ Q₂ ⟶ B₂ ⋙ R)
    (e₁₂ : R ⋙ Q₁₂ ⟶ B₁₂ ⋙ R)
    (b₁ : J ⋙ B₁ ⟶ A₁ ⋙ J) (b₂ : J ⋙ B₂ ⟶ A₂ ⋙ J)
    (b₁₂ : J ⋙ B₁₂ ⟶ A₁₂ ⋙ J)
    (he : ∀ L, e₁₂.app L = cQ.hom.app (R.obj L) ≫ Q₂.map (e₁.app L) ≫
      e₂.app (B₁.obj L) ≫ R.map (cB.inv.app L))
    (hb : ∀ K, b₁₂.app K = cB.hom.app (J.obj K) ≫ B₂.map (b₁.app K) ≫
      b₂.app (A₁.obj K) ≫ J.map (cA.inv.app K)) (K : C) :
    (joinedExchange J R A₁₂ B₁₂ Q₁₂ e₁₂ b₁₂).app K =
      cQ.hom.app ((J ⋙ R).obj K) ≫
        Q₂.map ((joinedExchange J R A₁ B₁ Q₁ e₁ b₁).app K) ≫
        (joinedExchange J R A₂ B₂ Q₂ e₂ b₂).app (A₁.obj K) ≫
        (J ⋙ R).map (cA.inv.app K) := by
  simp only [joinedExchange, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id]
  rw [he, hb]
  have h := exchange_slide R B₂ Q₂ e₂ (cB.app (J.obj K)) (b₁.app K)
    (b₂.app (A₁.obj K) ≫ J.map (cA.inv.app K))
    (cQ.hom.app ((J ⋙ R).obj K) ≫ Q₂.map (e₁.app (J.obj K)))
  simpa only [Functor.comp_obj, Functor.comp_map, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc] using h

private theorem inverse_exchange_comp
    {C D : Type*} [Category C] [Category D] (J : C ⥤ D)
    {P Q R : C ⥤ C} {A B S : D ⥤ D}
    (c : R ≅ P ⋙ Q) (d : S ≅ B ⋙ A)
    (a : J ⋙ A ≅ Q ⋙ J) (b : J ⋙ B ≅ P ⋙ J) (t : J ⋙ S ≅ R ⋙ J)
    (h : ∀ K, t.inv.app K = J.map (c.hom.app K) ≫
      a.inv.app (P.obj K) ≫ A.map (b.inv.app K) ≫ d.inv.app (J.obj K)) (K : C) :
    t.hom.app K = d.hom.app (J.obj K) ≫ A.map (b.hom.app K) ≫
      a.hom.app (P.obj K) ≫ J.map (c.inv.app K) := by
  let e := J.mapIso (c.app K) ≪≫ a.symm.app (P.obj K) ≪≫
    A.mapIso (b.symm.app K) ≪≫ d.symm.app (J.obj K)
  have he : t.symm.app K = e := by
    apply Iso.ext
    exact h K
  have hi := congrArg Iso.inv he
  simpa only [e, Iso.app_inv, Iso.symm_inv, Iso.trans_inv,
    Functor.mapIso_inv, Iso.app_hom, Category.assoc] using hi

private theorem iso_inv_comp_eq
    {C : Type*} [Category C] {A B T : C} (e : A ≅ B)
    {f : A ⟶ T} {g : B ⟶ T} (h : f = e.hom ≫ g) : e.inv ≫ f = g := by
  rw [h, Iso.inv_hom_id_assoc]

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

/-- The canonical pullback comparison used in the proper exchange mate.
Source: latest blueprint, ordinary condensed transport, definition of e;
def-weil-pbc-ambient-ringed-exchange, unit--comparison--counit formula
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
def properComparison (a : Automorphism k c) :
    (CondensedRing.upperStar Λ a.onS.hom).mapDerivedCategory ⋙
        (CondensedRing.upperStar Λ c.obj.obj.g).leftDerivedFunctor ≅
      (CondensedRing.upperStar Λ c.obj.obj.g).leftDerivedFunctor ⋙
        (CondensedRing.upperStar Λ a.onZ.hom).mapDerivedCategory :=
  Functor.isoWhiskerRight
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ a.onS.hom).symm _ ≪≫
    (CondensedRing.leftDerivedUpperStarComp Λ c.obj.obj.g a.onS.hom).symm ≪≫
    eqToIso (congrArg (fun h ↦ (CondensedRing.upperStar Λ h).leftDerivedFunctor)
      a.proper_comm.symm) ≪≫
    CondensedRing.leftDerivedUpperStarComp Λ a.onZ.hom c.obj.obj.g ≪≫
    Functor.isoWhiskerLeft _ (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ a.onZ.hom)

/-- The actual unit--comparison--counit proper exchange, transported to termwise pullbacks.
Source: latest blueprint, ordinary condensed transport, definition of e;
def-weil-pbc-ambient-ringed-exchange
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
def properExchange (a : Automorphism k c) :
    (CondensedRing.lowerStar Λ c.obj.obj.g).rightDerivedFunctor ⋙
        (CondensedRing.upperStar Λ a.onS.hom).mapDerivedCategory ⟶
      (CondensedRing.upperStar Λ a.onZ.hom).mapDerivedCategory ⋙
        (CondensedRing.lowerStar Λ c.obj.obj.g).rightDerivedFunctor :=
  (mateEquiv (CondensedRing.derivedUpperStarLowerStarAdjunction Λ c.obj.obj.g)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ c.obj.obj.g)
    (TwoSquare.mk _ _ _ _ (properComparison Λ k c a).hom)).natTrans

-- Keep scheme category instance reduction out of coefficient naturality checks.

private theorem eval_coherence (f : Spec (.of k) ⟶ Spec (.of k))
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1}) :
    B.obj.map (geometricFieldTestFinalMap (Spec (.of k))).op ≫
      ((geometricFieldRestrictionComparison f Ab).app B).hom.app
        (op (Profinite.of (ULift.{u, 0} PUnit.{1}))) =
    (geometricFieldEvaluationComparison f Ab).app B ≫
      ((Scheme.proEtaleSheafInverseImage f Ab).obj B).obj.map
        (geometricFieldTestFinalMap (Spec (.of k))).op := by
  let G := (Scheme.proEtaleSheafInverseImage f Ab).obj B
  let η := (Scheme.proEtaleSheafAdjunction f Ab).unit.app B
  have hn := η.hom.naturality (geometricFieldTestFinalMap (Spec (.of k))).op
  change B.obj.map (geometricFieldTestFinalMap (Spec (.of k))).op ≫
      η.hom.app _ = η.hom.app _ ≫
        G.obj.map ((Scheme.proEtaleBaseChange f).map
          (geometricFieldTestFinalMap (Spec (.of k)))).op at hn
  dsimp [geometricFieldRestrictionComparison, geometricFieldEvaluationComparison]
  simp only [Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    Functor.sheafPushforwardContinuous_map_hom_app, Iso.op_inv]
  rw [← Category.assoc, hn, Category.assoc]
  change η.hom.app _ ≫ G.obj.map _ ≫ G.obj.map _ =
    (η.hom.app _ ≫ G.obj.map _) ≫ G.obj.map _
  simp only [← CategoryTheory.Functor.map_comp, ← op_comp, Category.assoc]
  congr 2
  exact congrArg Quiver.Hom.op (geometricField_final_pullback_hom_ext f _ _)

private theorem unit_test (f : Spec (.of k) ⟶ Spec (.of k))
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    ((geometricFieldRestrictionComparison f Ab).app (condensedRingObj A (Spec (.of k)))).hom.app
        (op (Profinite.of (ULift.{u, 0} PUnit.{1}))) ≫
      (condensedPullbackHom A f).hom.app
        (op ((profiniteToProEtOf (Spec (.of k))).obj
          (Profinite.of (ULift.{u, 0} PUnit.{1})))) = 𝟙 _ := by
  have : IsIso (geometricFieldAbelianPointAdjunction (Spec (.of k))).unit :=
    (geometric_field_proetale_evaluation k).2.2.2.2.2.1
  let B := condensedRingObj A (Spec (.of k))
  have h : (geometricFieldRestrictionComparison f Ab).app B ≫
      (geometricFieldRestriction (Spec (.of k)) Ab).map (condensedPullbackHom A f) = 𝟙 _ := by
    apply (cancel_epi ((geometricFieldAbelianPointAdjunction (Spec (.of k))).unit.app A)).1
    simpa only [B, Functor.comp_obj, Functor.id_obj, Category.assoc, Category.comp_id] using
      CondensedCoefficientUnit.point_unit_restriction_sheaf f A
  have he := congrArg (fun w ↦ w.hom.app
    (op (Profinite.of (ULift.{u, 0} PUnit.{1})))) h
  simpa only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.comp_app, NatTrans.id_app, CondensedCoefficientUnit.restriction_map_component]
    using he

private theorem coefficient_natural (f : Spec (.of k) ⟶ Spec (.of k))
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    ((Scheme.proEtaleSheafInverseImage f Ab).obj
      (condensedRingObj A (Spec (.of k)))).obj.map
        (geometricFieldTestFinalMap (Spec (.of k))).op ≫
      (condensedPullbackHom A f).hom.app
        (op ((profiniteToProEtOf (Spec (.of k))).obj
          (Profinite.of (ULift.{u, 0} PUnit.{1})))) =
    (condensedPullbackHom A f).hom.app (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) ≫
      (condensedRingObj A (Spec (.of k))).obj.map
        (geometricFieldTestFinalMap (Spec (.of k))).op := by
  exact (condensedPullbackHom A f).hom.naturality
    (geometricFieldTestFinalMap (Spec (.of k))).op

private theorem point_normalized (f : Spec (.of k) ⟶ Spec (.of k))
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    (geometricFieldEvaluationComparison f Ab).app (condensedRingObj A (Spec (.of k))) ≫
      (condensedPullbackHom A f).hom.app
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) = 𝟙 _ := by
  have : IsIso (geometricFieldTestFinalMap (Spec (.of k))) :=
    (geometric_field_proetale_evaluation k).2.2.2.2.2.2.2.1
  exact point_from_test (C := Ab.{u + 1}) _ _
    ((condensedRingObj A (Spec (.of k))).obj.map
      (geometricFieldTestFinalMap (Spec (.of k))).op) _ _ _
    (eval_coherence k f _) (coefficient_natural k f A) (unit_test k f A)

private theorem point_evaluation (f : Spec (.of k) ⟶ Spec (.of k))
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    (geometricFieldEvaluationComparison f Ab).app (condensedRingObj A (Spec (.of k))) ≫
      ((upperStarFromPointComp f).hom.app A).hom.app
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) = 𝟙 _ := by
  simpa only [condensedPullbackHom, Functor.compAlgHom] using point_normalized k f A

private theorem insertion_on_point (h : Spec (.of k) ≅ Spec (.of k))
    (A : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    sectionInsertion Λ k h ((upperStarFromPointMod Λ (Spec (.of k))).obj A) ≫
        (((upperStarFromPointModComp Λ h.hom).hom.app A).hom.hom.app
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) = 𝟙 _ := by
  let M := (upperStarFromPointMod Λ (Spec (.of k))).obj A
  have hunit := extendUnitHom_comp_upperStarFromPointModComp_hom_app_hom Λ h.hom A
  have he := congrArg (fun w ↦ w.hom.app
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) hunit
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at he
  unfold sectionInsertion
  rw [Iso.app_inv, Mod.extendScalarsIsoComapInv_inv_app_hom,
    Mod.extendRestrictAdjunction_unit_app_hom, Category.assoc, he]
  exact point_evaluation k h.hom A.X

private theorem insertion_naturality (h : Spec (.of k) ≅ Spec (.of k))
    {M N : Modules Λ (Spec (.of k))} (t : M ⟶ N) :
    t.hom.hom.app (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) ≫ sectionInsertion Λ k h N =
      sectionInsertion Λ k h M ≫ ((CondensedRing.upperStar Λ h.hom).map t).hom.hom.app
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) := by
  have he := (geometricFieldEvaluationComparison h.hom Ab.{u + 1}).naturality t.hom
  have ht := (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ h.hom)).inv.naturality
    (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} h.hom).mapMod
      (condensedRingObj Λ (Spec (.of k)))).map t)
  have ht' := congrArg (fun w ↦ w.hom.hom.app
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) ht
  simp only [Mod.comp_hom', Mod.comap_map_hom,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at ht'
  change t.hom.hom.app _ ≫ (geometricFieldEvaluationComparison h.hom Ab).app N.X =
    (geometricFieldEvaluationComparison h.hom Ab).app M.X ≫
      ((AlgebraicGeometry.ProEtale.upperStar Ab h.hom).map t.hom).hom.app _ at he
  unfold sectionInsertion
  simp only [Iso.app_inv]
  rw [← Category.assoc, he, Category.assoc]
  change (geometricFieldEvaluationComparison h.hom Ab).app M.X ≫
    ((((AlgebraicGeometry.ProEtale.upperStar Ab h.hom).mapMod _).map t).hom.hom.app _ ≫ _) = _
  rw [ht']
  rfl

private def rawSections : Modules Λ (Spec (.of k)) ⥤ Ab.{u + 1} :=
  Mod.forget _ ⋙ sheafToPresheaf _ Ab.{u + 1} ⋙
    (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))

private def rawInsertion (h : Spec (.of k) ≅ Spec (.of k)) :
    rawSections Λ k ⟶ CondensedRing.upperStar Λ h.hom ⋙ rawSections Λ k where
  app := sectionInsertion Λ k h
  naturality _ _ t := insertion_naturality Λ k h t

private theorem sectionInsertion_eq (h : Spec (.of k) ≅ Spec (.of k))
    (M : Modules Λ (Spec (.of k))) :
    sectionInsertion Λ k h M =
      ((CondensedRing.upperStarIsoIdOfIsSepClosed Λ h.hom).inv.app M).hom.hom.app
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) := by
  let E := rawSections Λ k
  let τ := CondensedRing.upperStarIsoIdOfIsSepClosed Λ h.hom
  change sectionInsertion Λ k h M = E.map (τ.inv.app M)
  let θ : E ⟶ E := rawInsertion Λ k h ≫ Functor.whiskerRight τ.hom E
  have hA (A : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
      θ.app ((upperStarFromPointMod Λ (Spec (.of k))).obj A) = 𝟙 _ := by
    dsimp only [θ, E, rawInsertion, rawSections, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.comp_map, Mod.forget_map]
    rw [upperStarIsoIdOfIsSepClosed_hom_app_upperStarFromPointMod]
    exact insertion_on_point Λ k h A
  have hn := θ.naturality
    ((upperStarFromPointMod Λ (Spec (.of k))).objObjPreimageIso M).hom
  have hid : θ.app M = 𝟙 _ := by
    rw [hA, Category.id_comp] at hn
    exact (cancel_epi (E.map
      ((upperStarFromPointMod Λ (Spec (.of k))).objObjPreimageIso M).hom)).1
        (hn.trans (Category.comp_id _).symm)
  have hcomp : sectionInsertion Λ k h M ≫ E.map (τ.hom.app M) = 𝟙 (E.obj M) := by
    simpa only [θ, NatTrans.comp_app, rawInsertion, Functor.whiskerRight_app] using hid
  apply (cancel_mono (E.map (τ.hom.app M))).1
  rw [hcomp, ← E.map_comp, Iso.inv_hom_id_app, E.map_id]
  rfl

private theorem properExchange_isIso (a : Automorphism k c) :
    IsIso (properExchange Λ k c a) := by
  exact isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ c.obj.obj.g)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ c.obj.obj.g)
    ((CondensedRing.upperStar Λ a.onS.hom).mapDerivedCategory)
    ((CondensedRing.upperStar Λ a.onZ.hom).mapDerivedCategory)
    (properComparison Λ k c a)

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

/-- The left-adjoint mate before inversion, using D(j_!) adjoint to j^*.
Source: latest blueprint, ordinary condensed transport, definition of the open exchange
(blueprint: lem-zl-condensed-compactification-automorphism-transport). -/
def openMate (a : Automorphism k c) :
    (CondensedRing.upperStar Λ a.onX.hom).mapDerivedCategory ⋙
        (CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory ⟶
      (CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory ⋙
        (CondensedRing.upperStar Λ a.onZ.hom).mapDerivedCategory :=
  ((mateEquiv (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i)
    (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i)).symm
      (TwoSquare.mk _ _ _ _ (openComparison Λ k c a).hom)).natTrans

private theorem openMate_isIso (a : Automorphism k c) :
    IsIso (openMate Λ k c a) := by
  exact isIso_inverseMate_of_equivalences
    (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i)
    (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i)
    (openComparison Λ k c a)

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
    CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj ⋙
        (CondensedRing.upperStar Λ a.onS.hom).mapDerivedCategory ⟶
      (CondensedRing.upperStar Λ a.onX.hom).mapDerivedCategory ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (properExchange Λ k c a) ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight O.hom _ ≫
    (Functor.associator _ _ _).hom

private theorem exchange_isIso (a : Automorphism k c) (O : OpenExchange Λ k c a) :
    IsIso (exchange Λ k c a O) := by
  let := properExchange_isIso Λ k c a
  unfold exchange
  infer_instance

private theorem exactInsertion
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (V : C ⥤ D) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (τ : F ≅ 𝟭 C) (K : DerivedCategory C) :
    (Functor.mapDerivedCategoryNatTrans
        ((Functor.leftUnitor V).inv ≫ Functor.whiskerRight τ.inv V) ≫
      (Functor.mapDerivedCategoryCompIso F V).hom).app K =
    V.mapDerivedCategory.map
      ((Functor.mapDerivedCategoryNatIso τ ≪≫ Functor.mapDerivedCategoryIdIso C).inv.app K) := by
  have hn := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight τ V) K
  have hu := NatTrans.congr_app (Functor.mapDerivedCategoryCompIso_id_comp V) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hn hu
  have he : Functor.mapDerivedCategoryNatTrans
      ((Functor.leftUnitor V).inv ≫ Functor.whiskerRight τ.inv V) =
      (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight τ V)).inv := by
    have ht : (Functor.leftUnitor V).inv ≫ Functor.whiskerRight τ.inv V =
        Functor.whiskerRight τ.inv V := by ext X; simp
    rw [ht]
    change Functor.mapDerivedCategoryNatTrans (Functor.isoWhiskerRight τ V).inv = _
    simp only [Functor.mapDerivedCategoryNatTrans, Functor.mapDerivedCategoryNatIso,
      Localization.liftNatIso_inv]
    rfl
  rw [he, NatTrans.comp_app]
  apply (cancel_mono (V.mapDerivedCategory.map
    ((Functor.mapDerivedCategoryNatIso τ ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app K))).1
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, Iso.inv_hom_id_app_assoc, hu]
  simp only [← V.mapDerivedCategory.map_comp, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, V.mapDerivedCategory.map_id]
  rfl

private theorem inverse_trivialization_comp
    {C : Type*} [Category C] (P Q R : C ⥤ C)
    (c : R ≅ P ⋙ Q) (a : P ≅ 𝟭 C) (b : Q ≅ 𝟭 C) (d : R ≅ 𝟭 C)
    (h : ∀ K, c.hom.app K ≫ Q.map (a.hom.app K) ≫ b.hom.app K = d.hom.app K)
    (K : C) :
    d.inv.app K = a.inv.app K ≫ b.inv.app (P.obj K) ≫ c.inv.app K := by
  apply (cancel_mono (d.hom.app K)).1
  rw [← h K]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have hn := b.inv.naturality (a.hom.app K)
  change a.hom.app K ≫ b.inv.app K =
    b.inv.app (P.obj K) ≫ Q.map (a.hom.app K) at hn
  rw [← reassoc_of% hn, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rw [h, Iso.inv_hom_id_app]

private theorem point_trivialization_comp
    (f g : Spec (.of k) ⟶ Spec (.of k)) (K : DerivedCategory (Modules Λ (Spec (.of k)))) :
    (pullbackComp Λ f g).hom.app K ≫
        (CondensedRing.upperStar Λ f).mapDerivedCategory.map
          ((Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoIdOfIsSepClosed Λ g) ≪≫
            Functor.mapDerivedCategoryIdIso (Modules Λ (Spec (.of k)))).hom.app K) ≫
        (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoIdOfIsSepClosed Λ f) ≪≫
          Functor.mapDerivedCategoryIdIso (Modules Λ (Spec (.of k)))).hom.app K =
      (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoIdOfIsSepClosed Λ (f ≫ g)) ≪≫
        Functor.mapDerivedCategoryIdIso (Modules Λ (Spec (.of k)))).hom.app K := by
  have hd : CondensedRing.upperStarComp Λ f g ≪≫
      Functor.isoWhiskerRight (CondensedRing.upperStarIsoIdOfIsSepClosed Λ g)
        (CondensedRing.upperStar Λ f) ≪≫
      Functor.leftUnitor (CondensedRing.upperStar Λ f) ≪≫
        CondensedRing.upperStarIsoIdOfIsSepClosed Λ f =
        CondensedRing.upperStarIsoIdOfIsSepClosed Λ (f ≫ g) := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
    erw [Category.id_comp]
    exact sepClosedPointTrivialization_comp Λ f g N
  have h := exactTrivialization_comp _ _ _ (CondensedRing.upperStarComp Λ f g)
    (CondensedRing.upperStarIsoIdOfIsSepClosed Λ g) (CondensedRing.upperStarIsoIdOfIsSepClosed Λ f)
    (CondensedRing.upperStarIsoIdOfIsSepClosed Λ (f ≫ g)) hd K
  simpa only [pullbackComp, Iso.trans_hom, NatTrans.comp_app, Category.assoc] using h

private theorem transport_app (S : PointSections Λ k) (a : Automorphism k c)
    (O : OpenExchange Λ k c a) (K : DerivedCategory (Modules Λ X)) :
    (transport Λ k c S a O).app K =
      (S.derivedInsertion Λ k a.onS).app
          ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K) ≫
        (S.derived Λ k).map ((exchange Λ k c a O).app K) := by
  simp only [transport, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp, Category.comp_id]

private theorem transport_comp_of (S : PointSections Λ k)
    (O : ∀ a : Automorphism k c, OpenExchange Λ k c a)
    (a b : Automorphism k c)
    (hi : ∀ N,
      (S.derivedInsertion Λ k (a.onS ≪≫ b.onS)).app N =
        (S.derivedInsertion Λ k b.onS).app N ≫
          (S.derivedInsertion Λ k a.onS).app
            ((CondensedRing.upperStar Λ b.onS.hom).mapDerivedCategory.obj N) ≫
          (S.derived Λ k).map ((pullbackComp Λ a.onS.hom b.onS.hom).inv.app N))
    (he : ∀ K,
      (CondensedRing.upperStar Λ a.onS.hom).mapDerivedCategory.map
          ((exchange Λ k c b (O b)).app K) ≫
        (exchange Λ k c a (O a)).app
          ((CondensedRing.upperStar Λ b.onX.hom).mapDerivedCategory.obj K) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj).map
          ((pullbackComp Λ a.onX.hom b.onX.hom).inv.app K) =
      (pullbackComp Λ a.onS.hom b.onS.hom).inv.app
          ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K) ≫
        (exchange Λ k c (Automorphism.then k c a b)
          (O (Automorphism.then k c a b))).app K)
    (K : DerivedCategory (Modules Λ X)) :
    (transport Λ k c S (Automorphism.then k c a b)
      (O (Automorphism.then k c a b))).app K =
      (transport Λ k c S b (O b)).app K ≫
        (transport Λ k c S a (O a)).app
          ((CondensedRing.upperStar Λ b.onX.hom).mapDerivedCategory.obj K) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj ⋙ S.derived Λ k).map
          ((pullbackComp Λ a.onX.hom b.onX.hom).inv.app K) := by
  let C := CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj
  let V := S.derived Λ k
  let ia := S.derivedInsertion Λ k a.onS
  let ib := S.derivedInsertion Λ k b.onS
  let ea := exchange Λ k c a (O a)
  let eb := exchange Λ k c b (O b)
  have hn := ia.naturality (eb.app K)
  change V.map (eb.app K) ≫ ia.app (C.obj
      ((CondensedRing.upperStar Λ b.onX.hom).mapDerivedCategory.obj K)) =
    ia.app ((CondensedRing.upperStar Λ b.onS.hom).mapDerivedCategory.obj (C.obj K)) ≫
      V.map ((CondensedRing.upperStar Λ a.onS.hom).mapDerivedCategory.map (eb.app K)) at hn
  simp only [transport_app, Category.assoc]
  change (S.derivedInsertion Λ k (a.onS ≪≫ b.onS)).app (C.obj K) ≫ _ =
    ib.app (C.obj K) ≫ (V.map (eb.app K) ≫
      ia.app (C.obj ((CondensedRing.upperStar Λ b.onX.hom).mapDerivedCategory.obj K)) ≫
      V.map (ea.app ((CondensedRing.upperStar Λ b.onX.hom).mapDerivedCategory.obj K)) ≫
      V.map (C.map ((pullbackComp Λ a.onX.hom b.onX.hom).inv.app K)))
  rw [hi]
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  simp only [← V.map_comp]
  rw [he K]
  simp only [Functor.map_comp]
  rfl

private theorem pullback_id_comp (T : Scheme.{u})
    (K : DerivedCategory (Modules Λ T)) :
    (pullbackComp Λ (𝟙 T) (𝟙 T)).hom.app K ≫
      (CondensedRing.upperStar Λ (𝟙 T)).mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ T) ≪≫
          Functor.mapDerivedCategoryIdIso (Modules Λ T)).hom.app K) =
      eqToHom (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).mapDerivedCategory.obj K)
        (Category.id_comp (𝟙 T))) := by
  let F := CondensedRing.upperStar Λ (𝟙 T)
  let a := CondensedRing.upperStarId Λ T
  let d := CondensedRing.upperStarCongr Λ (Category.id_comp (𝟙 T)) ≪≫ a
  have hd : CondensedRing.upperStarComp Λ (𝟙 T) (𝟙 T) ≪≫
      Functor.isoWhiskerRight a F ≪≫ Functor.leftUnitor F ≪≫ a = d := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    dsimp only [d, F, a]
    simp only [CondensedRing.upperStarComp_id_left, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatTrans.comp_app, Functor.rightUnitor_inv_app,
      Functor.leftUnitor_hom_app, Category.assoc, Category.id_comp]
    rw [← reassoc_of% (CondensedRing.upperStarId Λ T).inv.naturality
      ((CondensedRing.upperStarId Λ T).hom.app M)]
    simp only [Iso.hom_inv_id_app_assoc]
    erw [Category.id_comp ((CondensedRing.upperStarId Λ T).hom.app M)]
  have h := exactTrivialization_comp F F (CondensedRing.upperStar Λ (𝟙 T ≫ 𝟙 T))
    (CondensedRing.upperStarComp Λ (𝟙 T) (𝟙 T)) a a d hd K
  simp only [d, Functor.mapDerivedCategoryNatIso_trans, CondensedRing.upperStarCongr,
    derived_iso_eqToIso, eqToIso.hom, NatTrans.comp_app, Category.assoc] at h
  apply (cancel_mono ((Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ T) ≪≫
    Functor.mapDerivedCategoryIdIso (Modules Λ T)).hom.app K)).1
  simpa only [F, a, pullbackComp, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc, eqToHom_app] using h

private theorem invertible_idempotent_transport
    {C D : Type*} [Category C] [Category D] (T : C ⥤ D) (P : C ⥤ C)
    (u : P ≅ 𝟭 C) (τ : T ⟶ P ⋙ T) [IsIso τ]
    (h : ∀ K, τ.app K = τ.app K ≫ τ.app (P.obj K) ≫ T.map (P.map (u.hom.app K)))
    (K : C) : τ.app K ≫ T.map (u.hom.app K) = 𝟙 _ := by
  have hc : τ.app (P.obj K) ≫ T.map (P.map (u.hom.app K)) = 𝟙 _ := by
    apply (cancel_epi (τ.app K)).1
    erw [Category.comp_id]
    exact (h K).symm
  have hn := τ.naturality (u.hom.app K)
  change T.map (u.hom.app K) ≫ τ.app K =
    τ.app (P.obj K) ≫ T.map (P.map (u.hom.app K)) at hn
  apply (cancel_mono (τ.app K)).1
  rw [Category.assoc, hn, hc]
  erw [Category.comp_id, Category.id_comp]

private theorem family_congr {D : Type*} [Category D]
    (T : DerivedCategory (Modules Λ X) ⥤ D)
    (τ : ∀ a : Automorphism k c,
      T ⟶ (CondensedRing.upperStar Λ a.onX.hom).mapDerivedCategory ⋙ T)
    {a b : Automorphism k c} (h : a = b) (K : DerivedCategory (Modules Λ X)) :
    (τ a).app K ≫ T.map (eqToHom (congrArg
      (fun a : Automorphism k c ↦
        (CondensedRing.upperStar Λ a.onX.hom).mapDerivedCategory.obj K) h)) =
      (τ b).app K := by
  subst h
  simp

private theorem family_identity {D : Type*} [Category D]
    (T : DerivedCategory (Modules Λ X) ⥤ D)
    (τ : ∀ a : Automorphism k c,
      T ⟶ (CondensedRing.upperStar Λ a.onX.hom).mapDerivedCategory ⋙ T)
    [∀ a, IsIso (τ a)]
    (hcomp : ∀ a b K, (τ (Automorphism.then k c a b)).app K =
      (τ b).app K ≫ (τ a).app
        ((CondensedRing.upperStar Λ b.onX.hom).mapDerivedCategory.obj K) ≫
      T.map ((pullbackComp Λ a.onX.hom b.onX.hom).inv.app K))
    (K : DerivedCategory (Modules Λ X)) :
    (τ (Automorphism.identity k c)).app K ≫ T.map
      ((Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ X) ≪≫
        Functor.mapDerivedCategoryIdIso (Modules Λ X)).hom.app K) = 𝟙 _ := by
  let a := Automorphism.identity k c
  let P : DerivedCategory (Modules Λ X) ⥤ DerivedCategory (Modules Λ X) :=
    (CondensedRing.upperStar Λ (𝟙 X)).mapDerivedCategory
  let u : P ≅ 𝟭 (DerivedCategory (Modules Λ X)) :=
    Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ X) ≪≫
    Functor.mapDerivedCategoryIdIso (Modules Λ X)
  have haa : Automorphism.then k c a a = a := by
    simp only [a, Automorphism.then, Automorphism.identity, Iso.refl_trans]
  apply invertible_idempotent_transport T P u (τ a) (fun L ↦ ?_) K
  let h := congrArg (fun f ↦ (CondensedRing.upperStar Λ f).mapDerivedCategory.obj L)
    (Category.id_comp (𝟙 X))
  have hu : (pullbackComp Λ (𝟙 X) (𝟙 X)).inv.app L ≫ eqToHom h =
      P.map (u.hom.app L) := by
    apply (cancel_epi ((pullbackComp Λ (𝟙 X) (𝟙 X)).hom.app L)).1
    rw [Iso.hom_inv_id_app_assoc]
    exact (pullback_id_comp Λ X L).symm
  have ht := congrArg (fun m ↦ m ≫ T.map (eqToHom h)) (hcomp a a L)
  simp only [Category.assoc] at ht
  change (τ (Automorphism.then k c a a)).app L ≫ T.map (eqToHom h) =
    (τ a).app L ≫ (τ a).app (P.obj L) ≫
      T.map ((pullbackComp Λ (𝟙 X) (𝟙 X)).inv.app L) ≫ T.map (eqToHom h) at ht
  rw [← T.map_comp, hu] at ht
  have he := family_congr Λ k c T τ haa L
  change (τ (Automorphism.then k c a a)).app L ≫ T.map (eqToHom h) = (τ a).app L at he
  rw [he] at ht
  exact ht

private theorem properExchange_eq_exact
    (hnorm : ∀ a : Automorphism k c, properComparison Λ k c a =
      Functor.isoWhiskerLeft _
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.g) ≪≫
      (exactSquare Λ (CommSq.mk a.proper_comm)).symm ≪≫
      Functor.isoWhiskerRight
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.g).symm _)
    (a : Automorphism k c) :
    properExchange Λ k c a =
      (mateEquiv
        ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ c.obj.obj.g).ofNatIsoLeft
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.g))
        ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ c.obj.obj.g).ofNatIsoLeft
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.g))
        (TwoSquare.mk _ _ _ _ (exactSquare Λ (CommSq.mk a.proper_comm)).inv)).natTrans := by
  rw [mate_ofNatIsoLeft]
  unfold properExchange
  congr 2
  ext K
  simp only [hnorm, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, Category.assoc]

private theorem properExchange_comp
    (hnorm : ∀ a : Automorphism k c, properComparison Λ k c a =
      Functor.isoWhiskerLeft _
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.g) ≪≫
      (exactSquare Λ (CommSq.mk a.proper_comm)).symm ≪≫
      Functor.isoWhiskerRight
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.g).symm _)
    (a b : Automorphism k c) (N : DerivedCategory (Modules Λ c.obj.obj.Z)) :
    (properExchange Λ k c (Automorphism.then k c a b)).app N =
      (pullbackComp Λ a.onS.hom b.onS.hom).hom.app
        ((CondensedRing.lowerStar Λ c.obj.obj.g).rightDerivedFunctor.obj N) ≫
      (CondensedRing.upperStar Λ a.onS.hom).mapDerivedCategory.map
        ((properExchange Λ k c b).app N) ≫
      (properExchange Λ k c a).app
        ((CondensedRing.upperStar Λ b.onZ.hom).mapDerivedCategory.obj N) ≫
      (CondensedRing.lowerStar Λ c.obj.obj.g).rightDerivedFunctor.map
        ((pullbackComp Λ a.onZ.hom b.onZ.hom).inv.app N) := by
  let adj := (CondensedRing.derivedUpperStarLowerStarAdjunction Λ c.obj.obj.g).ofNatIsoLeft
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.g)
  have h := exactSquare_horiz_inv Λ (CommSq.mk b.proper_comm) (CommSq.mk a.proper_comm)
  have hcomp {T U V : Scheme.{u}} (f : T ⟶ U) (g : U ⟶ V) :
      exactComp Λ f g (f ≫ g) rfl = pullbackComp Λ f g := by
    simp only [exactComp, ordinaryComp, eqToIso_refl, Iso.refl_trans]
    rfl
  rw [hcomp, hcomp] at h
  have hh : TwoSquare.mk _ _ _ _
      (exactSquare Λ (CommSq.mk (Automorphism.then k c a b).proper_comm)).inv =
      (((TwoSquare.mk _ _ _ _ (exactSquare Λ (CommSq.mk b.proper_comm)).inv ≫ₕ
        TwoSquare.mk _ _ _ _ (exactSquare Λ (CommSq.mk a.proper_comm)).inv).whiskerTop
          (pullbackComp Λ a.onS.hom b.onS.hom).hom).whiskerBottom
            (pullbackComp Λ a.onZ.hom b.onZ.hom).inv) := by
    exact congrArg (TwoSquare.mk _ _ _ _) h
  have hm := congrArg (mateEquiv adj adj) hh
  rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp _ adj] at hm
  have ht := congrArg (fun s ↦ s.natTrans.app N) hm
  simp only [properExchange_eq_exact Λ k c hnorm]
  simpa only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using ht

private theorem exactComp_pullback {T U V : Scheme.{u}} (f : T ⟶ U) (g : U ⟶ V) :
    exactComp Λ f g (f ≫ g) rfl = pullbackComp Λ f g := by
  simp only [exactComp, ordinaryComp, eqToIso_refl, Iso.refl_trans]
  rfl

private theorem exactSquare_open (a : Automorphism k c) :
    exactSquare Λ (CommSq.mk a.open_comm) = openComparison Λ k c a := by
  apply Iso.ext
  simp only [exactSquare, exactComp, ordinaryComp, Functor.mapDerivedCategoryTriangleIso,
    derived_iso_trans, derived_iso_eqToIso, eqToIso_refl,
    Iso.refl_trans, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Category.assoc, eqToIso.hom, openComparison, pullbackComp]

private theorem openComparison_comp (a b : Automorphism k c)
    (N : DerivedCategory (Modules Λ c.obj.obj.Z)) :
    (openComparison Λ k c (Automorphism.then k c a b)).hom.app N =
      (pullbackComp Λ a.onX.hom b.onX.hom).hom.app
          ((CondensedRing.upperStar Λ c.obj.obj.i).mapDerivedCategory.obj N) ≫
        (CondensedRing.upperStar Λ a.onX.hom).mapDerivedCategory.map
          ((openComparison Λ k c b).hom.app N) ≫
        (openComparison Λ k c a).hom.app
          ((CondensedRing.upperStar Λ b.onZ.hom).mapDerivedCategory.obj N) ≫
        (CondensedRing.upperStar Λ c.obj.obj.i).mapDerivedCategory.map
          ((pullbackComp Λ a.onZ.hom b.onZ.hom).inv.app N) := by
  have h := exactSquare_horiz Λ (CommSq.mk b.open_comm) (CommSq.mk a.open_comm) N
  rw [exactComp_pullback, exactComp_pullback] at h
  change (exactSquare Λ (CommSq.mk (Automorphism.then k c a b).open_comm)).hom.app N = _ at h
  simpa only [exactSquare_open] using h

private theorem total_congr {T U : Scheme.{u}} (f g : T ⟶ U) (h : f = g) :
    eqToIso (congrArg (fun h ↦ (CondensedRing.upperStar Λ h).leftDerivedFunctor) h) =
      (CondensedRing.upperStar Λ f).leftDerivedFunctorNatIso
        (eqToIso (congrArg (CondensedRing.upperStar Λ) h)) := by
  subst h
  apply Iso.ext
  simp [Functor.leftDerivedFunctorNatIso, Functor.mapDerivedCategoryNatIso_refl]

private theorem properComparison_exact (a : Automorphism k c) :
    properComparison Λ k c a =
      Functor.isoWhiskerLeft _
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.g) ≪≫
      ((pullbackComp Λ c.obj.obj.g a.onS.hom).symm ≪≫
        eqToIso (congrArg (fun h ↦ (CondensedRing.upperStar Λ h).mapDerivedCategory)
          a.proper_comm.symm) ≪≫ pullbackComp Λ a.onZ.hom c.obj.obj.g) ≪≫
      Functor.isoWhiskerRight
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.g).symm _ := by
  rw [properComparison, total_congr Λ _ _ a.proper_comm.symm]
  have h := normalize_square
    (C := DerivedCategory (Modules Λ (Spec (.of k))))
    (D := DerivedCategory (Modules Λ c.obj.obj.Z))
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ a.onS.hom)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.g)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ a.onZ.hom)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (c.obj.obj.g ≫ a.onS.hom))
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (a.onZ.hom ≫ c.obj.obj.g))
    (pullbackComp Λ c.obj.obj.g a.onS.hom)
    (pullbackComp Λ a.onZ.hom c.obj.obj.g)
    (eqToIso (congrArg (fun t ↦ (CondensedRing.upperStar Λ t).mapDerivedCategory)
      a.proper_comm.symm))
  simpa only [CondensedRing.leftDerivedUpperStarComp,
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso, pullbackComp,
    Iso.trans_assoc, Iso.trans_symm, Iso.symm_symm_eq, Iso.symm_self_id_assoc,
    Iso.self_symm_id_assoc, Iso.refl_trans, Iso.trans_refl, derived_iso_eqToIso] using h

private theorem openMate_comp (a b : Automorphism k c) :
    openMate Λ k c (Automorphism.then k c a b) =
      ((((TwoSquare.mk _ _ _ _ (openMate Λ k c b)) ≫ₕ
        (TwoSquare.mk _ _ _ _ (openMate Λ k c a))).whiskerTop
          (pullbackComp Λ a.onX.hom b.onX.hom).hom).whiskerBottom
            (pullbackComp Λ a.onZ.hom b.onZ.hom).inv).natTrans := by
  let adj := CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i
  apply congrArg TwoSquare.natTrans
  apply (mateEquiv adj adj).injective
  have hm (t : Automorphism k c) :
      mateEquiv adj adj (TwoSquare.mk _ _ _ _ (openMate Λ k c t)) =
        TwoSquare.mk _ _ _ _ (openComparison Λ k c t).hom :=
    (mateEquiv adj adj).apply_symm_apply _
  rw [hm, mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp _ adj, hm, hm]
  ext N
  simpa only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using openComparison_comp Λ k c a b N

private theorem properComparison_square (a : Automorphism k c) :
    properComparison Λ k c a =
      Functor.isoWhiskerLeft _
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.g) ≪≫
      (exactSquare Λ (CommSq.mk a.proper_comm)).symm ≪≫
      Functor.isoWhiskerRight
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.g).symm _ := by
  have hs : (exactSquare Λ (CommSq.mk a.proper_comm)).symm =
      (pullbackComp Λ c.obj.obj.g a.onS.hom).symm ≪≫
        eqToIso (congrArg (fun h ↦ (CondensedRing.upperStar Λ h).mapDerivedCategory)
          a.proper_comm.symm) ≪≫ pullbackComp Λ a.onZ.hom c.obj.obj.g := by
    apply Iso.ext
    simp only [exactSquare, exactComp, ordinaryComp,
      Functor.mapDerivedCategoryTriangleIso, pullbackComp,
      derived_iso_trans, derived_iso_eqToIso,
      eqToIso_refl, Iso.refl_trans, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Category.assoc, eqToIso.hom, eqToIso.inv]
  rw [hs]
  exact properComparison_exact Λ k c a

private theorem invert_open_comp
    (O : ∀ a : Automorphism k c, OpenExchange Λ k c a) (a b : Automorphism k c)
    (h : ∀ K, (O (Automorphism.then k c a b)).inv.app K =
      (CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.map
        ((pullbackComp Λ a.onX.hom b.onX.hom).hom.app K) ≫
      (O a).inv.app ((CondensedRing.upperStar Λ b.onX.hom).mapDerivedCategory.obj K) ≫
      (CondensedRing.upperStar Λ a.onZ.hom).mapDerivedCategory.map ((O b).inv.app K) ≫
      (pullbackComp Λ a.onZ.hom b.onZ.hom).inv.app
        ((CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj K))
    (K : DerivedCategory (Modules Λ X)) :
    (O (Automorphism.then k c a b)).hom.app K =
      (pullbackComp Λ a.onZ.hom b.onZ.hom).hom.app
        ((CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj K) ≫
      (CondensedRing.upperStar Λ a.onZ.hom).mapDerivedCategory.map ((O b).hom.app K) ≫
      (O a).hom.app ((CondensedRing.upperStar Λ b.onX.hom).mapDerivedCategory.obj K) ≫
      (CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.map
        ((pullbackComp Λ a.onX.hom b.onX.hom).inv.app K) := by
  exact inverse_exchange_comp
    (C := DerivedCategory (Modules Λ X))
    (D := DerivedCategory (Modules Λ c.obj.obj.Z))
    (CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory
    (pullbackComp Λ a.onX.hom b.onX.hom) (pullbackComp Λ a.onZ.hom b.onZ.hom)
    (O a) (O b) (O (Automorphism.then k c a b)) h K

private theorem exchange_eq_joined (a : Automorphism k c) (O : OpenExchange Λ k c a) :
    exchange Λ k c a O =
      joinedExchange
        (CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory
        (CondensedRing.lowerStar Λ c.obj.obj.g).rightDerivedFunctor
        (CondensedRing.upperStar Λ a.onX.hom).mapDerivedCategory
        (CondensedRing.upperStar Λ a.onZ.hom).mapDerivedCategory
        (CondensedRing.upperStar Λ a.onS.hom).mapDerivedCategory
        (properExchange Λ k c a) O.hom := by
  rfl

private theorem exchange_comp_of_mates
    (O : ∀ a : Automorphism k c, OpenExchange Λ k c a) (a b : Automorphism k c)
    (he : ∀ N, (properExchange Λ k c (Automorphism.then k c a b)).app N =
      (pullbackComp Λ a.onS.hom b.onS.hom).hom.app
        ((CondensedRing.lowerStar Λ c.obj.obj.g).rightDerivedFunctor.obj N) ≫
      (CondensedRing.upperStar Λ a.onS.hom).mapDerivedCategory.map
        ((properExchange Λ k c b).app N) ≫
      (properExchange Λ k c a).app
        ((CondensedRing.upperStar Λ b.onZ.hom).mapDerivedCategory.obj N) ≫
      (CondensedRing.lowerStar Λ c.obj.obj.g).rightDerivedFunctor.map
        ((pullbackComp Λ a.onZ.hom b.onZ.hom).inv.app N))
    (hb : ∀ K, (O (Automorphism.then k c a b)).inv.app K =
      (CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.map
        ((pullbackComp Λ a.onX.hom b.onX.hom).hom.app K) ≫
      (O a).inv.app ((CondensedRing.upperStar Λ b.onX.hom).mapDerivedCategory.obj K) ≫
      (CondensedRing.upperStar Λ a.onZ.hom).mapDerivedCategory.map ((O b).inv.app K) ≫
      (pullbackComp Λ a.onZ.hom b.onZ.hom).inv.app
        ((CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj K))
    (K : DerivedCategory (Modules Λ X)) :
    (CondensedRing.upperStar Λ a.onS.hom).mapDerivedCategory.map
        ((exchange Λ k c b (O b)).app K) ≫
      (exchange Λ k c a (O a)).app
        ((CondensedRing.upperStar Λ b.onX.hom).mapDerivedCategory.obj K) ≫
      (CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj).map
        ((pullbackComp Λ a.onX.hom b.onX.hom).inv.app K) =
    (pullbackComp Λ a.onS.hom b.onS.hom).inv.app
        ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K) ≫
      (exchange Λ k c (Automorphism.then k c a b)
        (O (Automorphism.then k c a b))).app K := by
  have h := joinedExchange_comp
    (CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ c.obj.obj.g).rightDerivedFunctor
    (CondensedRing.upperStar Λ b.onX.hom).mapDerivedCategory
    (CondensedRing.upperStar Λ a.onX.hom).mapDerivedCategory
    (CondensedRing.upperStar Λ (Automorphism.then k c a b).onX.hom).mapDerivedCategory
    (CondensedRing.upperStar Λ b.onZ.hom).mapDerivedCategory
    (CondensedRing.upperStar Λ a.onZ.hom).mapDerivedCategory
    (CondensedRing.upperStar Λ (Automorphism.then k c a b).onZ.hom).mapDerivedCategory
    (CondensedRing.upperStar Λ b.onS.hom).mapDerivedCategory
    (CondensedRing.upperStar Λ a.onS.hom).mapDerivedCategory
    (CondensedRing.upperStar Λ (Automorphism.then k c a b).onS.hom).mapDerivedCategory
    (pullbackComp Λ a.onX.hom b.onX.hom)
    (pullbackComp Λ a.onZ.hom b.onZ.hom)
    (pullbackComp Λ a.onS.hom b.onS.hom)
    (properExchange Λ k c b) (properExchange Λ k c a)
    (properExchange Λ k c (Automorphism.then k c a b))
    (O b).hom (O a).hom (O (Automorphism.then k c a b)).hom
    he (invert_open_comp Λ k c O a b hb) K
  have ht := iso_inv_comp_eq
    ((pullbackComp Λ a.onS.hom b.onS.hom).app
      (((CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory ⋙
        (CondensedRing.lowerStar Λ c.obj.obj.g).rightDerivedFunctor).obj K)) h
  simpa -implicitDefEqProofs only [exchange_eq_joined,
    CondensedRing.rightDerivedLowerShriekOfCompactification,
    Functor.comp_obj, Functor.comp_map, Iso.app_inv] using ht.symm

end AlgebraicGeometry.ProEtale.CondensedCompactificationTransport
