/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import Sheaf.CategoryTheory.DerivedInjectiveBoundary
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction

/-!
# The long exact sequence of cohomology with support

Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.4;
Stacks Project, Tags 093X, 03F3, 0117, 070I
(blueprint: thm-pur-with-support-exactness).
-/

@[expose] public section

set_option autoImplicit false

universe c v a w u d e

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
variable (A : Type a) [Category.{w} A] [Abelian A]
variable {V W : C} (j : W ⟶ V)

/-- Inclusion of the kernel of restriction into sections on `V`.
Source: Milne, Section 9, definition before Theorem 9.4
(blueprint: thm-pur-with-support-exactness). -/
noncomputable def supportedSectionsInclusion :
    supportedSectionsFunctor J A j ⟶ (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V)) where
  app F := kernel.ι (F.obj.map j.op)
  naturality f := by simp [supportedSectionsFunctor]

variable [HasSheafify J A]
variable [EnoughInjectives (Sheaf J A)] [HasDerivedCategory (Sheaf J A)]
variable [HasDerivedCategory A]

/-- Derived evaluation on an object of a site, followed by integer-indexed cohomology.
For a terminal object this is global hypercohomology; for the open object it is
hypercohomology of the localized site. Source: Stacks, Tag 03F3
(blueprint: thm-pur-with-support-exactness). -/
noncomputable abbrev sectionHypercohomologyFunctor (V : C) (q : ℤ) :
    DerivedCategory.Plus (Sheaf J A) ⥤ A :=
  (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V)).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor A q

/-- Derived supported sections followed by cohomology: this specializes exactly to
`Etale.supportHypercohomology` and `ProEtale.supportHypercohomology`.
Source: the support definition and Milne, Section 9, Theorem 9.4
(blueprint: thm-pur-with-support-exactness). -/
noncomputable abbrev supportHypercohomologyFunctor (q : ℤ) :
    DerivedCategory.Plus (Sheaf J A) ⥤ A :=
  (supportedSectionsFunctor J A j).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor A q

/-- The canonical first arrow in the support sequence, obtained by deriving kernel inclusion.
Source: Milne, Section 9, Theorem 9.4 (blueprint: thm-pur-with-support-exactness). -/
noncomputable def supportHypercohomologyInclusion (q : ℤ) :
    supportHypercohomologyFunctor J A j q ⟶ sectionHypercohomologyFunctor J A V q :=
  Functor.whiskerRight (Functor.rightDerivedFunctorPlusNatTrans
    (supportedSectionsInclusion J A j)) (DerivedCategory.Plus.homologyFunctor A q)

/-- The canonical second arrow in the support sequence, obtained by deriving restriction.
Source: Milne, Section 9, Theorem 9.4 (blueprint: thm-pur-with-support-exactness). -/
noncomputable def sectionHypercohomologyRestriction (q : ℤ) :
    sectionHypercohomologyFunctor J A V q ⟶ sectionHypercohomologyFunctor J A W q :=
  Functor.whiskerRight (Functor.rightDerivedFunctorPlusNatTrans
    (F := sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V))
    (G := sheafToPresheaf J A ⋙ (evaluation _ _).obj (op W))
    ((sheafSections J A).map j.op)) (DerivedCategory.Plus.homologyFunctor A q)

/-- The canonical cohomology comparison from a bounded-below injective representative,
including its specified identification with the derived object. Source: Stacks, Tags 05TI,
05TH and 070I (blueprint: thm-pur-with-support-exactness). -/
noncomputable def supportSequenceModelIso (E : Sheaf J A ⥤ A) [E.Additive]
    (I : CochainComplex.Plus (Sheaf J A)) [∀ n : ℤ, Injective (I.obj.X n)]
    (K : DerivedCategory.Plus (Sheaf J A)) (e : DerivedCategory.Plus.Q.obj I ≅ K)
    (q : ℤ) :
    ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q).obj
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj)) ≅
      (E.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A q).obj K :=
  (DerivedCategory.Plus.homologyFunctorObjQIso
    (E.mapCochainComplexPlus.obj I) q).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor A q).mapIso
      (asIso (E.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient _).obj I))) ≪≫
    (E.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A q).mapIso e

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
variable (A : Type a) [Category.{w} A] [Abelian A] [HasSheafify J A]
variable [EnoughInjectives (Sheaf J A)] [HasDerivedCategory (Sheaf J A)]
variable [HasDerivedCategory A] {V W : C} (j : W ⟶ V)
variable (P : ObjectProperty (DerivedCategory.Plus (Sheaf J A)))

/-- A family of boundary maps natural in the permitted derived coefficients.
Source: Milne, Section 9, Theorem 9.4 (blueprint: thm-pur-with-support-exactness). -/
abbrev SupportSequenceBoundary :=
  ∀ q : ℤ, P.ι ⋙ sectionHypercohomologyFunctor J A W q ⟶
    P.ι ⋙ supportHypercohomologyFunctor J A j (q + 1)

/-- Exactness at all three places, in all integer degrees, of the displayed sequence.
The other two maps are the derived kernel inclusion and restriction, not existential maps.
Source: Milne, Section 9, Theorem 9.4 (blueprint: thm-pur-with-support-exactness). -/
def SupportSequenceExact (δ : SupportSequenceBoundary J A j P) : Prop :=
  ∀ (K : P.FullSubcategory) (q : ℤ),
    ∃ (w₁ : (supportHypercohomologyInclusion J A j q).app K.obj ≫
        (sectionHypercohomologyRestriction J A j q).app K.obj = 0)
      (w₂ : (sectionHypercohomologyRestriction J A j q).app K.obj ≫ (δ q).app K = 0)
      (w₃ : (δ q).app K ≫ (supportHypercohomologyInclusion J A j (q + 1)).app K.obj = 0),
      (ShortComplex.mk _ _ w₁).Exact ∧ (ShortComplex.mk _ _ w₂).Exact ∧
        (ShortComplex.mk _ _ w₃).Exact

/-- The boundary on a specified injective representative, transported by the canonical
right-derived-functor unit. Source: Stacks, Tags 05TI, 05TH, 0117
(blueprint: thm-pur-with-support-exactness). -/
noncomputable def supportSequenceModelBoundary (δ : SupportSequenceBoundary J A j P)
    (I : CochainComplex.Plus (Sheaf J A)) [∀ n : ℤ, Injective (I.obj.X n)]
    (K : P.FullSubcategory) (e : DerivedCategory.Plus.Q.obj I ≅ K.obj) (q : ℤ) :
    ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q).obj
      (((sheafToPresheaf J A ⋙ (evaluation _ _).obj (op W)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.obj)) ⟶
    ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) (q + 1)).obj
      (((supportedSectionsFunctor J A j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.obj)) :=
  (supportSequenceModelIso J A
    (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op W)) I K.obj e q).hom ≫
    (δ q).app K ≫
    (supportSequenceModelIso J A (supportedSectionsFunctor J A j) I K.obj e (q + 1)).inv

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf

variable {C D : Type c} [Category.{v} C] [Category.{v} D]
variable (J : GrothendieckTopology C) (J' : GrothendieckTopology D)
variable (A : Type a) [Category.{w} A] [Abelian A]
variable (B : C ⥤ D) [hB : B.IsContinuous J J']

/-- Continuous pushforward acts by precomposition and is additive by definition.
Source: blueprint proof Step 7 (blueprint: thm-pur-with-support-exactness). -/
instance supportSequencePushforward_additive :
    (B.sheafPushforwardContinuous A J J').Additive where

/-- The chain map on sections induced by an adjoint coefficient chain map `b` and
restriction from `B(V)` to `V'`. For base change on scheme sites, this is precisely
`I(V) → L(V ×_X X') → L(V')` in the proof of pair functoriality.
Source: Milne, Section 9, Theorem 9.4; blueprint proof Step 7
(blueprint: thm-pur-with-support-exactness). -/
noncomputable def supportPairComplexSectionMap
    (I : CochainComplex.Plus (Sheaf J A)) (L : CochainComplex.Plus (Sheaf J' A))
    (b : I.obj ⟶ ((B.sheafPushforwardContinuous A J J').mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L.obj)
    {V : C} {V' : D} (t : V' ⟶ B.obj V) :
    (((sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I.obj) ⟶
    (((sheafToPresheaf J' A ⋙ (evaluation _ _).obj (op V')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L.obj) :=
  ((sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map b ≫
    (NatTrans.mapHomologicalComplex ((sheafSections J' A).map t.op)
      (ComplexShape.up ℤ)).app L.obj

variable [HasSheafify J A] [HasSheafify J' A]
variable [EnoughInjectives (Sheaf J A)] [EnoughInjectives (Sheaf J' A)]
variable [HasDerivedCategory (Sheaf J A)] [HasDerivedCategory (Sheaf J' A)]
variable [HasDerivedCategory A] {V W : C} (j : W ⟶ V) {V' W' : D} (j' : W' ⟶ V')
variable (P : ObjectProperty (DerivedCategory.Plus (Sheaf J A)))
variable (P' : ObjectProperty (DerivedCategory.Plus (Sheaf J' A)))

/-- Pair functoriality on injective representatives, with no choice of support map:
that map is uniquely determined by its kernel-inclusion square. The section maps are
explicitly those of the adjoint chain map, followed by restriction. All representatives
and their identifications with derived coefficients are quantified; thus this also gives
independence of representatives. Identity and composition follow from those of the chain
maps and their homology maps. Source: blueprint proof Steps 6-8; Milne, Section 9,
Theorem 9.4; Stacks, Tags 070I and 0117 (blueprint: thm-pur-with-support-exactness). -/
def SupportSequencePairNatural
    (δ : SupportSequenceBoundary J A j P) (δ' : SupportSequenceBoundary J' A j' P')
    (t : V' ⟶ B.obj V) (s : W' ⟶ B.obj W) : Prop :=
  ∀ (I : CochainComplex.Plus (Sheaf J A)) (L : CochainComplex.Plus (Sheaf J' A))
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (L.obj.X n)]
    (K : P.FullSubcategory) (K' : P'.FullSubcategory)
    (e : DerivedCategory.Plus.Q.obj I ≅ K.obj)
    (e' : DerivedCategory.Plus.Q.obj L ≅ K'.obj)
    (b : I.obj ⟶ ((B.sheafPushforwardContinuous A J J').mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L.obj),
    ∃! z : (((supportedSectionsFunctor J A j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.obj) ⟶
      (((supportedSectionsFunctor J' A j').mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L.obj),
      z ≫ (NatTrans.mapHomologicalComplex (supportedSectionsInclusion J' A j')
          (ComplexShape.up ℤ)).app L.obj =
        (NatTrans.mapHomologicalComplex (supportedSectionsInclusion J A j)
          (ComplexShape.up ℤ)).app I.obj ≫ supportPairComplexSectionMap J J' A B I L b t ∧
      ∀ q : ℤ,
        supportSequenceModelBoundary J A j P δ I K e q ≫
          (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) (q + 1)).map z =
        (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q).map
          (supportPairComplexSectionMap J J' A B I L b s) ≫
            supportSequenceModelBoundary J' A j' P' δ' L K' e' q

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
variable (A : Type a) [Category.{w} A] [Abelian A] [HasSheafify J A]
variable [EnoughInjectives (Sheaf J A)] [HasDerivedCategory.{d} (Sheaf J A)]
variable [HasDerivedCategory.{e} A] {V W : C} (j : W ⟶ V)

omit [HasSheafify J A] [EnoughInjectives (Sheaf J A)]
  [HasDerivedCategory.{d} (Sheaf J A)] [HasDerivedCategory.{e} A] in
private theorem supportRow_zero :
    supportedSectionsInclusion J A j ≫ (sheafSections J A).map j.op = 0 := by
  ext I
  exact kernel.condition _

omit [HasSheafify J A] [EnoughInjectives (Sheaf J A)]
  [HasDerivedCategory.{d} (Sheaf J A)] [HasDerivedCategory.{e} A] in
private theorem supportRow_shortExact
    (h : ∀ (I : Sheaf J A) [Injective I], Epi (I.obj.map j.op))
    (I : Sheaf J A) [Injective I] :
    (ShortComplex.mk ((supportedSectionsInclusion J A j).app I)
      (((sheafSections J A).map j.op).app I)
      (NatTrans.congr_app (supportRow_zero J A j) I)).ShortExact where
  exact := ShortComplex.kernelSequence_exact _
  mono_f := by change Mono (kernel.ι _); infer_instance
  epi_g := h I

private theorem supportBoundary_exists
    (h : ∀ (I : Sheaf J A) [Injective I], Epi (I.obj.map j.op)) :
    ∃ δ : ∀ q : ℤ, sectionHypercohomologyFunctor J A W q ⟶
        supportHypercohomologyFunctor J A j (q + 1),
      Functor.InjectiveBoundaryNormalized (supportedSectionsFunctor J A j)
        (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V))
        (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op W))
        (supportedSectionsInclusion J A j) ((sheafSections J A).map j.op)
        (supportRow_zero J A j) (supportRow_shortExact J A j h) δ :=
  Functor.exists_injectiveBoundary _ _ _ _ _ _ _

private theorem supportBoundary_exact
    (h : ∀ (I : Sheaf J A) [Injective I], Epi (I.obj.map j.op))
    (δ : ∀ q : ℤ, sectionHypercohomologyFunctor J A W q ⟶
      supportHypercohomologyFunctor J A j (q + 1))
    (hδ : Functor.InjectiveBoundaryNormalized (supportedSectionsFunctor J A j)
      (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V))
      (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op W))
      (supportedSectionsInclusion J A j) ((sheafSections J A).map j.op)
      (supportRow_zero J A j) (supportRow_shortExact J A j h) δ)
    (P : ObjectProperty (DerivedCategory.Plus (Sheaf J A))) :
    SupportSequenceExact J A j P (fun q => Functor.whiskerLeft P.ι (δ q)) := by
  intro K q
  let Q := (InjectiveObject.ι (Sheaf J A)).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  let M := Q.objPreimage K.obj
  obtain ⟨L, hL⟩ := HomotopyCategory.Plus.quotient_obj_surjective M
  let I := (InjectiveObject.ι (Sheaf J A)).mapCochainComplexPlus.obj L
  have (n : ℤ) : Injective (I.obj.X n) := inferInstanceAs (Injective (L.obj.X n).obj)
  let e : DerivedCategory.Plus.Q.obj I ≅ K.obj :=
    (Q.mapIso (eqToIso hL)) ≪≫ Q.objObjPreimageIso K.obj
  exact Functor.injectiveBoundary_exact _ _ _ _ _ _ _ δ hδ I K.obj e q

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem supportBoundary_pair
    {D : Type c} [Category.{v} D] (J' : GrothendieckTopology D)
    [HasSheafify J' A] [EnoughInjectives (Sheaf J' A)]
    [HasDerivedCategory.{d} (Sheaf J' A)]
    (B : C ⥤ D) [hB : B.IsContinuous J J'] {V' W' : D} (j' : W' ⟶ V')
    (h : ∀ (I : Sheaf J A) [Injective I], Epi (I.obj.map j.op))
    (h' : ∀ (I : Sheaf J' A) [Injective I], Epi (I.obj.map j'.op))
    (δ : ∀ q : ℤ, sectionHypercohomologyFunctor J A W q ⟶
      supportHypercohomologyFunctor J A j (q + 1))
    (δ' : ∀ q : ℤ, sectionHypercohomologyFunctor J' A W' q ⟶
      supportHypercohomologyFunctor J' A j' (q + 1))
    (hδ : Functor.InjectiveBoundaryNormalized (supportedSectionsFunctor J A j)
      (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V))
      (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op W))
      (supportedSectionsInclusion J A j) ((sheafSections J A).map j.op)
      (supportRow_zero J A j) (supportRow_shortExact J A j h) δ)
    (hδ' : Functor.InjectiveBoundaryNormalized (supportedSectionsFunctor J' A j')
      (sheafToPresheaf J' A ⋙ (evaluation _ _).obj (op V'))
      (sheafToPresheaf J' A ⋙ (evaluation _ _).obj (op W'))
      (supportedSectionsInclusion J' A j') ((sheafSections J' A).map j'.op)
      (supportRow_zero J' A j') (supportRow_shortExact J' A j' h') δ')
    (P : ObjectProperty (DerivedCategory.Plus (Sheaf J A)))
    (P' : ObjectProperty (DerivedCategory.Plus (Sheaf J' A)))
    (t : V' ⟶ B.obj V) (s : W' ⟶ B.obj W)
    (square : s ≫ B.map j = j' ≫ t) :
    SupportSequencePairNatural J J' A B j j' P P'
      (fun q => Functor.whiskerLeft P.ι (δ q))
      (fun q => Functor.whiskerLeft P'.ι (δ' q)) t s := by
  intro I L _ _ K K' e e' b
  let row := Functor.injectiveBoundaryRow (supportedSectionsFunctor J A j)
    (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V))
    (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op W))
    (supportedSectionsInclusion J A j) ((sheafSections J A).map j.op)
    (supportRow_zero J A j) I
  let row' := Functor.injectiveBoundaryRow (supportedSectionsFunctor J' A j')
    (sheafToPresheaf J' A ⋙ (evaluation _ _).obj (op V'))
    (sheafToPresheaf J' A ⋙ (evaluation _ _).obj (op W'))
    (supportedSectionsInclusion J' A j') ((sheafSections J' A).map j'.op)
    (supportRow_zero J' A j') L
  have R : row.ShortExact := Functor.injectiveBoundaryRow_shortExact
    (supportedSectionsFunctor J A j)
    (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V))
    (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op W))
    (supportedSectionsInclusion J A j) ((sheafSections J A).map j.op)
    (supportRow_zero J A j) (supportRow_shortExact J A j h) I
  have R' : row'.ShortExact := Functor.injectiveBoundaryRow_shortExact
    (supportedSectionsFunctor J' A j')
    (sheafToPresheaf J' A ⋙ (evaluation _ _).obj (op V'))
    (sheafToPresheaf J' A ⋙ (evaluation _ _).obj (op W'))
    (supportedSectionsInclusion J' A j') ((sheafSections J' A).map j'.op)
    (supportRow_zero J' A j') (supportRow_shortExact J' A j' h') L
  have : Mono row'.f := R'.mono_f
  let f := supportPairComplexSectionMap J J' A B I L b t
  let g := supportPairComplexSectionMap J J' A B I L b s
  have hg : row.g ≫ g = f ≫ row'.g := by
    ext n
    dsimp [row, row', f, g, supportPairComplexSectionMap, Functor.injectiveBoundaryRow,
      supportedSectionsInclusion]
    have hn := (b.f n).hom.naturality j.op
    change (I.obj.X n).obj.map j.op ≫ (b.f n).hom.app (op W) =
      (b.f n).hom.app (op V) ≫ (L.obj.X n).obj.map (B.map j).op at hn
    change (I.obj.X n).obj.map j.op ≫
        ((b.f n).hom.app (op W) ≫ (L.obj.X n).obj.map s.op) =
      ((b.f n).hom.app (op V) ≫ (L.obj.X n).obj.map t.op) ≫
        (L.obj.X n).obj.map j'.op
    rw [← Category.assoc, hn, Category.assoc, Category.assoc]
    rw [← (L.obj.X n).obj.map_comp, ← (L.obj.X n).obj.map_comp]
    rw [← op_comp, ← op_comp, square]
  have hz : row.f ≫ f ≫ row'.g = 0 := by
    rw [← hg, ← Category.assoc, row.zero, zero_comp]
  let z := R'.exact.fIsKernel.lift
    (KernelFork.ofι (row.f ≫ f) (by simpa only [Category.assoc] using hz))
  have hzι : z ≫ row'.f = row.f ≫ f := R'.exact.fIsKernel.fac _ WalkingParallelPair.zero
  refine ⟨z, ⟨hzι, ?_⟩, ?_⟩
  · intro q
    have hb : supportSequenceModelBoundary J A j P
        (fun q ↦ Functor.whiskerLeft P.ι (δ q)) I K e q = R.δ q (q + 1) rfl := by
      simpa only [supportSequenceModelBoundary, supportSequenceModelIso,
        Functor.injectiveHomologyModelIso, Functor.whiskerLeft_app, ObjectProperty.ι_obj]
        using hδ I K.obj e q
    have hb' : supportSequenceModelBoundary J' A j' P'
        (fun q ↦ Functor.whiskerLeft P'.ι (δ' q)) L K' e' q = R'.δ q (q + 1) rfl := by
      simpa only [supportSequenceModelBoundary, supportSequenceModelIso,
        Functor.injectiveHomologyModelIso, Functor.whiskerLeft_app, ObjectProperty.ι_obj]
        using hδ' L K'.obj e' q
    rw [hb, hb']
    let φ : row ⟶ row' :=
      { τ₁ := z, τ₂ := f, τ₃ := g, comm₁₂ := hzι, comm₂₃ := hg.symm }
    exact HomologicalComplex.HomologySequence.δ_naturality φ R R' q (q + 1) rfl
  · intro z' hz'
    apply (cancel_mono row'.f).1
    exact hz'.1.trans hzι.symm

end CategoryTheory.Sheaf

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem supportModule_restriction_epi
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Type (max u v)) [Ring R] [HasSheafify J (ModuleCat.{max u v} R)]
    (I : Sheaf J (ModuleCat.{max u v} R)) [Injective I]
    {W V : C} (j : W ⟶ V) [Mono j] : Epi (I.obj.map j.op) := by
  have : Injective I.obj := Injective.injective_of_adjoint (sheafificationAdjunction J _) I
  let a : (uliftYoneda.{u}.obj W ⋙ ModuleCat.free R) ⟶
      (uliftYoneda.{u}.obj V ⋙ ModuleCat.free R) :=
    Functor.whiskerRight (uliftYoneda.{u}.map j) (ModuleCat.free R)
  have : Mono a := by
    have (T : Cᵒᵖ) : Mono (a.app T) := by
      rw [ModuleCat.mono_iff_injective]
      apply Finsupp.mapDomain_injective
      intro x y h
      apply ULift.ext
      exact (cancel_mono j).1 (congrArg ULift.down h)
    exact NatTrans.mono_of_mono_app a
  rw [ModuleCat.epi_iff_surjective]
  intro s
  let b : (uliftYoneda.{u}.obj W ⋙ ModuleCat.free R) ⟶ I.obj :=
    { app := fun T ↦ ModuleCat.freeDesc (↾fun g ↦ I.obj.map g.down.op s)
      naturality := by
        intro T T' g
        apply ModuleCat.free_hom_ext
        intro x
        simp only [Functor.comp_map, ConcreteCategory.comp_apply]
        erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        change I.obj.map ((g.unop ≫ x.down).op) s = _
        rw [op_comp, I.obj.map_comp]
        rfl }
  obtain ⟨g, hg⟩ := Injective.factors b a
  refine ⟨g.app (op V) (ModuleCat.freeMk (ULift.up (𝟙 V))), ?_⟩
  have he := congrArg (fun f ↦ f.app (op W) (ModuleCat.freeMk (ULift.up (𝟙 W)))) hg
  have hn := ConcreteCategory.congr_hom (g.naturality j.op)
    (ModuleCat.freeMk (ULift.up (𝟙 V)))
  have he' : g.app (op W) (ModuleCat.freeMk (ULift.up j)) = s := by
    simpa [a, b, ModuleCat.free_map_apply, ModuleCat.freeDesc_apply] using he
  have hn' : I.obj.map j.op (g.app (op V) (ModuleCat.freeMk (ULift.up (𝟙 V)))) =
      g.app (op W) (ModuleCat.freeMk (ULift.up j)) := by
    simpa [ModuleCat.free_map_apply] using hn.symm
  exact hn'.trans he'

end CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The existing torsion-cohomology predicate restricted along the inclusion of `D⁺`.
Source: blueprint `def-weil-pbc-etale-sheaves`, final paragraph, and Milne, Section 9,
Theorem 9.4 (blueprint: thm-pur-with-support-exactness). -/
abbrev supportSequenceCoefficients (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
  ObjectProperty.inverseImage
    (fun K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ↦
      Scheme.HasTorsionEtaleCohomology K) DerivedCategory.Plus.ι

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry

/-- The long exact support sequence, natural in coefficients and in pairs, on both sites.
The first factor is the etale assertion on the full subcategory of `D⁺` with torsion
cohomology; the second is its pro-etale analogue with finite-torsion coefficients. For
sheaves take the degree-zero single functor: the canonical comparison
`Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso` identifies these groups and
maps with the natural-number right derived functors of the support definition.

The open complement is the actual open subscheme `i.openComplement`. In the pair clause
`t` and `s` are arrows over `X'` from its terminal and open objects to their base changes.
The terminal arrow is unique and exists; the open arrow exists exactly when
`U' ⊆ f⁻¹(U)`. Their displayed square encodes the restriction square. No Cartesian-pair,
quasi-compactness, Noetherian, constructibility, or descent hypothesis is imposed.

Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.4, with the site argument
of Stacks, Tags 093X, 03F3 and 0117 (blueprint: thm-pur-with-support-exactness).

Proof plan, following the node:
1. By lem-weil-pbc-site-sheaves-enough-injectives and
   lem-weil-pbc-dplus-injective-representative, represent each bounded-below object by a
   bounded-below complex of injective abelian sheaves (of coefficient modules in the
   pro-etale clause). For a sheaf start in degree zero. Torsion is required of cohomology,
   not of injective terms.
2. The support definition is the kernel of restriction on every term. By
   lem-weil-pbc-right-derived-plus-injective, supported, global and open derived sections
   are computed by these three section complexes; the comparison used here is exactly
   the right-derived-functor unit, followed by the specified representative isomorphism.
3. By lem-weil-pbc-injective-sheaf-mono-restriction, restriction of an injective along the
   open monomorphism is surjective. Thus these complexes form a short exact sequence.
   For module coefficients use the same free-module-on-a-monomorphism argument.
4. By lem-weil-pbc-site-restriction-injectives,
   lem-weil-pbc-cohomology-over-object-localization and
   lem-weil-pbc-etale-cohomology-over-open, open evaluation computes the cohomology on the
   open subscheme with restricted coefficients.
5. Apply lem-weil-pbc-complex-ses-homology-long-exact at each integer degree. Its three
   exactness assertions give the three conjuncts of SupportSequenceExact. For sheaves
   use the single-functor comparison to recover R^q and the initial zero term.
6. By lem-weil-pbc-kinjective-hom-derived, a derived coefficient map is represented by a
   chain map, unique up to homotopy. By lem-weil-pbc-complex-ses-long-exact-naturality its
   homology maps commute with the boundary. Evaluation and the support kernel preserve
   homotopies, giving a natural transformation on the torsion full subcategory and
   independence of all choices.
7. For a pair map and a coefficient map f⁻¹K → L, use exactness of inverse image
   (prop-weil-pbc-inverse-image-exact and lem-weil-pbc-site-pullback-abelian-exact) and
   lem-weil-pbc-kinjective-hom-derived to choose the adjoint chain map b : I → f_*J.
   Its section maps are precisely supportPairComplexSectionMap at t and s. Their square
   commutes, so the kernel map exists uniquely and the same long-exact naturality gives
   the boundary square. Homotopies restrict to kernels. Identity maps induce identities;
   for two pair maps, adjunction and lem-weil-pbc-inverse-image-composition (respectively
   lem-weil-pbc-site-morphism-composition) identify the adjoint of the composite with
   I → f_*J → f_*g_*P. Evaluation, restriction and kernel functoriality identify all
   three maps with the composites, hence the identity and composition laws hold.
8. Repeat the identical construction on the small pro-etale site. By
   lem-weil-proetale-weakly-etale-localization and
   lem-weil-pbc-proetale-restriction-injectives the localized site and its coefficient
   restriction are those of U. Steps 1-7 apply directly, including non-descending
   coefficients. Use the specified finite quotient rings A_{E,n}, with their canonical
   universe lift. -/
theorem exists_support_longExact :
    (∃ δ : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
        Sheaf.SupportSequenceBoundary X.smallEtaleTopology AddCommGrpCat.{u + 1}
          (Etale.supportRestrictionArrow i) (Etale.supportSequenceCoefficients X),
      (∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
        Sheaf.SupportSequenceExact X.smallEtaleTopology AddCommGrpCat.{u + 1}
          (Etale.supportRestrictionArrow i) (Etale.supportSequenceCoefficients X) (δ i)) ∧
      (∀ {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
        (i' : Z' ⟶ X') [IsClosedImmersion i'] (f : X' ⟶ X)
        (t : Scheme.Etale.mk (𝟙 X') ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ f).obj (Scheme.Etale.mk (𝟙 X)))
        (s : Scheme.Etale.mk i'.openComplement.ι ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ f).obj
            (Scheme.Etale.mk i.openComplement.ι)),
        s ≫ (MorphismProperty.Over.pullback @Etale ⊤ f).map
            (Etale.supportRestrictionArrow i) = Etale.supportRestrictionArrow i' ≫ t →
        Sheaf.SupportSequencePairNatural X.smallEtaleTopology X'.smallEtaleTopology
          AddCommGrpCat.{u + 1} (MorphismProperty.Over.pullback @Etale ⊤ f)
          (hB := Etale.isContinuous_overPullback f)
          (Etale.supportRestrictionArrow i) (Etale.supportRestrictionArrow i')
          (Etale.supportSequenceCoefficients X) (Etale.supportSequenceCoefficients X')
          (δ i) (δ i') t s)) ∧
    (∀ (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n),
      ∃ δ : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
          Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology X)
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))
            (ProEtale.supportRestrictionArrow i) ⊤,
        (∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
          Sheaf.SupportSequenceExact (Scheme.ProEt.topology X)
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))
            (ProEtale.supportRestrictionArrow i) ⊤ (δ i)) ∧
        (∀ {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
          (i' : Z' ⟶ X') [IsClosedImmersion i'] (f : X' ⟶ X)
          (t : Scheme.ProEt.mk (𝟙 X') ⟶
            (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj (Scheme.ProEt.mk (𝟙 X)))
          (s : Scheme.ProEt.mk i'.openComplement.ι ⟶
            (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj
              (Scheme.ProEt.mk i.openComplement.ι)),
          s ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map
              (ProEtale.supportRestrictionArrow i) = ProEtale.supportRestrictionArrow i' ≫ t →
          Sheaf.SupportSequencePairNatural (Scheme.ProEt.topology X) (Scheme.ProEt.topology X')
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))
            (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f)
            (hB := Scheme.ProEt.isContinuous_overPullback f)
            (ProEtale.supportRestrictionArrow i) (ProEtale.supportRestrictionArrow i')
            ⊤ ⊤ (δ i) (δ i') t s)) := by
  classical
  let : HasDerivedCategory.{u + 1} AddCommGrpCat.{u + 1} :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  have hEt {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I] :
      Epi (I.obj.map (Etale.supportRestrictionArrow i).op) := by
    have : Mono (Etale.supportRestrictionArrow i) :=
      (MorphismProperty.Over.forget @Etale ⊤ X ⋙ Over.forget X).mono_of_mono_map
        (inferInstanceAs (Mono i.openComplement.ι))
    rw [AddCommGrpCat.epi_iff_surjective]
    exact injective_sheaf_mono_restriction.{u + 1, u, u + 1} _ I _
  let dEt {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
      ∀ q : ℤ, Sheaf.sectionHypercohomologyFunctor.{u + 1, u, u + 2, u + 1, u + 1, u + 1}
        X.smallEtaleTopology AddCommGrpCat.{u + 1} (Scheme.Etale.mk i.openComplement.ι) q ⟶
        Sheaf.supportHypercohomologyFunctor X.smallEtaleTopology AddCommGrpCat.{u + 1}
          (Etale.supportRestrictionArrow i) (q + 1) :=
    Classical.choose (Sheaf.supportBoundary_exists.{u + 1, u, u + 2, u + 1, u + 1, u + 1}
      X.smallEtaleTopology
      AddCommGrpCat.{u + 1} (Etale.supportRestrictionArrow i) (hEt i))
  have hdEt {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
    Classical.choose_spec (Sheaf.supportBoundary_exists.{u + 1, u, u + 2, u + 1, u + 1, u + 1}
      X.smallEtaleTopology
      AddCommGrpCat.{u + 1} (Etale.supportRestrictionArrow i) (hEt i))
  constructor
  · refine ⟨fun {Z X} i _ q ↦ Functor.whiskerLeft
        (Etale.supportSequenceCoefficients X).ι (dEt i q), ?_, ?_⟩
    · intro Z X i hi
      exact Sheaf.supportBoundary_exact _ _ _ (hEt i) (dEt i) (hdEt i) _
    · intro Z X Z' X' i hi i' hi' f t s hs
      exact Sheaf.supportBoundary_pair X.smallEtaleTopology AddCommGrpCat.{u + 1}
        (Etale.supportRestrictionArrow i) X'.smallEtaleTopology
        (MorphismProperty.Over.pullback @Etale ⊤ f)
        (hB := Etale.isContinuous_overPullback f) (Etale.supportRestrictionArrow i')
        (hEt i) (hEt i')
        (dEt i) (dEt i') (hdEt i) (hdEt i') _ _ t s hs
  · intro l hl E hE hAl hFin n hn
    let A := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))
    let : HasDerivedCategory.{u + 1} A := HasDerivedCategory.ofIsGrothendieckAbelian _
    have hPro {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
        (I : Sheaf (Scheme.ProEt.topology X) A) [Injective I] :
        Epi (I.obj.map (ProEtale.supportRestrictionArrow i).op) := by
      have : Mono (ProEtale.supportRestrictionArrow i) :=
        (MorphismProperty.Over.forget @WeaklyEtale ⊤ X ⋙ Over.forget X).mono_of_mono_map
          (inferInstanceAs (Mono i.openComplement.ι))
      exact supportModule_restriction_epi.{u + 1, u, u + 1} _ _ I _
    let dPro {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
        ∀ q : ℤ, Sheaf.sectionHypercohomologyFunctor.{u + 1, u, u + 2, u + 1, u + 1, u + 1}
          (Scheme.ProEt.topology X) A (Scheme.ProEt.mk i.openComplement.ι) q ⟶
          Sheaf.supportHypercohomologyFunctor (Scheme.ProEt.topology X) A
            (ProEtale.supportRestrictionArrow i) (q + 1) :=
      Classical.choose (Sheaf.supportBoundary_exists.{u + 1, u, u + 2, u + 1, u + 1, u + 1}
        (Scheme.ProEt.topology X)
        A (ProEtale.supportRestrictionArrow i) (hPro i))
    have hdPro {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
      Classical.choose_spec (Sheaf.supportBoundary_exists.{u + 1, u, u + 2, u + 1, u + 1, u + 1}
        (Scheme.ProEt.topology X)
        A (ProEtale.supportRestrictionArrow i) (hPro i))
    refine ⟨fun {Z X} i _ q ↦ Functor.whiskerLeft
        (⊤ : ObjectProperty (DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) A))).ι
        (dPro i q), ?_, ?_⟩
    · intro Z X i hi
      exact Sheaf.supportBoundary_exact _ _ _ (hPro i) (dPro i) (hdPro i) _
    · intro Z X Z' X' i hi i' hi' f t s hs
      exact Sheaf.supportBoundary_pair (Scheme.ProEt.topology X) A
        (ProEtale.supportRestrictionArrow i) (Scheme.ProEt.topology X')
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f)
        (hB := Scheme.ProEt.isContinuous_overPullback f) (ProEtale.supportRestrictionArrow i')
        (hPro i) (hPro i')
        (dPro i) (dPro i') (hdPro i) (hdPro i') _ _ t s hs

end AlgebraicGeometry
