/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Two triple direct-image paths on common resolutions

Source: Stacks Project, Cohomology on Sites, Tag 0D6E, and Derived Categories,
Tags 070I and 070Y (blueprint: lem-pur-ringed-triple-resolution-formulas).
The six derived functors and four comparisons are represented with precisely the
unit characterization of `ringedToposDerivedPushforwardComposition`.
The existential coordinate isomorphisms below are fixed by equations for their
inverses; they are not arbitrary identifications. All underived composites use
the composites of the module functors, as in the pairwise comparison theorem.

## Main definitions

- `Functor.HasTripleResolutionFormulas`: the explicit common-resolution conclusion.

## Main statements

- `ringedTripleResolution_formulas`: the two paths for ringed-topos direct images.
-/

@[expose] public section

set_option autoImplicit false

universe u w v x

open CategoryTheory

namespace CategoryTheory.Functor

section FormulaPredicate

/-- The explicit common-resolution formulas, including all four factors and both
canonical kinds of resolution transition, packaged to avoid repeated elaboration of
concrete module-sheaf categories. This predicate is the conclusion of the ringed-topos
statement below; it imposes no hypotheses on the derived data by itself.
Source: Stacks Tags 0D6E, 070I and 070Y; the eight-step common-resolution extraction
(blueprint: lem-pur-ringed-triple-resolution-formulas). -/
noncomputable def HasTripleResolutionFormulas
    {M0 M1 M2 M3 : Type x}
    [Category.{v} M0] [Category.{v} M1] [Category.{v} M2] [Category.{v} M3]
    [Abelian M0] [Abelian M1] [Abelian M2] [Abelian M3]
    [HasDerivedCategory.{w} M0] [HasDerivedCategory.{w} M1]
    [HasDerivedCategory.{w} M2] [HasDerivedCategory.{w} M3]
    (F : M0 ⥤ M1) (G : M1 ⥤ M2) (H : M2 ⥤ M3)
    [F.Additive] [G.Additive] [H.Additive]
    (Rf : DerivedCategory.{w} M0 ⥤ DerivedCategory.{w} M1)
    (Rg : DerivedCategory.{w} M1 ⥤ DerivedCategory.{w} M2)
    (Rh : DerivedCategory.{w} M2 ⥤ DerivedCategory.{w} M3)
    (Rgf : DerivedCategory.{w} M0 ⥤ DerivedCategory.{w} M2)
    (Rhg : DerivedCategory.{w} M1 ⥤ DerivedCategory.{w} M3)
    (Rhgf : DerivedCategory.{w} M0 ⥤ DerivedCategory.{w} M3)
    (ηf : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rf)
    (ηg : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rg)
    (ηh : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rh)
    (ηgf : (F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rgf)
    (ηhg : (G ⋙ H).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rhg)
    (ηhgf : ((F ⋙ G) ⋙ H).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rhgf)
    (κgf : Rgf ≅ Rf ⋙ Rg) (κhg : Rhg ≅ Rg ⋙ Rh)
    (κh_gf : Rhgf ≅ Rgf ⋙ Rh) (κhg_f : Rhgf ≅ Rf ⋙ Rhg)
    (I : CochainComplex M0 ℤ)
    (J : CochainComplex M1 ℤ)
    (K T : CochainComplex M2 ℤ)
    (j : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso j]
    (k : (G.mapHomologicalComplex (.up ℤ)).obj J ⟶ K) [QuasiIso k]
    (t : ((G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj I)) ⟶ T)
          [QuasiIso t] : Prop :=
    QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j) ∧ QuasiIso
          (((G.mapHomologicalComplex (.up ℤ)).map j) ≫ k) ∧
    ∃ u : (HomotopyCategory.quotient _ (.up ℤ)).obj T ⟶
        (HomotopyCategory.quotient _ (.up ℤ)).obj K,
      DerivedCategory.Qh.{w}.map u = Functor.kInjectiveResolutionHomTarget t (𝟙 K)
          (DerivedCategory.Q.{w}.map (((G.mapHomologicalComplex (.up ℤ)).map j) ≫ k)) ∧
      (HomotopyCategory.quotient _ (.up ℤ)).map t ≫ u =
        (HomotopyCategory.quotient _ (.up ℤ)).map (((G.mapHomologicalComplex (.up ℤ)).map j) ≫ k) ∧
      (∀ u' : (HomotopyCategory.quotient _ (.up ℤ)).obj T ⟶
          (HomotopyCategory.quotient _ (.up ℤ)).obj K,
        DerivedCategory.Qh.{w}.map u' = Functor.kInjectiveResolutionHomTarget t (𝟙 K)
          (DerivedCategory.Q.{w}.map (((G.mapHomologicalComplex (.up ℤ)).map j) ≫ k)) →
          u' = u) ∧
      ∃ (a : Rf.obj (DerivedCategory.Q.{w}.obj I) ≅ (DerivedCategory.Q.{w}.obj J))
        (v : Rgf.obj (DerivedCategory.Q.{w}.obj I) ≅ (DerivedCategory.Q.{w}.obj
          ((G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj I))))
        (b : Rg.obj (Rf.obj (DerivedCategory.Q.{w}.obj I)) ≅ (DerivedCategory.Q.{w}.obj
          ((G.mapHomologicalComplex (.up ℤ)).obj J)))
        (s : Rhgf.obj (DerivedCategory.Q.{w}.obj I) ≅ (DerivedCategory.Q.{w}.obj
          ((H.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj I)))))
        (m : Rh.obj (Rgf.obj (DerivedCategory.Q.{w}.obj I)) ≅ (DerivedCategory.Q.{w}.obj
          ((H.mapHomologicalComplex (.up ℤ)).obj T)))
        (r : Rhg.obj (Rf.obj (DerivedCategory.Q.{w}.obj I)) ≅ (DerivedCategory.Q.{w}.obj
          ((H.mapHomologicalComplex (.up ℤ)).obj ((G.mapHomologicalComplex (.up ℤ)).obj J))))
        (d : Rh.obj (Rg.obj (Rf.obj (DerivedCategory.Q.{w}.obj I))) ≅ (DerivedCategory.Q.{w}.obj
          ((H.mapHomologicalComplex (.up ℤ)).obj K))),
        a.inv = CategoryTheory.inv (DerivedCategory.Q.{w}.map j) ≫ ηf.app I ∧
        v.inv = ηgf.app I ∧
        b.inv = ηg.app J ≫ Rg.map a.inv ∧
        s.inv = ηhgf.app I ∧
        m.inv = ηh.app T ≫ Rh.map (CategoryTheory.inv (DerivedCategory.Q.{w}.map t) ≫ v.inv) ∧
        r.inv = ηhg.app J ≫ Rhg.map a.inv ∧
        d.inv = ηh.app K ≫ Rh.map (CategoryTheory.inv (DerivedCategory.Q.{w}.map k) ≫ b.inv) ∧
        s.inv ≫ κh_gf.hom.app (DerivedCategory.Q.{w}.obj I) ≫ m.hom = DerivedCategory.Q.{w}.map
          ((H.mapHomologicalComplex (.up ℤ)).map t) ∧
        m.inv ≫ Rh.map (κgf.hom.app (DerivedCategory.Q.{w}.obj I)) ≫ d.hom =
          H.kInjectiveHomotopyImage u ∧
        s.inv ≫ κhg_f.hom.app (DerivedCategory.Q.{w}.obj I) ≫ r.hom = DerivedCategory.Q.{w}.map
          ((H.mapHomologicalComplex (.up ℤ)).map ((G.mapHomologicalComplex (.up ℤ)).map j)) ∧
        r.inv ≫ κhg.hom.app (Rf.obj (DerivedCategory.Q.{w}.obj I)) ≫ d.hom =
          DerivedCategory.Q.{w}.map ((H.mapHomologicalComplex (.up ℤ)).map k) ∧
        s.inv ≫ κh_gf.hom.app (DerivedCategory.Q.{w}.obj I) ≫
            Rh.map (κgf.hom.app (DerivedCategory.Q.{w}.obj I)) ≫ d.hom =
          DerivedCategory.Q.{w}.map ((H.mapHomologicalComplex (.up ℤ)).map t) ≫
          H.kInjectiveHomotopyImage u ∧
        s.inv ≫ κhg_f.hom.app (DerivedCategory.Q.{w}.obj I) ≫
            κhg.hom.app (Rf.obj (DerivedCategory.Q.{w}.obj I)) ≫ d.hom =
          DerivedCategory.Q.{w}.map ((H.mapHomologicalComplex (.up ℤ)).map
          ((G.mapHomologicalComplex (.up ℤ)).map j)) ≫ DerivedCategory.Q.{w}.map
          ((H.mapHomologicalComplex (.up ℤ)).map k) ∧
        (∀ (T' : CochainComplex M2 ℤ) [T'.IsKInjective]
            (t' : ((G.mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj I)) ⟶ T') [QuasiIso t']
            (m' : Rh.obj (Rgf.obj (DerivedCategory.Q.{w}.obj I)) ≅
              DerivedCategory.Q.{w}.obj ((H.mapHomologicalComplex (.up ℤ)).obj T')),
          m'.inv = ηh.app T' ≫ Rh.map (CategoryTheory.inv (DerivedCategory.Q.{w}.map t') ≫ v.inv) →
          ∃! z : (HomotopyCategory.quotient _ (.up ℤ)).obj T ⟶
              (HomotopyCategory.quotient _ (.up ℤ)).obj T',
            DerivedCategory.Qh.{w}.map z =
                Functor.kInjectiveResolutionHomTarget t t' (𝟙 (DerivedCategory.Q.{w}.obj
          ((G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj I)))) ∧
              m.inv ≫ m'.hom = H.kInjectiveHomotopyImage z) ∧
        (∀ (J' : CochainComplex M1 ℤ) [J'.IsKInjective]
            (K' : CochainComplex M2 ℤ) [K'.IsKInjective]
            (j' : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J') [QuasiIso j']
            (k' : (G.mapHomologicalComplex (.up ℤ)).obj J' ⟶ K') [QuasiIso k']
            (a' : Rf.obj (DerivedCategory.Q.{w}.obj I) ≅ DerivedCategory.Q.{w}.obj J')
            (b' : Rg.obj (Rf.obj (DerivedCategory.Q.{w}.obj I)) ≅ DerivedCategory.Q.{w}.obj
          ((G.mapHomologicalComplex (.up ℤ)).obj J'))
            (d' : Rh.obj (Rg.obj (Rf.obj (DerivedCategory.Q.{w}.obj I))) ≅
              DerivedCategory.Q.{w}.obj ((H.mapHomologicalComplex (.up ℤ)).obj K')),
          a'.inv = CategoryTheory.inv (DerivedCategory.Q.{w}.map j') ≫ ηf.app I →
          b'.inv = ηg.app J' ≫ Rg.map a'.inv →
          d'.inv = ηh.app K' ≫ Rh.map (CategoryTheory.inv (DerivedCategory.Q.{w}.map k') ≫ b'.inv) →
          ∃! z : (HomotopyCategory.quotient _ (.up ℤ)).obj K ⟶
              (HomotopyCategory.quotient _ (.up ℤ)).obj K',
            DerivedCategory.Qh.{w}.map z =
                Functor.kInjectiveResolutionHomTarget k k' (b.inv ≫ b'.hom) ∧
              d.inv ≫ d'.hom = H.kInjectiveHomotopyImage z)
end FormulaPredicate

private theorem homotopyImage_map
    {A B : Type x} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive]
    {I J : CochainComplex A ℤ} (g : I ⟶ J) :
    F.kInjectiveHomotopyImage ((HomotopyCategory.quotient A (.up ℤ)).map g) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map g) := by
  unfold kInjectiveHomotopyImage
  change (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient B (.up ℤ)).map
      ((F.mapHomologicalComplex (.up ℤ)).map g)) ≫
      (DerivedCategory.quotientCompQhIso B).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj J) = _
  rw [DerivedCategory.quotientCompQhIso_hom_naturality]
  simp

private theorem resolution_naturality
    {A B : Type x} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    {N N' I J : CochainComplex A ℤ} (a : N ⟶ I) (b : N' ⟶ J) [QuasiIso a]
    (h : DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj N')
    (g : (HomotopyCategory.quotient A (.up ℤ)).obj I ⟶
      (HomotopyCategory.quotient A (.up ℤ)).obj J)
    (hg : DerivedCategory.Qh.map g = kInjectiveResolutionHomTarget a b h) :
    η.app I ≫ RF.map (CategoryTheory.inv (DerivedCategory.Q.map a) ≫ h ≫ DerivedCategory.Q.map b) =
      F.kInjectiveHomotopyImage g ≫ η.app J := by
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective g
  have hq : DerivedCategory.Q.map g =
      CategoryTheory.inv (DerivedCategory.Q.map a) ≫ h ≫ DerivedCategory.Q.map b := by
    have he := congrArg (fun q ↦ (DerivedCategory.quotientCompQhIso A).inv.app I ≫ q ≫
      (DerivedCategory.quotientCompQhIso A).hom.app J) hg
    simpa [kInjectiveResolutionHomTarget, Category.assoc,
      ← DerivedCategory.quotientCompQhIso_inv_naturality, -NatTrans.naturality] using he
  rw [← hq, homotopyImage_map]
  exact (η.naturality g).symm

private theorem coordinate_map
    {A B : Type x} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    {N N' I J : CochainComplex A ℤ} (a : N ⟶ I) (b : N' ⟶ J)
    [QuasiIso a] [QuasiIso b]
    {X Y : DerivedCategory.{w} A} (e : X ≅ DerivedCategory.Q.obj N)
    (e' : Y ≅ DerivedCategory.Q.obj N') (q : X ⟶ Y)
    (c : RF.obj X ≅ DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I))
    (c' : RF.obj Y ≅ DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj J))
    (hc : c.inv = η.app I ≫ RF.map (CategoryTheory.inv (DerivedCategory.Q.map a) ≫ e.inv))
    (hc' : c'.inv = η.app J ≫ RF.map (CategoryTheory.inv (DerivedCategory.Q.map b) ≫ e'.inv))
    (g : (HomotopyCategory.quotient A (.up ℤ)).obj I ⟶
      (HomotopyCategory.quotient A (.up ℤ)).obj J)
    (hg : DerivedCategory.Qh.map g =
      kInjectiveResolutionHomTarget a b (e.inv ≫ q ≫ e'.hom)) :
    c.inv ≫ RF.map q ≫ c'.hom = F.kInjectiveHomotopyImage g := by
  apply (cancel_mono c'.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hc, hc']
  have hn := resolution_naturality F RF η a b (e.inv ≫ q ≫ e'.hom) g hg
  calc
    _ = (η.app I ≫ RF.map (CategoryTheory.inv (DerivedCategory.Q.map a) ≫
        (e.inv ≫ q ≫ e'.hom) ≫ DerivedCategory.Q.map b)) ≫
        RF.map (CategoryTheory.inv (DerivedCategory.Q.map b) ≫ e'.inv) := by
      simp [Functor.map_comp, Category.assoc]
    _ = _ := by rw [hn, Category.assoc]

private theorem unit_iso
    {A B : Type x} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
    (η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    [RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ))]
    (I : CochainComplex A ℤ) [I.IsKInjective] : IsIso (η.app I) :=
  (CategoryTheory.derives F).isIso_of_isRightDerivedFunctor η (CochainComplex.KInjectives.mk I)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem triple_formulas
    {M0 M1 M2 M3 : Type x}
    [Category.{v} M0] [Category.{v} M1] [Category.{v} M2] [Category.{v} M3]
    [Abelian M0] [Abelian M1] [Abelian M2] [Abelian M3]
    [HasDerivedCategory.{w} M0] [HasDerivedCategory.{w} M1]
    [HasDerivedCategory.{w} M2] [HasDerivedCategory.{w} M3]
    [Abelian.HasKInjectiveResolutions M0] [Abelian.HasKInjectiveResolutions M1]
    [Abelian.HasKInjectiveResolutions M2]
    (F : M0 ⥤ M1) (G : M1 ⥤ M2) (H : M2 ⥤ M3)
    [F.Additive] [G.Additive] [H.Additive]
    (Rf : DerivedCategory.{w} M0 ⥤ DerivedCategory.{w} M1)
    (Rg : DerivedCategory.{w} M1 ⥤ DerivedCategory.{w} M2)
    (Rh : DerivedCategory.{w} M2 ⥤ DerivedCategory.{w} M3)
    (Rgf : DerivedCategory.{w} M0 ⥤ DerivedCategory.{w} M2)
    (Rhg : DerivedCategory.{w} M1 ⥤ DerivedCategory.{w} M3)
    (Rhgf : DerivedCategory.{w} M0 ⥤ DerivedCategory.{w} M3)
    (ηf : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rf)
    (ηg : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rg)
    (ηh : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rh)
    (ηgf : (F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rgf)
    (ηhg : (G ⋙ H).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rhg)
    (ηhgf : ((F ⋙ G) ⋙ H).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rhgf)
    [Rf.IsRightDerivedFunctor ηf (HomologicalComplex.quasiIso M0 (.up ℤ))]
    [Rg.IsRightDerivedFunctor ηg (HomologicalComplex.quasiIso M1 (.up ℤ))]
    [Rh.IsRightDerivedFunctor ηh (HomologicalComplex.quasiIso M2 (.up ℤ))]
    [Rgf.IsRightDerivedFunctor ηgf (HomologicalComplex.quasiIso M0 (.up ℤ))]
    [Rhg.IsRightDerivedFunctor ηhg (HomologicalComplex.quasiIso M1 (.up ℤ))]
    [Rhgf.IsRightDerivedFunctor ηhgf (HomologicalComplex.quasiIso M0 (.up ℤ))]
    (κgf : Rgf ≅ Rf ⋙ Rg) (κhg : Rhg ≅ Rg ⋙ Rh)
    (κh_gf : Rhgf ≅ Rgf ⋙ Rh) (κhg_f : Rhgf ≅ Rf ⋙ Rhg)
    (hκgf : ∀ X, ηgf.app X ≫ κgf.hom.app (DerivedCategory.Q.obj X) =
      ηg.app ((F.mapHomologicalComplex (.up ℤ)).obj X) ≫ Rg.map (ηf.app X))
    (hκhg : ∀ X, ηhg.app X ≫ κhg.hom.app (DerivedCategory.Q.obj X) =
      ηh.app ((G.mapHomologicalComplex (.up ℤ)).obj X) ≫ Rh.map (ηg.app X))
    (hκh_gf : ∀ X, ηhgf.app X ≫ κh_gf.hom.app (DerivedCategory.Q.obj X) =
      ηh.app (((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj X) ≫ Rh.map (ηgf.app X))
    (hκhg_f : ∀ X, ηhgf.app X ≫ κhg_f.hom.app (DerivedCategory.Q.obj X) =
      ηhg.app ((F.mapHomologicalComplex (.up ℤ)).obj X) ≫ Rhg.map (ηf.app X))
    (I : CochainComplex M0 ℤ) [I.IsKInjective]
    (J : CochainComplex M1 ℤ) [J.IsKInjective]
    (K T : CochainComplex M2 ℤ) [K.IsKInjective] [T.IsKInjective]
    (j : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso j]
    (k : (G.mapHomologicalComplex (.up ℤ)).obj J ⟶ K) [QuasiIso k]
    (t : ((G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj I)) ⟶ T)
          [QuasiIso t] :
    HasTripleResolutionFormulas F G H Rf Rg Rh Rgf Rhg Rhgf
      ηf ηg ηh ηgf ηhg ηhgf κgf κhg κh_gf κhg_f I J K T j k t := by
  classical
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let Hc := H.mapHomologicalComplex (.up ℤ)
  have := unit_iso F Rf ηf I
  have := unit_iso G Rg ηg J
  have := unit_iso H Rh ηh K
  have := unit_iso H Rh ηh T
  have := unit_iso (F ⋙ G) Rgf ηgf I
  have := unit_iso (G ⋙ H) Rhg ηhg J
  have := unit_iso ((F ⋙ G) ⋙ H) Rhgf ηhgf I
  let a := (asIso (ηf.app I)).symm ≪≫ asIso (DerivedCategory.Q.map j)
  let v := (asIso (ηgf.app I)).symm
  let b := Rg.mapIso a ≪≫ (asIso (ηg.app J)).symm
  let s := (asIso (ηhgf.app I)).symm
  let m := Rh.mapIso v ≪≫ Rh.mapIso (asIso (DerivedCategory.Q.map t)) ≪≫
    (asIso (ηh.app T)).symm
  let r := Rhg.mapIso a ≪≫ (asIso (ηhg.app J)).symm
  let d := Rh.mapIso b ≪≫ Rh.mapIso (asIso (DerivedCategory.Q.map k)) ≪≫
    (asIso (ηh.app K)).symm
  have ha : a.inv = CategoryTheory.inv (DerivedCategory.Q.map j) ≫ ηf.app I := rfl
  have hb : b.inv = ηg.app J ≫ Rg.map a.inv := rfl
  have hm : m.inv = ηh.app T ≫ Rh.map (CategoryTheory.inv (DerivedCategory.Q.map t) ≫ v.inv) := by
    simp [m, Functor.map_comp]
  have hd : d.inv = ηh.app K ≫ Rh.map (CategoryTheory.inv (DerivedCategory.Q.map k) ≫ b.inv) := by
    simp [d, Functor.map_comp]
  have hr : r.inv = ηhg.app J ≫ Rhg.map a.inv := rfl
  have hp : v.inv ≫ κgf.hom.app (DerivedCategory.Q.obj I) ≫ b.hom =
      DerivedCategory.Q.map (Gc.map j) := by
    apply (cancel_mono b.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change ηgf.app I ≫ κgf.hom.app (DerivedCategory.Q.obj I) = _
    rw [hκgf I, hb, ha]
    have hn := ηg.naturality j
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, hn]
    simp [Functor.map_comp, Category.assoc]
  have : IsIso (DerivedCategory.Q.map (Gc.map j)) := by
    rw [← hp]
    infer_instance
  have hpq : QuasiIso (Gc.map j) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp inferInstance
  have := hpq
  have hwq : QuasiIso (Gc.map j ≫ k) := inferInstance
  obtain ⟨u, hu⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient M2 (.up ℤ)).obj T) K).surjective
      (kInjectiveResolutionHomTarget t (𝟙 K) (DerivedCategory.Q.map (Gc.map j ≫ k)))
  have htu : (HomotopyCategory.quotient M2 (.up ℤ)).map t ≫ u =
      (HomotopyCategory.quotient M2 (.up ℤ)).map (Gc.map j ≫ k) := by
    apply (CochainComplex.IsKInjective.Qh_map_bijective _ K).injective
    rw [Functor.map_comp, hu]
    simp [kInjectiveResolutionHomTarget, Category.assoc,
      DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
  have h₁ : s.inv ≫ κh_gf.hom.app (DerivedCategory.Q.obj I) ≫ m.hom =
      DerivedCategory.Q.map (Hc.map t) := by
    apply (cancel_mono m.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change ηhgf.app I ≫ κh_gf.hom.app (DerivedCategory.Q.obj I) = _
    rw [hκh_gf I, hm]
    have hn := ηh.naturality t
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, hn]
    simp [Functor.map_comp, Category.assoc]; rfl
  have h₂ : m.inv ≫ Rh.map (κgf.hom.app (DerivedCategory.Q.obj I)) ≫ d.hom =
      H.kInjectiveHomotopyImage u := by
    apply coordinate_map H Rh ηh t k v b _ m d hm hd u
    rw [hp]
    simpa only [kInjectiveResolutionHomTarget, Functor.map_comp, Functor.map_id,
      Category.comp_id, Category.id_comp, Category.assoc] using hu
  have h₃ : s.inv ≫ κhg_f.hom.app (DerivedCategory.Q.obj I) ≫ r.hom =
      DerivedCategory.Q.map (Hc.map (Gc.map j)) := by
    apply (cancel_mono r.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change ηhgf.app I ≫ κhg_f.hom.app (DerivedCategory.Q.obj I) = _
    rw [hκhg_f I, hr, ha]
    have hn := ηhg.naturality j
    dsimp only [Functor.comp_map] at hn
    change ηhg.app (Fc.obj I) ≫ Rhg.map (ηf.app I) =
      DerivedCategory.Q.map (((G ⋙ H).mapHomologicalComplex (.up ℤ)).map j) ≫
        ηhg.app J ≫ Rhg.map (CategoryTheory.inv (DerivedCategory.Q.map j) ≫ ηf.app I)
    rw [← Category.assoc, hn]
    simp [Functor.map_comp, Category.assoc]; rfl
  have h₄ : r.inv ≫ κhg.hom.app (Rf.obj (DerivedCategory.Q.obj I)) ≫ d.hom =
      DerivedCategory.Q.map (Hc.map k) := by
    apply (cancel_mono d.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hr, hd]
    have hn := κhg.hom.naturality a.inv
    dsimp only [Functor.comp_map] at hn
    rw [Category.assoc]
    change ηhg.app J ≫ Rhg.map a.inv ≫ κhg.hom.app ((DerivedCategory.Q ⋙ Rf).obj I) =
      DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map k) ≫
        ηh.app K ≫ Rh.map (CategoryTheory.inv (DerivedCategory.Q.map k) ≫ b.inv)
    rw [hn, ← Category.assoc, hκhg J, hb]
    have hk := ηh.naturality k
    dsimp only [Functor.comp_map] at hk
    rw [← Category.assoc (DerivedCategory.Q.map (Hc.map k)), hk]
    simp [Functor.map_comp, Category.assoc]
  refine ⟨hpq, hwq, u, hu, htu, ?_, a, v, b, s, m, r, d,
    ha, rfl, hb, rfl, hm, hr, hd, h₁, h₂, h₃, h₄, ?_, ?_, ?_, ?_⟩
  · intro u' hu'
    exact (CochainComplex.IsKInjective.Qh_map_bijective _ K).injective (hu'.trans hu.symm)
  · rw [← h₁, ← h₂]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  · rw [← h₃, ← h₄]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  · intro T' hT' t' ht' m' hm'
    obtain ⟨z, hz⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient M2 (.up ℤ)).obj T) T').surjective
        (kInjectiveResolutionHomTarget t t' (𝟙 _))
    refine ⟨z, ⟨hz, ?_⟩, ?_⟩
    · have he := coordinate_map H Rh ηh t t' v v (𝟙 _) m m' hm hm' z
      simp only [Category.id_comp, Iso.inv_hom_id] at he
      simpa using he hz
    · intro z' hz'
      exact (CochainComplex.IsKInjective.Qh_map_bijective _ T').injective
        (hz'.1.trans hz.symm)
  · intro J' hJ' K' hK' j' hj' k' hk' a' b' d' ha' hb' hd'
    obtain ⟨z, hz⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient M2 (.up ℤ)).obj K) K').surjective
        (kInjectiveResolutionHomTarget k k' (b.inv ≫ b'.hom))
    refine ⟨z, ⟨hz, ?_⟩, ?_⟩
    · have he := coordinate_map H Rh ηh k k' b b' (𝟙 _) d d' hd hd' z
      simp only [Category.id_comp] at he
      simpa using he hz
    · intro z' hz'
      exact (CochainComplex.IsKInjective.Qh_map_bijective _ K').injective
        (hz'.1.trans hz.symm)

end CategoryTheory.Functor

namespace CategoryTheory

variable
    {C0 : Type u} [SmallCategory C0]
    {C1 : Type u} [SmallCategory C1]
    {C2 : Type u} [SmallCategory C2]
    {C3 : Type u} [SmallCategory C3]
    (J0 : GrothendieckTopology C0) (A0 : Sheaf J0 CommRingCat.{u})
    (J1 : GrothendieckTopology C1) (A1 : Sheaf J1 CommRingCat.{u})
    (J2 : GrothendieckTopology C2) (A2 : Sheaf J2 CommRingCat.{u})
    (J3 : GrothendieckTopology C3) (A3 : Sheaf J3 CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J2 (forget₂ CommRingCat.{u} RingCat.{u})).obj A2))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J3 (forget₂ CommRingCat.{u} RingCat.{u})).obj A3))]
    (f : RingedToposMorphism ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)
      ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1))
    (g : RingedToposMorphism ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)
      ((sheafCompose J2 (forget₂ CommRingCat.{u} RingCat.{u})).obj A2))
    (h : RingedToposMorphism ((sheafCompose J2 (forget₂ CommRingCat.{u} RingCat.{u})).obj A2)
      ((sheafCompose J3 (forget₂ CommRingCat.{u} RingCat.{u})).obj A3))
    (Rf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)))
    (Rg : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J2 (forget₂ CommRingCat.{u} RingCat.{u})).obj A2)))
    (Rh : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J2 (forget₂ CommRingCat.{u} RingCat.{u})).obj A2)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J3 (forget₂ CommRingCat.{u} RingCat.{u})).obj A3)))
    (Rgf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J2 (forget₂ CommRingCat.{u} RingCat.{u})).obj A2)))
    (Rhg : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J3 (forget₂ CommRingCat.{u} RingCat.{u})).obj A3)))
    (Rhgf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J3 (forget₂ CommRingCat.{u} RingCat.{u})).obj A3)))
    (ηf : (f.modules).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rf)
    (ηg : (g.modules).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rg)
    (ηh : (h.modules).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rh)
    (ηgf : (f.modules ⋙ g.modules).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rgf)
    (ηhg : (g.modules ⋙ h.modules).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rhg)
    (ηhgf : ((f.modules ⋙ g.modules) ⋙ h.modules).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rhgf)
    [hRf : Rf.IsRightDerivedFunctor ηf
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) (.up ℤ))]
    [hRg : Rg.IsRightDerivedFunctor ηg
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)) (.up ℤ))]
    [hRh : Rh.IsRightDerivedFunctor ηh
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J2 (forget₂ CommRingCat.{u} RingCat.{u})).obj A2)) (.up ℤ))]
    [hRgf : Rgf.IsRightDerivedFunctor ηgf
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) (.up ℤ))]
    [hRhg : Rhg.IsRightDerivedFunctor ηhg
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)) (.up ℤ))]
    [hRhgf : Rhgf.IsRightDerivedFunctor ηhgf
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) (.up ℤ))]
    (κgf : Rgf ≅ Rf ⋙ Rg) (κhg : Rhg ≅ Rg ⋙ Rh)
    (κh_gf : Rhgf ≅ Rgf ⋙ Rh) (κhg_f : Rhgf ≅ Rf ⋙ Rhg)
    (hκgf : ∀ M : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ℤ,
      ηgf.app M ≫ κgf.hom.app (DerivedCategory.Q.{w}.obj M) =
        ηg.app (((f.modules).mapHomologicalComplex (.up ℤ)).obj M) ≫
          Rg.map (ηf.app M))
    (hκhg : ∀ M : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)) ℤ,
      ηhg.app M ≫ κhg.hom.app (DerivedCategory.Q.{w}.obj M) =
        ηh.app (((g.modules).mapHomologicalComplex (.up ℤ)).obj M) ≫
          Rh.map (ηg.app M))
    (hκh_gf : ∀ M : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ℤ,
      ηhgf.app M ≫ κh_gf.hom.app (DerivedCategory.Q.{w}.obj M) =
        ηh.app (((f.modules ⋙ g.modules).mapHomologicalComplex (.up ℤ)).obj M) ≫
          Rh.map (ηgf.app M))
    (hκhg_f : ∀ M : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ℤ,
      ηhgf.app M ≫ κhg_f.hom.app (DerivedCategory.Q.{w}.obj M) =
        ηhg.app (((f.modules).mapHomologicalComplex (.up ℤ)).obj M) ≫
          Rhg.map (ηf.app M))

include hRf hRg hRh hRgf hRhg hRhgf hκgf hκhg hκh_gf hκhg_f

/-- Both triple paths and each of their factors, in the same canonical coordinates.
Source: Stacks Tags 0D6E, 070I and 070Y
(blueprint: lem-pur-ringed-triple-resolution-formulas).

The section variables spell out the node's chosen derived functors and normalized
comparisons. The four hκ equations are the dependency's unit normalization, not
additional coherence assumptions. The inverse equations specify a, v, b, s, m, r, d
as the coordinates in proof step 4, inside `Functor.HasTripleResolutionFormulas`.
That real-data predicate is unfolded to read the complete conclusion.
Homotopy-category equality is chain homotopy;
`kInjectiveHomotopyImage` applies h_* degreewise to a class, then localizes.

Proof, following the eight steps of the DAG:
1. Small ringed-site module categories admit K-injective resolutions by
   prop-pur-kinjective-resolutions-exist. The units evaluate invertibly on
   K-injectives by def-sfb-right-derived-functor. Put B=g_*f_*I, C=g_*J.
2. The normalized (f,g) comparison makes p=g_*j a quasi-isomorphism;
   w=p followed by k is one too (lem-weil-pbc-ringed-topoi-derived-pushforward-composition).
3. The Hom bijection into K gives the unique class u with Qu=Qw(Qt)^{-1}.
   The same bijection with source B gives t followed by u homotopic to w
   (lem-weil-pbc-kinjective-hom-derived).
4. Form a=(Qj)e_f, v=e_gf, b=e_g R_g(a), s=e_hgf,
   m=e_h R_h(Qt v), r=e_hg R_hg(a), d=e_h R_h(Qk b).
   The displayed inverse equations are these definitions in Lean's order.
5. Normalization for (gf,h) gives the first factor Q(h_*t).
6. Apply lem-sf-kinjective-derived-map-computation to Qp with resolutions t,k.
   The unique lift is u, giving the second factor Q(h_*u). Multiply to get alpha.
7. Normalization for (f,hg), then (g,h), and naturality along a give the two
   beta factors Q(h_*g_*j), Q(h_*k); multiply in exactly the same s,d coordinates.
8. All choices were arbitrary. Changing t gives the canonical intermediate
   transition computed by the map-computation node. Simultaneously changing
   j,k gives the canonical target transition computed from b inverse followed
   by b'. These are isomorphisms, obey the cocycle law, and conjugate each
   factor (the intermediate transitions cancel) and each full path. No direct
   image is required to preserve K-injectives. -/
theorem ringedTripleResolution_formulas
    (I : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J0 (forget₂ CommRingCat.{u} RingCat.{u})).obj A0)) ℤ) [I.IsKInjective]
    (J : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J1 (forget₂ CommRingCat.{u} RingCat.{u})).obj A1)) ℤ) [J.IsKInjective]
    (K T : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J2 (forget₂ CommRingCat.{u} RingCat.{u})).obj A2)) ℤ) [K.IsKInjective]
          [T.IsKInjective]
    (j : (f.modules.mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso j]
    (k : (g.modules.mapHomologicalComplex (.up ℤ)).obj J ⟶ K) [QuasiIso k]
    (t : ((g.modules.mapHomologicalComplex (.up ℤ)).obj ((f.modules.mapHomologicalComplex (.up
          ℤ)).obj I)) ⟶ T) [QuasiIso t] :
    Functor.HasTripleResolutionFormulas f.modules g.modules h.modules
      Rf Rg Rh Rgf Rhg Rhgf ηf ηg ηh ηgf ηhg ηhgf κgf κhg κh_gf κhg_f
      I J K T j k t := by
  have := (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
    J0 A0).1
  have := (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
    J1 A1).1
  have := (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
    J2 A2).1
  exact Functor.triple_formulas f.modules g.modules h.modules
    Rf Rg Rh Rgf Rhg Rhgf ηf ηg ηh ηgf ηhg ηhgf κgf κhg κh_gf κhg_f
    hκgf hκhg hκh_gf hκhg_f I J K T j k t

end CategoryTheory
