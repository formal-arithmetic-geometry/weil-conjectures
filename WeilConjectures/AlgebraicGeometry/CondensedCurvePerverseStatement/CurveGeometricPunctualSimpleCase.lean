/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPerverseSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverse.CondensedCurvePerverseStatement
public import WeilConjectures.AlgebraicGeometry.CurvePunctual.CurvePunctualSupport
public import WeilConjectures.AlgebraicGeometry.AffineLineConventions.AffineLineConventions
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstructibleTruncations
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.CategoryTheory.Simple

import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverseStatement.CurvePunctualSheafClassification
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import Mathlib.CategoryTheory.Abelian.Subcategory

/-!
# Geometric punctual perverse simple objects

Source: latest blueprint, `prop-a1-curve-perverse-simples.proof.md`, punctual simplicity and the
punctual classification case.
(blueprint: lem-a1-geometric-punctual-simple-case).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCurvePerverseStatement

private theorem simple_of_simple_homology
    {A H : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category H] [HasZeroMorphisms H]
    (I : H ⥤ DerivedCategory A) [I.Full] [I.Faithful] [I.PreservesZeroMorphisms]
    (S : ObjectProperty A)
    (hcon : ∀ X : H, S ((DerivedCategory.homologyFunctor A 0).obj (I.obj X)))
    (hle : ∀ X : H, (I.obj X).IsLE 0)
    (P : H) (hge : (I.obj P).IsGE 0)
    (hmono : ∀ {X : H} (f : X ⟶ P), Mono f →
      (I.obj X).IsGE 0 ∧ Mono ((DerivedCategory.homologyFunctor A 0).map (I.map f)))
    (hP : Simple (⟨(DerivedCategory.homologyFunctor A 0).obj (I.obj P), hcon P⟩ :
      S.FullSubcategory)) : Simple P := by
  let K := DerivedCategory.homologyFunctor A 0
  have hfaith {X Y : H} (hy : (I.obj Y).IsGE 0) {f g : X ⟶ Y}
      (h : K.map (I.map f) = K.map (I.map g)) : f = g := by
    have := hle X
    have := hy
    apply I.map_injective
    exact (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE 0).1 h
  constructor
  intro X f hf
  have := hf
  obtain ⟨hx, hfm⟩ := hmono f hf
  have := hfm
  let f0 : (⟨K.obj (I.obj X), hcon X⟩ : S.FullSubcategory) ⟶
      ⟨K.obj (I.obj P), hcon P⟩ := ObjectProperty.homMk (K.map (I.map f))
  have : Mono f0 := S.ι.mono_of_mono_map (by dsimp [f0]; infer_instance)
  constructor
  · intro hisof hzero
    have hf0iso : IsIso f0 := by
      apply (ObjectProperty.isIso_hom_iff f0).mp
      change IsIso (K.map (I.map f))
      infer_instance
    apply (Simple.mono_isIso_iff_nonzero f0).mp hf0iso
    apply ObjectProperty.hom_ext
    simp [f0, hzero]
  · intro hne
    have hf0ne : f0 ≠ 0 := by
      intro hz
      apply hne
      apply hfaith hge
      simpa [f0] using congrArg (fun z ↦ z.hom) hz
    have hf0iso : IsIso f0 := (Simple.mono_isIso_iff_nonzero f0).mpr hf0ne
    have hiso : IsIso (I.map f) := by
      apply (DerivedCategory.isIso_iff A _).mpr
      intro n
      by_cases hn : n = 0
      · subst n
        exact S.ι.map_isIso f0
      · have hX : IsZero ((DerivedCategory.homologyFunctor A n).obj (I.obj X)) := by
          rcases lt_or_gt_of_ne hn with hn | hn
          · exact (DerivedCategory.isGE_iff _ 0).mp hx n hn
          · exact (DerivedCategory.isLE_iff _ 0).mp (hle X) n hn
        have hY : IsZero ((DerivedCategory.homologyFunctor A n).obj (I.obj P)) := by
          rcases lt_or_gt_of_ne hn with hn | hn
          · exact (DerivedCategory.isGE_iff _ 0).mp hge n hn
          · exact (DerivedCategory.isLE_iff _ 0).mp (hle P) n hn
        exact isIso_of_source_target_iso_zero _ hX.isoZero hY.isoZero
    exact isIso_of_fully_faithful I f


private theorem simple_homology_of_simple
    {A H : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category H] [HasZeroMorphisms H]
    (I : H ⥤ DerivedCategory A) [I.Full] [I.Faithful] [I.PreservesZeroMorphisms]
    (S : ObjectProperty A) [S.ι.PreservesMonomorphisms]
    (hcon : ∀ X : H, S ((DerivedCategory.homologyFunctor A 0).obj (I.obj X)))
    (hle : ∀ X : H, (I.obj X).IsLE 0)
    (P : H) (hge : (I.obj P).IsGE 0)
    (hlift : ∀ (M : S.FullSubcategory)
      (f : M ⟶ ⟨(DerivedCategory.homologyFunctor A 0).obj (I.obj P), hcon P⟩),
      Mono f → ∃ X : H, (I.obj X).IsGE 0 ∧
        Nonempty ((DerivedCategory.homologyFunctor A 0).obj (I.obj X) ≅ M.obj))
    [Simple P] :
    Simple (⟨(DerivedCategory.homologyFunctor A 0).obj (I.obj P), hcon P⟩ :
      S.FullSubcategory) := by
  let K := DerivedCategory.homologyFunctor A 0
  have hfaith {X Y : H} (hy : (I.obj Y).IsGE 0) {f g : X ⟶ Y}
      (h : K.map (I.map f) = K.map (I.map g)) : f = g := by
    have := hle X
    have := hy
    apply I.map_injective
    exact (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE 0).1 h
  constructor
  intro M f hf
  have := hf
  obtain ⟨X, hx, ⟨e⟩⟩ := hlift M f hf
  have := hle X
  have := hge
  obtain ⟨g, hg⟩ :=
    (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE
      (X := I.obj X) (Y := I.obj P) 0).2 (e.hom ≫ f.hom)
  let q : X ⟶ P := I.preimage g
  have hq : K.map (I.map q) = e.hom ≫ f.hom := by simpa [q] using hg
  have hfmono : Mono f.hom := S.ι.map_mono f
  have hqmono : Mono (K.map (I.map q)) := by rw [hq]; infer_instance
  have : Mono q := by
    constructor
    intro Z a b hab
    apply hfaith hx
    apply (cancel_mono (K.map (I.map q))).mp
    simp only [← K.map_comp, ← I.map_comp, hab]
  constructor
  · intro hiso hz
    have hqzero : q = 0 := by
      apply hfaith hge
      simp only [hq, hz, ObjectProperty.zero_hom, comp_zero,
        Functor.map_zero]
    exact ((Simple.mono_isIso_iff_nonzero q).mp (by
      have : IsIso (K.map (I.map q)) := by rw [hq]; infer_instance
      have hqi : IsIso (I.map q) := by
        apply (DerivedCategory.isIso_iff A _).mpr
        intro n
        by_cases hn : n = 0
        · subst n; infer_instance
        · have zx : IsZero ((DerivedCategory.homologyFunctor A n).obj (I.obj X)) := by
            rcases lt_or_gt_of_ne hn with hn | hn
            · exact (DerivedCategory.isGE_iff _ 0).mp hx n hn
            · exact (DerivedCategory.isLE_iff _ 0).mp (hle X) n hn
          have zy : IsZero ((DerivedCategory.homologyFunctor A n).obj (I.obj P)) := by
            rcases lt_or_gt_of_ne hn with hn | hn
            · exact (DerivedCategory.isGE_iff _ 0).mp hge n hn
            · exact (DerivedCategory.isLE_iff _ 0).mp (hle P) n hn
          exact isIso_of_source_target_iso_zero _ zx.isoZero zy.isoZero
      exact isIso_of_fully_faithful I q)) hqzero
  · intro hne
    have hqne : q ≠ 0 := by
      intro hzero
      apply hne
      apply ObjectProperty.hom_ext
      have hz : e.hom ≫ f.hom = 0 := by simpa [hzero] using hq.symm
      exact (cancel_epi e.hom).mp (by simpa using hz)
    have : IsIso q := isIso_of_mono_of_nonzero hqne
    have hfiso : IsIso f.hom := by
      have hcomp : IsIso (e.hom ≫ f.hom) := by rw [← hq]; infer_instance
      have : IsIso (e.inv ≫ (e.hom ≫ f.hom)) := inferInstance
      simpa using this
    exact (ObjectProperty.isIso_hom_iff f).mp hfiso




private theorem punctual_sequence
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (Q : ObjectProperty (DerivedCategory A))
    (le ge : ObjectProperty Q.FullSubcategory)
    (C p : ObjectProperty A)
    (hcon : ∀ (P : (le ⊓ ge).FullSubcategory) n,
      C ((DerivedCategory.homologyFunctor A n).obj P.obj.obj))
    (hclosed : ∀ {M N : A} (f : M ⟶ N), Mono f → C M → p N → p M)
    (hheart : ∀ P : (le ⊓ ge).FullSubcategory,
      p ((DerivedCategory.homologyFunctor A 0).obj P.obj.obj) ∧
      (∀ G, ∀ i : G ⟶ ((DerivedCategory.homologyFunctor A (-1)).obj P.obj.obj),
        Mono i → p G → IsZero G))
    (hsix : ∀ S : ShortComplex (le ⊓ ge).FullSubcategory, S.ShortExact →
      ∃ d : ((DerivedCategory.homologyFunctor A (-1)).obj S.X₃.obj.obj) ⟶
          ((DerivedCategory.homologyFunctor A 0).obj S.X₁.obj.obj),
        Mono ((DerivedCategory.homologyFunctor A (-1)).map S.f.hom.hom) ∧
        (ComposableArrows.mk₂
          ((DerivedCategory.homologyFunctor A (-1)).map S.g.hom.hom) d).Exact ∧
        (ComposableArrows.mk₂ d
          ((DerivedCategory.homologyFunctor A 0).map S.f.hom.hom)).Exact)
    (S : ShortComplex (le ⊓ ge).FullSubcategory) (hS : S.ShortExact)
    (hmid : IsZero ((DerivedCategory.homologyFunctor A (-1)).obj S.X₂.obj.obj)) :
    IsZero ((DerivedCategory.homologyFunctor A (-1)).obj S.X₁.obj.obj) ∧
      IsZero ((DerivedCategory.homologyFunctor A (-1)).obj S.X₃.obj.obj) ∧
      Mono ((DerivedCategory.homologyFunctor A 0).map S.f.hom.hom) := by
  obtain ⟨d, hmono, hex₁, hex₂⟩ := hsix S hS
  have := hmono
  have hleft := IsZero.of_mono
    ((DerivedCategory.homologyFunctor A (-1)).map S.f.hom.hom) hmid
  have hd : Mono d := (hex₁.exact 0).mono_g (hmid.eq_of_src _ _)
  have hright := (hheart S.X₃).2 _ (𝟙 _) inferInstance
    (hclosed d hd (hcon S.X₃ (-1)) (hheart S.X₁).1)
  exact ⟨hleft, hright, (hex₂.exact 0).mono_g (hright.eq_of_src _ _)⟩



private theorem support_mono {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (f : M ⟶ N) [Mono f] :
    CondensedRing.condensedModuleSupport R M ⊆ CondensedRing.condensedModuleSupport R N := by
  apply closure_mono
  intro x hx hn
  apply hx
  have : Mono f.hom := (Mod.forget R).map_mono f
  have : Mono f.hom.hom := (sheafToPresheaf _ _).map_mono f.hom
  have (V : (Scheme.ProEtaleGeometricNeighbourhood (X.algClosurePoint x))ᵒᵖ) :
      Mono ((Functor.whiskerLeft
        (Scheme.proEtaleGeometricNeighbourhoodForget (X.algClosurePoint x)).op f.hom.hom).app V) :=
    ((evaluation _ _).obj
      ((Scheme.proEtaleGeometricNeighbourhoodForget (X.algClosurePoint x)).op.obj V)).map_mono _
  have : Mono (Functor.whiskerLeft
      (Scheme.proEtaleGeometricNeighbourhoodForget (X.algClosurePoint x)).op f.hom.hom) :=
    NatTrans.mono_of_mono_app _
  have : Mono (colim.map (Functor.whiskerLeft
      (Scheme.proEtaleGeometricNeighbourhoodForget (X.algClosurePoint x)).op f.hom.hom)) :=
    inferInstance
  exact IsZero.of_mono (colim.map (Functor.whiskerLeft
    (Scheme.proEtaleGeometricNeighbourhoodForget (X.algClosurePoint x)).op f.hom.hom)) hn


private theorem geometric_punctual_subobjects
    (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (C : Over (Spec (.of k))) [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
    [IsSeparated C.hom] [Smooth C.hom] (hPure : Scheme.IsPureDimension C.left 1)
    (S : ShortComplex (CondensedRing.FiniteOrClosedPerverseLEZero ell hk C ⊓
      CondensedRing.FiniteOrClosedPerverseGEZero ell hk C).FullSubcategory)
    (hS : S.ShortExact)
    (hmid : IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj S.X₂.obj.obj)) :
    IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj S.X₁.obj.obj) ∧
      IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj S.X₃.obj.obj) ∧
      Mono ((DerivedCategory.homologyFunctor _ 0).map S.f.hom.hom) := by
  let R := condensedRingObj (Profinite.padicAlgClRingObj ell) C.left
  have h := CondensedRing.curveSupportHeart ell hk C hPure
  let H := (CondensedRing.FiniteOrClosedPerverseLEZero ell hk C ⊓
    CondensedRing.FiniteOrClosedPerverseGEZero ell hk C).FullSubcategory
  have hheart (P : H) :
      CurvePunctual.IsPunctual ell C.left
        ((DerivedCategory.homologyFunctor _ 0).obj P.obj.obj) ∧
      CurvePunctual.HasNoPunctualSubsheaf ell C.left
        ((DerivedCategory.homologyFunctor _ (-1)).obj P.obj.obj) :=
    ((h.2.1.2.2 P.obj).mp P.property).2
  apply punctual_sequence _ _ _ (IsConstructibleModuleObject R)
    (CurvePunctual.IsPunctual ell C.left)
    (fun P n ↦ P.obj.property.2 n) ?_ hheart ?_ S hS hmid
  · intro M N f hf hM hN
    have := hf
    have hs := support_mono R f
    exact ⟨hM, hN.2.1.subset hs, fun x hx ↦ hN.2.2 x (hs hx)⟩
  · intro S hS
    obtain ⟨d, hT, hm, he, h₀, h₁, h₂, h₃⟩ := h.2.2.2.2 S hS
    exact ⟨_, hm, h₁, h₂⟩


private theorem geometric_simple_of_H0_simple
    (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (C : Over (Spec (.of k))) [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
    [IsSeparated C.hom] [Smooth C.hom] (hPure : Scheme.IsPureDimension C.left 1)
    (P : (CondensedRing.FiniteOrClosedPerverseLEZero ell hk C ⊓
      CondensedRing.FiniteOrClosedPerverseGEZero ell hk C).FullSubcategory)
    (hneg : IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj P.obj.obj))
    (hsimple : Simple
      (⟨(DerivedCategory.homologyFunctor _ 0).obj P.obj.obj, P.obj.property.2 0⟩ :
        ObjectProperty.FullSubcategory (IsConstructibleModuleObject
          (condensedRingObj (Profinite.padicAlgClRingObj ell) C.left)))) :
    Simple P := by
  let R := condensedRingObj (Profinite.padicAlgClRingObj ell) C.left
  let Q := boundedConstructible R
  let H := (CondensedRing.FiniteOrClosedPerverseLEZero ell hk C ⊓
    CondensedRing.FiniteOrClosedPerverseGEZero ell hk C).FullSubcategory
  let I : H ⥤ DerivedCategory _ := ObjectProperty.ι _ ⋙ ObjectProperty.ι Q
  have h := CondensedRing.curveSupportHeart ell hk C hPure
  obtain ⟨ha⟩ := h.2.1.2.1
  have heq : @Preadditive.preadditiveHasZeroMorphisms H _ ha.toPreadditive =
      (inferInstance : HasZeroMorphisms H) := Subsingleton.elim _ _
  let : HasCokernels H := (congrArg (fun z : HasZeroMorphisms H ↦ @HasCokernels H _ z) heq).mp
    (@Abelian.has_cokernels H _ ha)
  let : CategoryWithHomology H :=
    (congrArg (fun z : HasZeroMorphisms H ↦ @CategoryWithHomology H _ z) heq).mp
    (@categoryWithHomology_of_abelian H _ ha)
  have hle (X : H) : (I.obj X).IsLE 0 := by
    apply (DerivedCategory.isLE_iff _ 0).mpr
    exact ((h.1.1 X.obj).mp X.property.1).1
  have hge (X : H)
      (hz : IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj X.obj.obj)) :
      (I.obj X).IsGE 0 := by
    apply (DerivedCategory.isGE_iff _ 0).mpr
    intro n hn
    by_cases he : n = -1
    · subst n; exact hz
    · exact ((h.1.2 X.obj).mp X.property.2).1 n (by omega)
  apply simple_of_simple_homology I (IsConstructibleModuleObject R)
    (fun X ↦ X.obj.property.2 0) hle P (hge P hneg) ?_ hsimple
  intro X f hf
  have := hf
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel f) }
  have hseq := geometric_punctual_subobjects ell hk C hPure S hS hneg
  exact ⟨hge X hseq.1, hseq.2.2⟩


private theorem geometric_H0_simple_of_simple
    (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (C : Over (Spec (.of k))) [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
    [IsSeparated C.hom] [Smooth C.hom] (hPure : Scheme.IsPureDimension C.left 1)
    (P : (CondensedRing.FiniteOrClosedPerverseLEZero ell hk C ⊓
      CondensedRing.FiniteOrClosedPerverseGEZero ell hk C).FullSubcategory)
    (hneg : IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj P.obj.obj))
    [Simple P] : Simple
      (⟨(DerivedCategory.homologyFunctor _ 0).obj P.obj.obj, P.obj.property.2 0⟩ :
        ObjectProperty.FullSubcategory (IsConstructibleModuleObject
          (condensedRingObj (Profinite.padicAlgClRingObj ell) C.left))) := by
  let R := condensedRingObj (Profinite.padicAlgClRingObj ell) C.left
  let Q := boundedConstructible R
  let S : ObjectProperty
      (CondensedCurvePerverse.Modules (Profinite.padicAlgClRingObj ell) C.left) :=
    IsConstructibleModuleObject R
  let H := (CondensedRing.FiniteOrClosedPerverseLEZero ell hk C ⊓
    CondensedRing.FiniteOrClosedPerverseGEZero ell hk C).FullSubcategory
  let I : H ⥤ DerivedCategory _ := ObjectProperty.ι _ ⋙ ObjectProperty.ι Q
  have h := CondensedRing.curveSupportHeart ell hk C hPure
  have hle (X : H) : (I.obj X).IsLE 0 := by
    apply (DerivedCategory.isLE_iff _ 0).mpr
    exact ((h.1.1 X.obj).mp X.property.1).1
  have hge : (I.obj P).IsGE 0 := by
    apply (DerivedCategory.isGE_iff _ 0).mpr
    intro n hn
    by_cases he : n = -1
    · subst n; exact hneg
    · exact ((h.1.2 P.obj).mp P.property.2).1 n (by omega)
  have hzero : IsZero ((DerivedCategory.homologyFunctor _ 1).obj P.obj.obj) :=
    ((DerivedCategory.isLE_iff _ 0).mp (hle P)) 1 (by decide)
  let : S.ContainsZero := ⟨_, hzero, P.obj.property.2 1⟩
  let : S.IsClosedUnderIsomorphisms := ⟨fun e he ↦ he.of_iso e⟩
  have hkern := (isConstructibleModuleObject_serre_padicAlgCl C.left ell).1
  let : S.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, c, hc, hf⟩
    exact ((hkern _ _ f hf.1 hf.2).1).of_iso (limit.isoLimitCone ⟨c, hc⟩)⟩
  let := S.preservesMonomorphisms_ι_of_isNormalEpiCategory
  have hclosed {M N : CondensedCurvePerverse.Modules (Profinite.padicAlgClRingObj ell) C.left}
      (f : M ⟶ N) [Mono f] (hc : S M)
      (hp : CurvePunctual.IsPunctual ell C.left N) :
      CurvePunctual.IsPunctual ell C.left M := by
    have hs := support_mono R f
    exact ⟨hc, hp.2.1.subset hs, fun x hx ↦ hp.2.2 x (hs hx)⟩
  apply simple_homology_of_simple I S (fun X ↦ X.obj.property.2 0) hle P hge
  intro M f hf
  have := hf
  have : Mono f.hom := S.ι.map_mono f
  have hpunM := hclosed f.hom M.property
    ((h.2.1.2.2 P.obj).mp P.property).2.1
  let K := (DerivedCategory.singleFunctor _ 0).obj M.obj
  have hK : Q K := by
    refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩
    intro n
    by_cases hn : n = 0
    · subst n
      exact S.prop_of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app
        M.obj).symm M.property
    · apply S.prop_of_isZero
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact DerivedCategory.isZero_of_isGE _ 0 n hn
      · exact DerivedCategory.isZero_of_isLE _ 0 n hn
  have hmem : CondensedRing.FiniteOrClosedPerverseLEZero ell hk C ⟨K, hK⟩ ∧
      CondensedRing.FiniteOrClosedPerverseGEZero ell hk C ⟨K, hK⟩ := by
    apply (h.2.1.2.2 ⟨K, hK⟩).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro n hn hn0
      rcases lt_or_gt_of_ne hn0 with hn0 | hn0
      · exact DerivedCategory.isZero_of_isGE _ 0 n hn0
      · exact DerivedCategory.isZero_of_isLE _ 0 n hn0
    · let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M.obj
      have : Mono e.hom := inferInstance
      exact hclosed e.hom (hK.2 0) hpunM
    · intro G i hi hp
      have := hi
      exact IsZero.of_mono i (DerivedCategory.isZero_of_isGE K 0 (-1) (by decide))
  refine ⟨⟨⟨K, hK⟩, hmem⟩, ?_,
    ⟨(DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M.obj⟩⟩
  change K.IsGE 0
  dsimp [K]
  infer_instance


private theorem geometric_punctual_iso_H0
    (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (C : Over (Spec (.of k))) [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
    [IsSeparated C.hom] [Smooth C.hom] (hPure : Scheme.IsPureDimension C.left 1)
    (P : (CondensedRing.FiniteOrClosedPerverseLEZero ell hk C ⊓
      CondensedRing.FiniteOrClosedPerverseGEZero ell hk C).FullSubcategory)
    (hneg : IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj P.obj.obj)) :
    Nonempty (P.obj.obj ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((DerivedCategory.homologyFunctor _ 0).obj P.obj.obj)) := by
  have h := CondensedRing.curveSupportHeart ell hk C hPure
  have : P.obj.obj.IsLE 0 := (DerivedCategory.isLE_iff _ 0).mpr
    (((h.1.1 P.obj).mp P.property.1).1)
  have : P.obj.obj.IsGE 0 := by
    apply (DerivedCategory.isGE_iff _ 0).mpr
    intro n hn
    by_cases he : n = -1
    · subst n; exact hneg
    · exact ((h.1.2 P.obj).mp P.property.2).1 n (by omega)
  obtain ⟨M, ⟨e⟩⟩ := P.obj.obj.exists_iso_singleFunctor_obj_of_isGE_of_isLE 0
  let eM := (DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso eM.symm⟩


/-- The classification in the pure degree-zero case.
Source: latest blueprint, `prop-a1-curve-perverse-simples.proof.md`, punctual simplicity and the
punctual classification case.
Proof: The heart description and the vanishing of H^-1 identify P with G[0],
where G = H^0 P is constructible and has finite closed support. For a subobject of
G[0] in the perverse heart, the six-term ordinary cohomology sequence makes its
negative-degree term zero. The next term injects into its punctual H^0 and is
therefore punctual; absence of punctual subsheaves forces it to vanish. Thus these
perverse subobjects are exactly the constructible sheaf subobjects of G.
Localization on the finite support decomposes G into the direct images of its
restrictions at the closed points. Simplicity selects one nonzero summand and makes
its residue-field sheaf irreducible. Conversely closed direct image is exact and
fully faithful on supported sheaves, so irreducibility at the point gives simplicity
among sheaf subobjects, hence among perverse subobjects. The zero object satisfies
neither simplicity nor the displayed irreducible-point alternative.
(blueprint: lem-a1-geometric-punctual-simple-case). -/
theorem geometric_punctual_simple_case
    (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (C : Over (Spec (.of k))) [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
    [IsSeparated C.hom] [Smooth C.hom] (_hPure : Scheme.IsPureDimension C.left 1)
    (P : (CondensedRing.FiniteOrClosedPerverseLEZero ell hk C ⊓
      CondensedRing.FiniteOrClosedPerverseGEZero ell hk C).FullSubcategory)
    (_hCoh : IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj P.obj.obj)) :
    Simple P ↔
  ∃ (x : C.left), IsClosed ({x} : Set C.left) ∧
    ∃ (E : CondensedCurvePerverse.Modules (Profinite.padicAlgClRingObj ell)
        (Spec (C.left.residueField x)))
      (hE : IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicAlgClRingObj ell)
          (Spec (C.left.residueField x))) E),
      Simple (⟨E, hE⟩ : ObjectProperty.FullSubcategory
        (IsConstructibleModuleObject
          (condensedRingObj (Profinite.padicAlgClRingObj ell)
            (Spec (C.left.residueField x)))) ) ∧
      Nonempty (P.obj.obj ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ell)
            (C.left.fromSpecResidueField x)).obj E)) := by
  have h := CondensedRing.curveSupportHeart ell hk C _hPure
  have hpunc := ((h.2.1.2.2 P.obj).mp P.property).2.1
  have hcase := punctual_sheaf_classification ell C.left
    ((DerivedCategory.homologyFunctor _ 0).obj P.obj.obj) hpunc
  obtain ⟨eP⟩ := geometric_punctual_iso_H0 ell hk C _hPure P _hCoh
  constructor
  · intro hsimple
    have := hsimple
    have h0 := geometric_H0_simple_of_simple ell hk C _hPure P _hCoh
    obtain ⟨x, hx, E, hE, hsimpleE, ⟨e⟩⟩ := hcase.mp h0
    exact ⟨x, hx, E, hE, hsimpleE,
      ⟨eP ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e⟩⟩
  · intro htype
    apply geometric_simple_of_H0_simple ell hk C _hPure P _hCoh
    apply hcase.mpr
    obtain ⟨x, hx, E, hE, hsimpleE, ⟨e⟩⟩ := htype
    exact ⟨x, hx, E, hE, hsimpleE,
      ⟨(DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _⟩⟩

end AlgebraicGeometry.ProEtale.CondensedCurvePerverseStatement
