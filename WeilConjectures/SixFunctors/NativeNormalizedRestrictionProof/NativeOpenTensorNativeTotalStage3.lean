/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorDescentData
public import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-! Native total restriction data for open tensor descent.
(blueprint: new-sf-native-open-tensor-total-stage3) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits Opposite
universe u a b
namespace NativeNormalizedRestrictionProof

/-- A total restriction comparison together with its summand equation. -/
structure TotalDataCore
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    [c.R.PreservesZeroMorphisms]
    (sr : c.SB ⋙ c.R ≅ c.R.prod c.R ⋙ c.SA) where
  total : Functor.uncurry.obj c.TB ⋙ c.R.mapHomologicalComplex (.up ℤ) ≅
    (c.R.mapHomologicalComplex (.up ℤ)).prod (c.R.mapHomologicalComplex (.up ℤ)) ⋙
      Functor.uncurry.obj c.TA
  summands : ∀ P T (p q n : ℤ) (h : p + q = n),
    c.R.map (m.iB P T p q n h) ≫ (total.hom.app (P, T)).f n =
      sr.hom.app (P.X p, T.X q) ≫
        m.iA ((c.R.mapHomologicalComplex (.up ℤ)).obj P)
          ((c.R.mapHomologicalComplex (.up ℤ)).obj T) p q n h

@[irreducible] def TotalData
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    [c.R.PreservesZeroMorphisms]
    (sr : c.SB ⋙ c.R ≅ c.R.prod c.R ⋙ c.SA) : Type _ :=
  TotalDataCore c m sr

def totalDataMk
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    [c.R.PreservesZeroMorphisms]
    (sr : c.SB ⋙ c.R ≅ c.R.prod c.R ⋙ c.SA)
    (total : Functor.uncurry.obj c.TB ⋙ c.R.mapHomologicalComplex (.up ℤ) ≅
      (c.R.mapHomologicalComplex (.up ℤ)).prod (c.R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj c.TA)
    (summands : ∀ P T (p q n : ℤ) (h : p + q = n),
      c.R.map (m.iB P T p q n h) ≫ (total.hom.app (P, T)).f n =
        sr.hom.app (P.X p, T.X q) ≫
          m.iA ((c.R.mapHomologicalComplex (.up ℤ)).obj P)
            ((c.R.mapHomologicalComplex (.up ℤ)).obj T) p q n h) :
    TotalData c m sr := by
  unfold TotalData
  exact ⟨total, summands⟩

def totalData_total
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    [c.R.PreservesZeroMorphisms]
    (sr : c.SB ⋙ c.R ≅ c.R.prod c.R ⋙ c.SA)
    (d : TotalData c m sr) :
    Functor.uncurry.obj c.TB ⋙ c.R.mapHomologicalComplex (.up ℤ) ≅
      (c.R.mapHomologicalComplex (.up ℤ)).prod (c.R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj c.TA := by
  unfold TotalData at d
  exact d.total

theorem totalData_summands
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    [c.R.PreservesZeroMorphisms]
    (sr : c.SB ⋙ c.R ≅ c.R.prod c.R ⋙ c.SA)
    (d : TotalData c m sr) : ∀ P T (p q n : ℤ) (h : p + q = n),
      c.R.map (m.iB P T p q n h) ≫
          ((totalData_total c m sr d).hom.app (P, T)).f n =
        sr.hom.app (P.X p, T.X q) ≫
          m.iA ((c.R.mapHomologicalComplex (.up ℤ)).obj P)
            ((c.R.mapHomologicalComplex (.up ℤ)).obj T) p q n h := by
  unfold TotalData at d
  exact d.summands

private theorem restrictionDataWithModels
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    [HasCountableCoproducts A] [HasCountableCoproducts B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    [c.R.PreservesZeroMorphisms] [c.R.Additive] [PreservesColimitsOfSize.{0, 0} c.R]
    (H : B ⥤ B ⥤ B) (H' : A ⥤ A ⥤ A)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    (hSA : c.SA = Functor.uncurry.obj H') (hSB : c.SB = Functor.uncurry.obj H)
    (hTA : c.TA = H'.map₂CochainComplex) (hTB : c.TB = H.map₂CochainComplex)
    (hiA : HEq m.iA (fun (P T : CochainComplex A ℤ) p q n h ↦
      HomologicalComplex.ιMapBifunctor P T H' (.up ℤ) p q n h))
    (hiB : HEq m.iB (fun (P T : CochainComplex B ℤ) p q n h ↦
      HomologicalComplex.ιMapBifunctor P T H (.up ℤ) p q n h))
    (sr : c.SB ⋙ c.R ≅ c.R.prod c.R ⋙ c.SA) :
    Nonempty (NativeNormalizedRestrictionProof.TotalData c m sr) := by
  rcases c with @⟨E, R, ea, ra, el, ec, rl, rc, ez, rz, SA, SB, TA, TB, DA, DB, fA, fB⟩
  dsimp only at hSA hSB hTA hTB
  subst SA
  subst SB
  subst TA
  subst TB
  obtain ⟨e, he⟩ := restrictionTotalWithSummands R H H' sr
  refine ⟨NativeNormalizedRestrictionProof.totalDataMk _ m sr e ?_⟩
  intro P T p q n h
  dsimp only [Functor.uncurry_obj_obj, Functor.map₂CochainComplex,
    Functor.map₂HomologicalComplex] at hiA hiB
  rw [eq_of_heq hiA, eq_of_heq hiB]
  exact he P T p q n h

private theorem restrictionTotalWithSummands
    {A B : Type a} [Category.{b} A] [Category.{b} B]
    [Preadditive A] [Preadditive B] [HasCountableCoproducts A] [HasCountableCoproducts B]
    (R : B ⥤ A) [R.Additive] [PreservesColimitsOfSize.{0, 0} R]
    (H : B ⥤ B ⥤ B) (H' : A ⥤ A ⥤ A)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    (r : Functor.uncurry.obj H ⋙ R ≅ R.prod R ⋙ Functor.uncurry.obj H') :
    ∃ e : Functor.uncurry.obj H.map₂CochainComplex ⋙
        R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj H'.map₂CochainComplex,
      ∀ P T (p q n : ℤ) (h : p + q = n),
        R.map (HomologicalComplex.ιMapBifunctor P T H (.up ℤ) p q n h) ≫
            (e.hom.app (P, T)).f n =
          r.hom.app (P.X p, T.X q) ≫
            HomologicalComplex.ιMapBifunctor
              ((R.mapHomologicalComplex (.up ℤ)).obj P)
              ((R.mapHomologicalComplex (.up ℤ)).obj T) H' (.up ℤ) p q n h := by
  let τ : (Functor.postcompose₂.obj R).obj H ≅
      (((Functor.whiskeringLeft₂ _).obj R).obj R).obj H' :=
    SheafOfModules.bifunctorIsoOfComponents _ _ (fun M N ↦ r.app (M, N)) (by
      intro M M' N N' a b
      change R.map ((H.map a).app N) ≫ R.map ((H.obj M').map b) ≫
          (r.app (M', N')).hom = (r.app (M, N)).hom ≫
          (H'.map (R.map a)).app (R.obj N) ≫ (H'.obj (R.obj M')).map (R.map b)
      simpa only [Functor.comp_map, Functor.comp_obj, Functor.prod_obj, Iso.app_hom,
        Functor.uncurry_obj_map, Functor.prod_map, Functor.map_comp, Category.assoc] using
          r.hom.naturality (Prod.mkHom a b))
  have hτ : ∀ M N, IsIso ((τ.hom.app M).app N) := by
    intro M N
    dsimp [τ]
    infer_instance
  let e : Functor.uncurry.obj H.map₂CochainComplex ⋙
        R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj H'.map₂CochainComplex :=
    NatIso.ofComponents
      (fun PQ ↦ by
        refine @asIso _ _ _ _
          (HomologicalComplex.mapBifunctorComparison τ.hom (.up ℤ) PQ.1 PQ.2) ?_
        apply HomologicalComplex.instIsIsoMapBifunctorComparisonOfAppFunctor)
      (by
        intro PQ PQ' fg
        simp only [Functor.comp_map, Functor.comp_obj, Functor.prod_obj,
          Functor.uncurry_obj_map, Functor.prod_map, SheafOfModules.map₂_map_eq]
        dsimp only [asIso, Functor.uncurry_obj_obj, Functor.map₂CochainComplex,
          Functor.map₂HomologicalComplex]
        exact HomologicalComplex.mapBifunctorComparison_naturality τ.hom (.up ℤ) fg.1 fg.2)
  refine ⟨e, ?_⟩
  intro P T p q n h
  have hh := HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    τ.hom (.up ℤ) P T p q n h
  dsimp only [e, NatIso.ofComponents, asIso, Functor.comp_obj,
    Functor.prod_obj, Functor.uncurry_obj_obj, Functor.map₂CochainComplex,
    Functor.map₂HomologicalComplex, Functor.mapHomologicalComplex] at hh ⊢
  simpa only [HomologicalComplex.mapBifunctorComparison_f,
    HomologicalComplex.mapBifunctorComparisonApp, τ,
    SheafOfModules.bifunctorIsoOfComponents_hom, Iso.app_hom] using hh

-- Transport the insertion families while all categorical inputs are abstract.

end NativeNormalizedRestrictionProof

namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local instance] OpenTensorDescentInput.r_add OpenTensorDescentInput.r_lim
  OpenTensorDescentInput.r_colim OpenTensorDescentInput.r_zero

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- The native total restriction comparison exists under the native model links.

Source: Stacks 012Z (totalization) and 07A4.
(blueprint: new-sf-native-open-tensor-total-stage3)

Proof: the native totals are `(nativeTensorBifunctor _ _ X).flip.map₂CochainComplex` and the
sheaf tensors are the uncurried same bifunctors. Restriction is a left adjoint, so it
preserves the coproducts over p+q=n; the total-bifunctor comparison applied to the
natural isomorphism sr gives a natural chain isomorphism, compatible with the signed
total differentials by naturality of sr in both variables. By hm the insertions of m are
the native ιMapBifunctor, so on the (p,q)-summand the comparison is sr followed by the
open insertion, which is the summand equation. -/
theorem totalComparisonStage3
    (s : NativeOpenTensorData k₀ l j)
    (m : OpenTensorDescentModels (nativeOpenTensorDescentInput k₀ l j))
    (hm : NativeOpenTensorModelsCompatibility k₀ l j s m)
    (sr : (nativeOpenTensorDescentInput k₀ l j).SB ⋙
      (nativeOpenTensorDescentInput k₀ l j).R ≅
      (nativeOpenTensorDescentInput k₀ l j).R.prod
        (nativeOpenTensorDescentInput k₀ l j).R ⋙
      (nativeOpenTensorDescentInput k₀ l j).SA) :
    Nonempty (NativeNormalizedRestrictionProof.TotalData
      (nativeOpenTensorDescentInput k₀ l j) m sr) := by
  let H := (nativeTensorBifunctor k₀ l Z).flip
  let H' := (nativeTensorBifunctor k₀ l U).flip
  let hH : H.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive H
  let hH' : H'.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive H'
  let hHM : ∀ M, (H.obj M).PreservesZeroMorphisms := fun M ↦
    Functor.preservesZeroMorphisms_of_additive (H.obj M)
  let hHM' : ∀ M, (H'.obj M).PreservesZeroMorphisms := fun M ↦
    Functor.preservesZeroMorphisms_of_additive (H'.obj M)
  exact @restrictionDataWithModels
    (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (nativeOpenTensorDescentInput k₀ l j) m
    (nativeOpenTensorDescentInput k₀ l j).r_zero
    (nativeOpenTensorDescentInput k₀ l j).r_add
    (by
      dsimp only [nativeOpenTensorDescentInput]
      exact (upperStarLowerStarAdjunction k₀ l j).leftAdjoint_preservesColimits)
    H H' hH hHM hH' hHM'
    (by rfl) (by rfl) (by rfl) (by rfl)
    (hm.iA.trans (by unfold nativeOpenTensorInsertion; rfl))
    (hm.iB.trans (by unfold nativeOpenTensorInsertion; rfl)) sr

end AlgebraicGeometry.ProEtaleWeilSheaf
