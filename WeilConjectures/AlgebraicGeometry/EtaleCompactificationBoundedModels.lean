/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportNormalization
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
import WeilConjectures.CategoryTheory.RightDerivedSingleH0
import all WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleSupportMapCompatibility
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-! # Bounded models for an etale compactification

Source: Stacks Project, Tag 0GL6, bounded-model preparation using the prescribed
etale compact-support normalization (blueprint: lem-sp-etale-compactification-bounded-models).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Etale



attribute [local instance 2000] Sheaf.instHasColimitsOfShape
  Functor.preservesZeroMorphisms_of_additive


attribute [local irreducible] lowerStar upperStar Functor.mapDerivedCategory
  Functor.rightDerivedFunctor Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryFactorsh Functor.rightDerivedFunctorUnit
  Functor.rightDerivedFunctorUnitQ

/-- The canonical acyclic-complex arrow, before any acyclicity assertion. First use the
right-derived unit on the actual degreewise open extension, then the exact-functor
localization comparison for that open extension. Thus its target is precisely compact
support in the chosen compactification, with no resolution or map chosen as extra data.
Source: Stacks Project, Tag 0GL6; the graph comparison's derived-unit formula
(blueprint: lem-sp-etale-compactification-bounded-models). -/
noncomputable def etaleCompactificationAcyclicComparison
    (R : Type (u + 1)) [CommRing R] {U V : Scheme.{u}} {e : U ⟶ V}
    (c : Compactification e)
    (K : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ) :
    _root_.DerivedCategory.Q.obj
        (((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i ⋙
          lowerStar (ModuleCat.{u + 1} R) c.g).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj
        (_root_.DerivedCategory.Q.obj K) :=
  (lowerStar (ModuleCat.{u + 1} R) c.g).rightDerivedFunctorUnitQ
      (((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapHomologicalComplex
        (.up ℤ)).obj K) ≫
    (lowerStar (ModuleCat.{u + 1} R) c.g).rightDerivedFunctor.map
      ((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategoryFactors.inv.app K)

private theorem comparison_cancel
    {C : Type*} [Category C] {X Y Z W : C}
    (s : X ≅ Y) (a : Y ≅ Z) (t : W ≅ X) (f : Z ⟶ W)
    (h : s.hom ≫ a.hom ≫ f = t.inv) : f ≫ t.hom ≫ s.hom = a.inv := by
  apply (cancel_epi (s.hom ≫ a.hom)).1
  calc
    _ = (s.hom ≫ a.hom ≫ f) ≫ t.hom ≫ s.hom := by simp only [Category.assoc]
    _ = s.hom := by rw [h]; simp only [Iso.inv_hom_id_assoc]
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem acyclicComparison_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (O : C ⥤ D) (F : D ⥤ E) [O.Additive] [F.Additive]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    {K L : CochainComplex C ℤ} (phi : K ⟶ L) :
    DerivedCategory.Q.map (((O ⋙ F).mapHomologicalComplex (.up ℤ)).map phi) ≫
        (F.rightDerivedFunctorUnitQ ((O.mapHomologicalComplex (.up ℤ)).obj L) ≫
          F.rightDerivedFunctor.map (O.mapDerivedCategoryFactors.inv.app L)) =
      (F.rightDerivedFunctorUnitQ ((O.mapHomologicalComplex (.up ℤ)).obj K) ≫
          F.rightDerivedFunctor.map (O.mapDerivedCategoryFactors.inv.app K)) ≫
        F.rightDerivedFunctor.map (O.mapDerivedCategory.map (DerivedCategory.Q.map phi)) := by
  change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map
    ((O.mapHomologicalComplex (.up ℤ)).map phi)) ≫ _ = _
  rw [Functor.rightDerivedFunctorUnitQ_naturality_assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact congrArg F.rightDerivedFunctor.map
    (NatTrans.naturality O.mapDerivedCategoryFactors.inv phi)

private theorem normalization_complex
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (S : C ⥤ E) (O : C ⥤ D) (F : D ⥤ E)
    [S.Additive] [O.Additive] [F.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    (a : S ⟶ O ⋙ F)
    (σ : S.mapDerivedCategory ⟶ O.mapDerivedCategory ⋙ F.rightDerivedFunctor)
    (hσ : ∀ J : HomotopyCategory C (.up ℤ),
      σ.app (DerivedCategory.Qh.obj J) =
        S.mapDerivedCategoryFactorsh.hom.app J ≫
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).app J) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ F)) (.up ℤ)).inv.app J) ≫
        F.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj J) ≫
        F.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.inv.app J))
    (L : CochainComplex C ℤ) :
    S.mapDerivedCategoryFactors.hom.app L ≫
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).app L) ≫
      F.rightDerivedFunctorUnitQ ((O.mapHomologicalComplex (.up ℤ)).obj L) ≫
      F.rightDerivedFunctor.map (O.mapDerivedCategoryFactors.inv.app L) =
      σ.app (DerivedCategory.Q.obj L) := by
  have h := comparison_complex_fac S O F a σ hσ L
  have hu : right_unit_Q F ((O.mapHomologicalComplex (.up ℤ)).obj L) =
      F.rightDerivedFunctorUnitQ ((O.mapHomologicalComplex (.up ℤ)).obj L) := by
    unfold right_unit_Q Functor.rightDerivedFunctorUnitQ
    rfl
  rw [hu] at h
  calc
    _ = (S.mapDerivedCategoryFactors.hom.app L ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).app L) ≫
        F.rightDerivedFunctorUnitQ ((O.mapHomologicalComplex (.up ℤ)).obj L)) ≫
        F.rightDerivedFunctor.map (O.mapDerivedCategoryFactors.inv.app L) := by
      simp only [Category.assoc]
    _ = _ := by
      rw [← h]
      simp only [Category.assoc, ← F.rightDerivedFunctor.map_comp, Iso.hom_inv_id_app]
      erw [F.rightDerivedFunctor.map_id, Category.comp_id]

/-- Bounded models, with the specified sheaf and derived comparisons rather than arbitrary
isomorphisms. The inverse of `nu` is the normalization's graph-extension transformation;
therefore `nu` is its degree-zero proper-support-to-sheet-components comparison.
The chain isomorphism is `NatIso.mapHomologicalComplex nu`, so its components are exactly
`nu.app (K.X n)` and its naturality is built into the natural isomorphism.
Source: Stacks Project, Tag 0GL6, bounded-model preparation
(blueprint: lem-sp-etale-compactification-bounded-models).

Proof:
1. Properness makes c.g finite type; finite type over the Noetherian V makes c.Z
   Noetherian (lem-weil-pbc-finite-type-over-noetherian). The module categories have enough
   injectives (lem-weil-pbc-module-sheaves-enough-injectives); direct image is left exact
   by prop-weil-pbc-inverse-image-modules-exact.
2. Apply lem-asd-etale-compact-support-normalization to M[0]. Its target is concentrated
   in degree zero. The single-object derived identification
   lem-sp-derived-functor-single-identification gives vanishing of positive higher direct
   images of j_!M, without flatness, hence in particular of every j_!K^n.
3. The graph-derived comparison of def-asd-compact-support-graph-comparison is the
   derived unit after the degreewise graph map. Its inverse is the prescribed normalization
   by lem-asd-compact-support-graph-derived-isomorphism. In degree zero the unit is the
   identity by left exactness. Thus the inverse graph sheaf map is exactly nu.
4. Naturality of that sheaf map for the differentials makes its inverse a chain
   isomorphism. Expand the graph-derived formula to obtain alpha = Da Q(nu).
   Cancellation with the prescribed inverse c gives c alpha = Q(nu) as actual derived
   arrows. Naturality of the unit and the two natural isomorphisms gives chain naturality.
5. Extension by zero and etale sum extension are exact and additive
   (lem-weil-pbc-etale-restriction-injectives); direct image is additive. Degreewise they
   preserve zero, hence the same interval [a,b].
6. With flat terms, use lem-pur-etale-projection-kan-comparison: tensoring with v_!M
   is v_! applied to M tensor v^*(-). Exactness of inverse image, tensoring with M,
   and v_! proves flatness for v=j,e. Transport flatness to r_*j_!M using nu.
7. All four complexes are bounded above and termwise flat, so the bounded-flat
   criterion lem-weil-pbc-independent-bounded-flat-kflat gives K-flatness. Steps 1--5
   never assumed flatness. -/
theorem etaleCompactification_bounded_models
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : EtaleCompactSupportNormalization R)
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] [IsSeparated e] [QuasiCompact e]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian V] [CompactSpace V]
    (c : Compactification e) :
    IsNoetherian c.Z ∧
    ∃ nu : openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i ⋙
        lowerStar (ModuleCat.{u + 1} R) c.g ≅
      etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance,
      nu.inv = N.sheafComparison e c ∧
      ∀ (K : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
        (a b : ℤ) (_hK : ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)),
        (∀ (n : ℤ) (q : ℕ), 0 < q →
          IsZero (((lowerStar (ModuleCat.{u + 1} R) c.g).rightDerived q).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).obj (K.X n)))) ∧
        IsIso (etaleCompactificationAcyclicComparison R c K) ∧
        (etaleCompactificationAcyclicComparison R c K ≫
            (N.comparison e c).hom.app (_root_.DerivedCategory.Q.obj K) ≫
            (etaleLowerShriek (ModuleCat.{u + 1} R) e
              inferInstance).mapDerivedCategoryFactors.hom.app K =
          _root_.DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex nu (.up ℤ)).hom.app K)) ∧
        (∀ (L : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
          (phi : K ⟶ L),
          _root_.DerivedCategory.Q.map
              (((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i ⋙
                lowerStar (ModuleCat.{u + 1} R) c.g).mapHomologicalComplex (.up ℤ)).map phi) ≫
              etaleCompactificationAcyclicComparison R c L =
            etaleCompactificationAcyclicComparison R c K ≫
              (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).map
                (_root_.DerivedCategory.Q.map phi)) ∧
        (∀ n : ℤ, n < a ∨ b < n →
          IsZero ((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).obj (K.X n)) ∧
          IsZero ((lowerStar (ModuleCat.{u + 1} R) c.g).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).obj (K.X n))) ∧
          IsZero ((etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).obj (K.X n))) ∧
        ((∀ n : ℤ, exactFunctor _ _ (tensorRight (K.X n))) →
          (∀ n : ℤ,
            exactFunctor _ _ (tensorRight
              ((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).obj (K.X n))) ∧
            exactFunctor _ _ (tensorRight ((lowerStar (ModuleCat.{u + 1} R) c.g).obj
              ((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).obj (K.X n)))) ∧
            exactFunctor _ _ (tensorRight
              ((etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).obj (K.X n)))) ∧
          (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat K ∧
          (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
            (((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapHomologicalComplex
              (.up ℤ)).obj K) ∧
          (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
            (((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i ⋙
              lowerStar (ModuleCat.{u + 1} R) c.g).mapHomologicalComplex (.up ℤ)).obj K) ∧
          (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
            (((etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).mapHomologicalComplex
              (.up ℤ)).obj K)) := by
  have hZ : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have hZc : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have ha : IsIso (N.sheafComparison e c) := supportSheafIso R N e c
  let nu := (asIso (N.sheafComparison e c)).symm
  refine ⟨⟨⟩, nu, rfl, ?_⟩
  have hchain (L : CochainComplex
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ) :
      IsIso (((N.sheafComparison e c).mapHomologicalComplex (.up ℤ)).app L) := by
    change IsIso ((NatIso.mapHomologicalComplex nu (.up ℤ)).inv.app L)
    infer_instance
  have hnorm (L : CochainComplex
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ) :
      (etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).mapDerivedCategoryFactors.hom.app L ≫
        DerivedCategory.Q.map
          (((N.sheafComparison e c).mapHomologicalComplex (.up ℤ)).app L) ≫
        etaleCompactificationAcyclicComparison R c L =
      (N.comparison e c).inv.app (DerivedCategory.Q.obj L) := by
    exact normalization_complex _ _ _ (N.sheafComparison e c) (N.comparison e c).inv
      (N.derived_normalization e c) L
  intro K a b hK
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n q hq
    let O := openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i
    let D := lowerStar (ModuleCat.{u + 1} R) c.g
    let E := etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance
    let M := K.X n
    let i := D.rightDerivedFunctor.mapIso
        ((O.mapDerivedCategorySingleFunctor 0).app M).symm ≪≫
      (N.comparison e c).app ((DerivedCategory.singleFunctor _ 0).obj M) ≪≫
      (E.mapDerivedCategorySingleFunctor 0).app M
    have hz : IsZero ((DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (E.obj M))) :=
      (DerivedCategory.isLE_iff _ 0).1 inferInstance q (by omega)
    exact hz.of_iso
      ((D.homologyRightDerivedFunctorObjSingleFunctorIso (O.obj M) q).symm ≪≫
        (DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso i)
  · have h : IsIso
        ((etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).mapDerivedCategoryFactors.hom.app
            K ≫
          DerivedCategory.Q.map
            (((N.sheafComparison e c).mapHomologicalComplex (.up ℤ)).app K) ≫
          etaleCompactificationAcyclicComparison R c K) := by
      rw [hnorm]
      infer_instance
    have h' : IsIso (DerivedCategory.Q.map
        (((N.sheafComparison e c).mapHomologicalComplex (.up ℤ)).app K) ≫
          etaleCompactificationAcyclicComparison R c K) :=
      IsIso.of_isIso_comp_left
        ((etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).mapDerivedCategoryFactors.hom.app
          K) _
    exact IsIso.of_isIso_comp_left
      (DerivedCategory.Q.map
        (((N.sheafComparison e c).mapHomologicalComplex (.up ℤ)).app K)) _
  · exact comparison_cancel
      ((etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).mapDerivedCategoryFactors.app K)
      (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex nu (.up ℤ)).symm.app K))
      ((N.comparison e c).app (DerivedCategory.Q.obj K))
      (etaleCompactificationAcyclicComparison R c K) (hnorm K)
  · intro L phi
    exact acyclicComparison_naturality
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i)
      (lowerStar (ModuleCat.{u + 1} R) c.g) phi
  · intro n hn
    exact ⟨(openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).map_isZero (hK n hn),
      (lowerStar (ModuleCat.{u + 1} R) c.g).map_isZero
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).map_isZero (hK n hn)),
      (etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).map_isZero (hK n hn)⟩
  · intro hflat
    have hf (n : ℤ) : ObjectProperty.flat (K.X n) :=
      ⟨(exactFunctor _ _).prop_of_iso
        (BraidedCategory.tensorLeftIsoTensorRight (K.X n)).symm (hflat n), hflat n⟩
    have hfo (n : ℤ) : ObjectProperty.flat
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).obj (K.X n)) := by
      exact Functor.PreservesFlat.flat_obj
        (F := etaleLowerShriek (ModuleCat.{u + 1} R) c.i inferInstance) (hf n)
    have hfe (n : ℤ) : ObjectProperty.flat
        ((etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).obj (K.X n)) :=
      Functor.PreservesFlat.flat_obj (hf n)
    have hfd (n : ℤ) : ObjectProperty.flat
        ((lowerStar (ModuleCat.{u + 1} R) c.g).obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).obj (K.X n))) :=
      ObjectProperty.prop_of_iso _ (nu.app (K.X n)).symm (hfe n)
    have hkflat {X : Scheme.{u}}
        (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
        (hz : ∀ n : ℤ, b < n → IsZero (P.X n))
        (hfP : ∀ n, ObjectProperty.flat (P.X n)) :
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P := by
      have : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).2 hz
      have : AB5OfSize.{0, 0} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
        AB5OfSize_of_univLE.{0, 0, u + 1, u + 1} _
      exact P.kFlat_of_isStrictlyLE_of_flat b hfP
    refine ⟨fun n ↦ ⟨(hfo n).2, (hfd n).2, (hfe n).2⟩,
      hkflat K (fun n hn ↦ hK n (.inr hn)) hf,
      hkflat _ (fun n hn ↦ ?_) hfo,
      hkflat _ (fun n hn ↦ ?_) hfd,
      hkflat _ (fun n hn ↦ ?_) hfe⟩
    · exact (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).map_isZero
        (hK n (.inr hn))
    · exact (lowerStar (ModuleCat.{u + 1} R) c.g).map_isZero
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).map_isZero (hK n (.inr hn)))
    · exact (etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).map_isZero
        (hK n (.inr hn))

end AlgebraicGeometry.Etale
