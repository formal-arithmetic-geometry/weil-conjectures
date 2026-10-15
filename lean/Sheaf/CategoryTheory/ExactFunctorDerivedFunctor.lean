/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-!
# Exact functors are their own derived functors

Source: Stacks Project, Derived Categories, Tag 015F, lemma-right-derived-exact-functor,
parts (2)--(4), and Tag 05RW, lemma-bounded-derived; Cohomology on Sites, Section 0735,
section-base-change-map (blueprint: lem-weil-pbc-exact-functor-derived-functor).
-/

@[expose] public section

universe wA wB vA vB uA uB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- An arbitrary factorization pair for an exact functor is both its right and its left
 derived functor, on all complexes and on bounded below complexes. The bounded pair is
 compatible with the supplied unbounded comparison; the quotient-to-derived comparisons
 in that equation identify the included bounded localizations with the unbounded ones.
 Every comparison for any other right or left derived pair is invertible at every complex.

 Source: Stacks Project, Tag 015F, lemma-right-derived-exact-functor, parts (2)--(4);
 Tag 05RW, lemma-bounded-derived; Section 0735, section-base-change-map
 (blueprint: lem-weil-pbc-exact-functor-derived-functor).

 Proof plan:
 1. Descend a transformation out of the termwise functor, composed with `φ.hom`, through
 the localization universal property (lem-weil-pbc-localization-universal-property).
 Its unique descent gives the left Kan property for `φ.inv`.
 2. Descend a transformation into the termwise functor, composed with `φ.inv`, in the
 opposite direction. Its uniqueness gives the right Kan property for `φ.hom`.
 3. Compare `FD` with `F.mapDerivedCategory` by descending `φ` and the canonical
 factorization (lem-weil-pbc-exact-functor-derived-factorization). The resulting natural
 isomorphism and lem-weil-pbc-exact-functor-bounded-below show that `FD` preserves the
 bounded below subcategory (def-weil-pbc-bounded-derived-subcategories). Additivity
 preserves zero objects, so the termwise functor restricts to bounded below complexes.
 Restrict `φ` using the full inclusions and the localization comparisons; its component
 is the equation below.
 4. Apply the same two descent arguments to the bounded below localization
 (lem-weil-pbc-bounded-below-cochain-localization). No injectives are required.
 5. The units/counits of the displayed pairs are invertible. For any other derived pair,
 the Kan universal properties give comparison transformations in both directions.
 Uniqueness makes their composites identities, so the other unit/counit is also
 invertible, on all complexes and likewise on bounded below complexes. -/
theorem exactFunctor_derivedFunctor
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (FD : DerivedCategory A ⥤ DerivedCategory B)
    (φ : DerivedCategory.Q ⋙ FD ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) :
    FD.IsRightDerivedFunctor φ.inv (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ∧
    FD.IsLeftDerivedFunctor φ.hom (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ∧
    (∀ (RF : DerivedCategory A ⥤ DerivedCategory B)
      (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ RF),
      RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) →
      ∀ (K : CochainComplex A ℤ), IsIso (α.app K)) ∧
    (∀ (LF : DerivedCategory A ⥤ DerivedCategory B)
      (ε : DerivedCategory.Q ⋙ LF ⟶
        F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q),
      LF.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) →
      ∀ (K : CochainComplex A ℤ), IsIso (ε.app K)) ∧
    ∃ (Fplus : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
      (e : Fplus ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ FD)
      (φplus : DerivedCategory.Plus.Q ⋙ Fplus ≅
        F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q),
      (∀ (K : CochainComplex.Plus A),
        DerivedCategory.Plus.ι.map (φplus.hom.app K) ≫
          (DerivedCategory.quotientCompQhIso B).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj) =
        e.hom.app (DerivedCategory.Plus.Q.obj K) ≫
          FD.map ((DerivedCategory.quotientCompQhIso A).hom.app K.obj) ≫
          φ.hom.app K.obj) ∧
      Fplus.IsLeftKanExtension φplus.inv ∧
      Fplus.IsRightKanExtension φplus.hom ∧
      (∀ (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
        (α : F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
          DerivedCategory.Plus.Q ⋙ RF),
        RF.IsLeftKanExtension α →
        ∀ (K : CochainComplex.Plus A), IsIso (α.app K)) ∧
      (∀ (LF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
        (ε : DerivedCategory.Plus.Q ⋙ LF ⟶
          F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q),
        LF.IsRightKanExtension ε →
        ∀ (K : CochainComplex.Plus A), IsIso (ε.app K)) := by
  let hF := F.mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso
    (ComplexShape.up ℤ)
  have hright : FD.IsRightDerivedFunctor φ.inv
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) := by
    exact Functor.isRightDerivedFunctor_of_inverts
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) FD φ
  have hleft : FD.IsLeftDerivedFunctor φ.hom
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) := by
    exact Functor.isLeftDerivedFunctor_of_inverts
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) FD φ
  refine ⟨hright, hleft, ?_, ?_, ?_⟩
  · intro RF α hRF K
    have : IsIso α := Functor.isIso_of_isRightDerivedFunctor_of_inverts RF α hF
    infer_instance
  · intro LF ε hLF K
    have : IsIso ε := Functor.isIso_of_isLeftDerivedFunctor_of_inverts LF ε hF
    infer_instance
  · let δ : FD ≅ F.mapDerivedCategory :=
      Localization.liftNatIso DerivedCategory.Q
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
        (DerivedCategory.Q ⋙ FD) (DerivedCategory.Q ⋙ F.mapDerivedCategory)
        FD F.mapDerivedCategory (φ ≪≫ F.mapDerivedCategoryFactors.symm)
    have hplus : ∀ X : DerivedCategory.Plus A,
        DerivedCategory.TStructure.t.plus (FD.obj X.obj) := by
      rintro ⟨X, n, hn⟩
      have := F.isGE_mapDerivedCategory_obj X n
      exact ⟨n, DerivedCategory.TStructure.t.isGE_of_iso (δ.app X).symm n⟩
    let Fplus : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B :=
      DerivedCategory.TStructure.t.plus.lift (DerivedCategory.Plus.ι ⋙ FD) hplus
    let cA : DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ≅
        CochainComplex.Plus.ι A ⋙ DerivedCategory.Q :=
      NatIso.ofComponents (fun K ↦ (DerivedCategory.quotientCompQhIso A).app K.obj)
        (fun f ↦ (DerivedCategory.quotientCompQhIso A).hom.naturality f.hom)
    let cB : DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ≅
        CochainComplex.Plus.ι B ⋙ DerivedCategory.Q :=
      NatIso.ofComponents (fun K ↦ (DerivedCategory.quotientCompQhIso B).app K.obj)
        (fun f ↦ (DerivedCategory.quotientCompQhIso B).hom.naturality f.hom)
    let ψ : (DerivedCategory.Plus.Q ⋙ Fplus) ⋙ DerivedCategory.Plus.ι ≅
        (F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) ⋙ DerivedCategory.Plus.ι :=
      isoWhiskerRight cA FD ≪≫ isoWhiskerLeft (CochainComplex.Plus.ι A) φ ≪≫
        isoWhiskerLeft F.mapCochainComplexPlus cB.symm
    let φplus : DerivedCategory.Plus.Q ⋙ Fplus ≅
        F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q :=
      Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι ψ
    have hloc : (DerivedCategory.Plus.Q (C := A)).IsLocalization
        (CochainComplex.Plus.quasiIso A) := by
      dsimp only [DerivedCategory.Plus.Q]
      infer_instance
    have hright := Functor.isRightDerivedFunctor_of_inverts
      (CochainComplex.Plus.quasiIso A) Fplus φplus
    have hleft := Functor.isLeftDerivedFunctor_of_inverts
      (CochainComplex.Plus.quasiIso A) Fplus φplus
    have hF : (CochainComplex.Plus.quasiIso A).IsInvertedBy
        (F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) := by
      apply (MorphismProperty.IsInvertedBy.iff_of_iso
        (CochainComplex.Plus.quasiIso A) φplus).mp
      exact MorphismProperty.IsInvertedBy.of_comp _ _
        (Localization.inverts _ (CochainComplex.Plus.quasiIso A)) Fplus
    refine ⟨Fplus, Iso.refl _, φplus, ?_, ?_, ?_, ?_, ?_⟩
    · intro K
      dsimp only [φplus]
      rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
      change ψ.hom.app K ≫ (cB.hom.app (F.mapCochainComplexPlus.obj K)) = _
      simp only [ψ, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
        whiskerRight_app, isoWhiskerLeft_hom, whiskerLeft_app, cA, cB,
        NatIso.ofComponents_hom_app, Iso.symm_hom, NatIso.ofComponents_inv_app,
        Iso.app_hom, Iso.app_inv, Iso.refl_hom, NatTrans.id_app,
        Category.id_comp, Category.assoc, Iso.inv_hom_id_app]
      exact congrArg (fun f ↦
        FD.map ((DerivedCategory.quotientCompQhIso A).hom.app K.obj) ≫ f)
        (Category.comp_id (φ.hom.app K.obj))
    · exact hright.isLeftKanExtension
    · exact hleft.isRightKanExtension
    · intro RF α hRF K
      have : RF.IsRightDerivedFunctor α (CochainComplex.Plus.quasiIso A) := ⟨hRF⟩
      have : IsIso α := Functor.isIso_of_isRightDerivedFunctor_of_inverts RF α hF
      infer_instance
    · intro LF ε hLF K
      have : LF.IsLeftDerivedFunctor ε (CochainComplex.Plus.quasiIso A) := ⟨hLF⟩
      have : IsIso ε := Functor.isIso_of_isLeftDerivedFunctor_of_inverts LF ε hF
      infer_instance

end CategoryTheory.Functor
