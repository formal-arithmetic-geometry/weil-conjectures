/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-! # The evaluation-defined site comparison

Source: Weil blueprint, lem-sf-hom-comparison-finite-free, evaluation paragraph;
Stacks Tags 03EO, 03EL, 08J7 (blueprint: def-sf-evaluation-hom-site-comparison).
The tensor comparison below uses only the comparison-site adjunction, avoiding
unrelated scheme-pullback coherence modules.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

/-- The canonical derived tensor comparison of the comparison inverse image.
It is obtained by deriving the oplax structure conjugate to restriction of sheaves;
representable flatness makes that structure strong monoidal.
Source: Stacks Tags 03EO, 03EL (blueprint: def-sf-evaluation-hom-site-comparison). -/
noncomputable def siteComparisonTensorIso
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (Etale.derivedTensor A X).obj K ⋙ (comparisonUpperStar A X).mapDerivedCategory ≅
      (comparisonUpperStar A X).mapDerivedCategory ⋙
        (derivedTensor A X).obj ((comparisonUpperStar A X).mapDerivedCategory.obj K) := by
  letI : (comparisonLowerStar A X).LaxMonoidal := by
    unfold comparisonLowerStar
    infer_instance
  letI : (comparisonUpperStar A X).OplaxMonoidal :=
    (comparisonAdjunction A X).leftAdjointOplaxMonoidal
  letI (V : X.ProEtᵒᵖ) : IsFiltered (CostructuredArrow X.toProEt.op V) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence _ (unop V))
  letI (F G : Sheaf X.smallEtaleTopology A) :
      IsIso (Functor.OplaxMonoidal.δ (comparisonUpperStar A X) F G) := by
    unfold comparisonUpperStar
    infer_instance
  letI : IsIso (Functor.OplaxMonoidal.η (comparisonUpperStar A X)) := by
    unfold comparisonUpperStar
    infer_instance
  letI : (comparisonUpperStar A X).Monoidal := .ofOplaxMonoidal _
  exact Functor.isoWhiskerLeft _
      (comparisonUpperStar A X).leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    (asIso (comparisonUpperStar A X).leftDerivedTensorComparison).app K ≪≫
    Functor.isoWhiskerRight
      (comparisonUpperStar A X).leftDerivedFunctorIsoMapDerivedCategory _ ≪≫
    Functor.isoWhiskerLeft (comparisonUpperStar A X).mapDerivedCategory
      ((derivedTensor A X).mapIso
        ((comparisonUpperStar A X).leftDerivedFunctorIsoMapDerivedCategory.app K))

/-- The specified comparison is the transpose of pullback of evaluation, using the
canonical tensor comparison. It is defined on all ambient complexes; invertibility
requires hypotheses and is a separate assertion.
Source: Stacks Tags 03EO, 03EL, 08J7
(blueprint: def-sf-evaluation-hom-site-comparison). -/
noncomputable def siteComparisonEvaluationHom
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (comparisonUpperStar A X).mapDerivedCategory.obj
        (((Etale.derivedHom A X).obj (op K)).obj M) ⟶
      ((derivedHom A X).obj
        (op ((comparisonUpperStar A X).mapDerivedCategory.obj K))).obj
          ((comparisonUpperStar A X).mapDerivedCategory.obj M) :=
  let F := (comparisonUpperStar A X).mapDerivedCategory
  let H := ((Etale.derivedHom A X).obj (op K)).obj M
  (derivedTensorHomAdjunction A (F.obj K)).homEquiv (F.obj H) (F.obj M)
    ((siteComparisonTensorIso A X K).inv.app H ≫
      F.map ((Etale.derivedTensorHomAdjunction A K).counit.app M))

end AlgebraicGeometry.ProEtale
