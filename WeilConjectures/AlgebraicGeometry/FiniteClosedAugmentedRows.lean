/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteClosedRowConstructions

/-!
# Finite signed augmented closed rows without exactness

Source: Stacks Project, proetale.tex, Tag 09AH, lemma-ses-associated-to-open;
homology.tex, Tag 0133; the six-step agent comparison deduction in the DAG.
(blueprint: def-sfb-finite-closed-augmented-rows).

The graded terms, signs, intersections, units, and ordinary totalization reuse the
existing finite-closed construction. The row interface below deliberately imposes no
covering or exactness condition. Its restriction maps are fixed by the actual units,
which are epimorphic under the geometric hypotheses of the statements.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u vP uP
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry

/-- A finite signed closed row, with its actual unit augmentation, without an exactness
assertion. The unit equations uniquely specify the actual pushed units after inverse-image
composition. Finite products here are the canonical finite biproducts.
Source: Stacks, Tag 09AH; the displayed row in the comparison deduction
(blueprint: def-sfb-finite-closed-augmented-rows). -/
structure FiniteClosedAugmentedRows {X Z : Scheme.{u}} (i : Z ⟶ X) {m : ℕ}
    (W : Fin m → Over X) (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) where
  restriction : ∀ s t : Finset (Fin m),
    finiteClosedRestriction (finiteClosedIntersection W s).hom A ⟶
      finiteClosedRestriction (finiteClosedIntersection W t).hom A
  restriction_unit : ∀ (s t : Finset (Fin m)), s ⊆ t →
    finiteClosedUnit (finiteClosedIntersection W s).hom A ≫ restriction s t =
      finiteClosedUnit (finiteClosedIntersection W t).hom A
  restriction_zero : ∀ (s t : Finset (Fin m)), ¬s ⊆ t → restriction s t = 0
  ambientRestriction : ∀ s : Finset (Fin m), s.Nonempty →
    (finiteClosedRestriction i A ⟶ finiteClosedRestriction (finiteClosedIntersection W s).hom A)
  ambient_unit : ∀ (s : Finset (Fin m)) (hs : s.Nonempty),
    finiteClosedUnit i A ≫ ambientRestriction s hs =
      finiteClosedUnit (finiteClosedIntersection W s).hom A
  rows : ProEtaleTensorComparison.Modules A ⥤
    CochainComplex (ProEtaleTensorComparison.Modules A) ℤ
  additive : rows.Additive
  terms : ∀ p : ℕ, rows ⋙ HomologicalComplex.eval _ _ (p : ℤ) ≅ finiteClosedTerms W A p
  differential : ∀ (M : ProEtaleTensorComparison.Modules A) (p : ℕ),
    (terms p).inv.app M ≫ (rows.obj M).d (p : ℤ) ((p : ℤ) + 1) ≫
      (terms (p + 1)).hom.app M = (finiteClosedDifferential W A restriction p).app M
  support : ∀ (M : ProEtaleTensorComparison.Modules A) (p : ℤ),
    p < 0 ∨ (m : ℤ) ≤ p → IsZero ((rows.obj M).X p)
  augment : finiteClosedRestriction i A ⟶ rows ⋙ HomologicalComplex.eval _ _ (0 : ℤ)
  augment_unit : ∀ (M : ProEtaleTensorComparison.Modules A) (t : Fin 1 ↪o Fin m),
    (finiteClosedUnit i A).app M ≫ augment.app M ≫ (terms 0).hom.app M ≫
      (finiteClosedTermProjection W A 0 t).app M =
        (finiteClosedUnit (finiteClosedIntersection W (Finset.univ.image t)).hom A).app M
  totalAugment : (finiteClosedRestriction i A).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
    @finiteClosedTotal X A rows additive
  totalAugment_f : ∀ (K : CochainComplex (ProEtaleTensorComparison.Modules A) ℤ) (n : ℤ),
    (totalAugment.app K).f n = augment.app (K.X n) ≫
      ((@finiteClosedDouble X A rows additive).obj K).ιTotal (ComplexShape.up ℤ)
        0 n n (Int.zero_add n)

/-- The row comparison specified on all intersection projections; in negative degrees
both sides vanish. The inverse-image coefficient ring is the recorded one.
Source: Stacks, Tag 09AH; comparison deduction, step 3
(blueprint: def-sfb-finite-closed-augmented-rows). -/
def FiniteClosedAugmentedRows.RowFormula {X Z Y : Scheme.{u}} {i : Z ⟶ X} {m : ℕ}
    {W : Fin m → Over X} {A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (D : FiniteClosedAugmentedRows i W A) (g : Y ⟶ X)
    (D' : FiniteClosedAugmentedRows (pullback.fst g i) (finiteClosedPullbackFamily W g)
      (ProEtaleTensorComparison.inverseRing g A))
    (cs : ∀ s : Finset (Fin m), s.Nonempty →
      (finiteClosedRestriction (finiteClosedIntersection W s).hom A ⋙
          proEtaleModuleInverseImage g A ≅
        proEtaleModuleInverseImage g A ⋙
          finiteClosedRestriction (finiteClosedIntersection (finiteClosedPullbackFamily W g) s).hom
            (ProEtaleTensorComparison.inverseRing g A)))
    (σ : D.rows ⋙ finiteClosedPullbackComplex g A ⟶ proEtaleModuleInverseImage g A ⋙ D'.rows) :
    Prop :=
  ∀ (p : ℕ) (t : Fin (p + 1) ↪o Fin m)
    (ht : (Finset.univ.image t).Nonempty),
    Functor.whiskerRight σ (HomologicalComplex.eval _ _ (p : ℤ)) ≫
        Functor.whiskerLeft (proEtaleModuleInverseImage g A)
          ((D'.terms p).hom ≫ finiteClosedTermProjection (finiteClosedPullbackFamily W g)
            (ProEtaleTensorComparison.inverseRing g A) p t) =
      Functor.whiskerRight ((D.terms p).hom ≫ finiteClosedTermProjection W A p t)
          (proEtaleModuleInverseImage g A) ≫ (cs (Finset.univ.image t) ht).hom

/-- The diagonal-inclusion formula after restriction along any complex-valued functor.
This single equation is shared by the cover theorem on all complexes and by the pullback
comparison on bounded-below complexes.
Source: homology.tex, Tag 0133; comparison deduction, step 4
(blueprint: def-sfb-finite-closed-augmented-rows). -/
def FiniteClosedAugmentedRows.TotalFormulaOn {X Z Y : Scheme.{u}} {i : Z ⟶ X} {m : ℕ}
    {W : Fin m → Over X} {A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (D : FiniteClosedAugmentedRows i W A) (g : Y ⟶ X)
    (D' : FiniteClosedAugmentedRows (pullback.fst g i) (finiteClosedPullbackFamily W g)
      (ProEtaleTensorComparison.inverseRing g A))
    {P : Type vP} [Category.{uP} P]
    (I : P ⥤ CochainComplex (ProEtaleTensorComparison.Modules A) ℤ)
    (σ : D.rows ⋙ finiteClosedPullbackComplex g A ⟶ proEtaleModuleInverseImage g A ⋙ D'.rows)
    (τ : I ⋙ @finiteClosedTotal X A D.rows D.additive ⋙ finiteClosedPullbackComplex g A ⟶
      I ⋙ finiteClosedPullbackComplex g A ⋙ @finiteClosedTotal Y _ D'.rows D'.additive) :
    Prop :=
  ∀ (K : P) (p q n : ℤ) (h : p + q = n),
    (proEtaleModuleInverseImage g A).map
        (((@finiteClosedDouble X A D.rows D.additive).obj (I.obj K)).ιTotal
          (ComplexShape.up ℤ) p q n h) ≫ (τ.app K).f n =
      (σ.app ((I.obj K).X q)).f p ≫
        (((@finiteClosedDouble Y _ D'.rows D'.additive).obj
          ((finiteClosedPullbackComplex g A).obj (I.obj K))).ιTotal
            (ComplexShape.up ℤ) p q n h)

/-- The shared total formula restricted to bounded-below complexes.
Source: homology.tex, Tag 0133; comparison deduction, step 4
(blueprint: def-sfb-finite-closed-augmented-rows). -/
abbrev FiniteClosedAugmentedRows.TotalFormula {X Z Y : Scheme.{u}} {i : Z ⟶ X} {m : ℕ}
    {W : Fin m → Over X} {A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (D : FiniteClosedAugmentedRows i W A) (g : Y ⟶ X)
    (D' : FiniteClosedAugmentedRows (pullback.fst g i) (finiteClosedPullbackFamily W g)
      (ProEtaleTensorComparison.inverseRing g A))
    (σ : D.rows ⋙ finiteClosedPullbackComplex g A ⟶ proEtaleModuleInverseImage g A ⋙ D'.rows)
    (τ : CochainComplex.Plus.ι (ProEtaleTensorComparison.Modules A) ⋙
        @finiteClosedTotal X A D.rows D.additive ⋙ finiteClosedPullbackComplex g A ⟶
      CochainComplex.Plus.ι (ProEtaleTensorComparison.Modules A) ⋙
        finiteClosedPullbackComplex g A ⋙ @finiteClosedTotal Y _ D'.rows D'.additive) : Prop :=
  D.TotalFormulaOn g D' (CochainComplex.Plus.ι (ProEtaleTensorComparison.Modules A)) σ τ

end AlgebraicGeometry
