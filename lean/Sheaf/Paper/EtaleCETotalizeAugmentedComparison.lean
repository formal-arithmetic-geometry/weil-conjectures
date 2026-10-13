/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.EtaleCETotalSections
import Sheaf.CategoryTheory.CartanEilenbergMappedTotal

/-! # Totalizing an augmented CE comparison

Source: Stacks Project, Derived Categories, Tags 015J and 015K.
(blueprint: lem-weil-pbc-ce-totalize-augmented-comparison).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option maxHeartbeats 1000000 in
-- Elaborate the dependent CE totals and representative equations together.
/-- Totalize a supplied augmented bicomplex map, retaining its summand equations.
This theorem constructs no pages and makes no choice of CE resolutions.
Source: Stacks Project, Tag 015J, finite-diagonal total comparison; Tag 015K.
(blueprint: lem-weil-pbc-ce-totalize-augmented-comparison).

Proof. Apply the finite-diagonal comparison for upperStar to the source bicomplex.
Invert this comparison, then extend φ by zero, flip and totalize it. On a nonnegative
resolution summand the extension comparison and the total-map coprojection equation
give the displayed formula. In negative resolution degree both sides vanish.
In resolution degree zero, substitute this formula into D.aug_formula. The equation
hφ identifies the result with v followed by D'.aug_formula, proving the strict square.
Conjugate the sections map by the two totalSectionsIso maps. Their coprojection
formulas and naturality of globalSectionsUpperStarMap show that this map carries the
summand of complex degree q to the target summand of degree q. Each source generating
image therefore factors through the corresponding target filtration step. Taking
the finite supremum gives degreewise restrictions. Cancel the target step inclusions
in the chain-map equation for b to prove that the restrictions commute with the
differentials; they assemble to s. This argument also covers empty diagonals. -/
theorem etaleCE_totalize_augmented_comparison
    {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj)
    (D : EtaleTermwiseHypercohomology X K) (D' : EtaleTermwiseHypercohomology Y L)
    (φ : (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj D.I ⟶ D'.I)
    (hφ : ∀ q : ℤ,
      (upperStar AddCommGrpCat.{uNatural + 1} f).map
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.obj.X q)).inv ≫
            (D.a.f q).f 0) ≫ (φ.f q).f 0 =
        v.f q ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.obj.X q)).inv ≫
            (D'.a.f q).f 0) :
    ∃ u : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj D.sheafTotal ⟶ D'.sheafTotal,
      ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map D.aug ≫ u = v ≫ D'.aug ∧
      (∀ (m : ℕ) (q n : ℤ) (h : (m : ℤ) + q = n),
        (upperStar AddCommGrpCat.{uNatural + 1} f).map
            ((HomologicalComplex.extendXIso
              (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h) ≫ u.f n =
          (φ.f q).f m ≫
            (HomologicalComplex.extendXIso
              (((𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D'.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D'.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h) ∧
      let b := D.totalSectionsIso.hom ≫ ceSectionsLift f u ≫ D'.totalSectionsIso.inv
      (∀ q : ℤ, ∃ s : (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ) ⟶
          (D'.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ),
        s ≫ (D'.L.step q).arrow = (D.L.step q).arrow ≫ b) := by sorry

end AlgebraicGeometry.Etale
