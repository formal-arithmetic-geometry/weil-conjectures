/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisComparisons
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisExact

/-!
# Mayer-Vietoris for étale cohomology

## References

* Stacks Project, Tags 0A50 and 03F3
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite


namespace AlgebraicGeometry.Etale

/-- The Mayer-Vietoris sequence for a cover of `X` by two opens `U` and `V`, with connecting
maps natural in the coefficient sheaf (Stacks, Tags 0A50 and 03F3). -/
theorem etale_mayerVietoris (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    Nonempty (∀ n : ℕ, (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X)))).rightDerived n ≅
      (DerivedCategory.singleFunctor _ 0 ⋙ cohomology AddCommGrpCat.{u + 1} X n)) ∧
    Nonempty (∀ n : ℕ, (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk U.ι))).rightDerived n ≅
      (upperStar AddCommGrpCat.{u + 1} U.ι ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        cohomology AddCommGrpCat.{u + 1} U.toScheme n)) ∧
    Nonempty (∀ n : ℕ, (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk V.ι))).rightDerived n ≅
      (upperStar AddCommGrpCat.{u + 1} V.ι ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        cohomology AddCommGrpCat.{u + 1} V.toScheme n)) ∧
    Nonempty (∀ n : ℕ, (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk (U ⊓ V).ι))).rightDerived n ≅
      (upperStar AddCommGrpCat.{u + 1} (U ⊓ V).ι ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        cohomology AddCommGrpCat.{u + 1} (U ⊓ V).toScheme n)) ∧
    ∃ δ : ∀ n : ℕ,
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk (U ⊓ V).ι))).rightDerived n ⟶
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X)))).rightDerived (n + 1),
      ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
        Function.Injective (fun x => (((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology
            AddCommGrpCat.{u + 1})
          ((evaluation _ _).map (MorphismProperty.Over.homMk
            (A := Scheme.Etale.mk U.ι) (B := Scheme.Etale.mk (𝟙 X))
            U.ι (Category.comp_id U.ι)).op)).rightDerived 0).app F x,
          ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk V.ι)
              (B := Scheme.Etale.mk (𝟙 X)) (V.ι) (Category.comp_id V.ι)).op)).rightDerived 0).app F
            x)) ∧
        (∀ n : ℕ,
          Function.Exact (fun x => (((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology
            AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk U.ι)
              (B := Scheme.Etale.mk (𝟙 X)) (U.ι) (Category.comp_id U.ι)).op)).rightDerived n).app F
            x,
          ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk V.ι)
              (B := Scheme.Etale.mk (𝟙 X)) (V.ι) (Category.comp_id V.ι)).op)).rightDerived n).app F
            x))
            (fun x => ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u +
            1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk (U ⊓ V).ι)
              (B := Scheme.Etale.mk U.ι) (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (X.homOfLE_ι
            inf_le_left)).op)).rightDerived
            n).app F x.1 -
          ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk (U ⊓ V).ι)
              (B := Scheme.Etale.mk V.ι) (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (X.homOfLE_ι
            inf_le_right)).op)).rightDerived
            n).app F x.2) ∧
          Function.Exact (fun (x :
            ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
              (evaluation _ _).obj (op (Scheme.Etale.mk U.ι))).rightDerived n).obj F ×
            ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
              (evaluation _ _).obj (op (Scheme.Etale.mk V.ι))).rightDerived n).obj F) =>
            ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology
            AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk (U ⊓ V).ι)
              (B := Scheme.Etale.mk U.ι) (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) (X.homOfLE_ι
            inf_le_left)).op)).rightDerived
            n).app F x.1 -
          ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk (U ⊓ V).ι)
              (B := Scheme.Etale.mk V.ι) (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (X.homOfLE_ι
            inf_le_right)).op)).rightDerived
            n).app F x.2) ((δ n).app F) ∧
          Function.Exact ((δ n).app F)
            (fun x => (((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u
            + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk U.ι)
              (B := Scheme.Etale.mk (𝟙 X)) (U.ι) (Category.comp_id U.ι)).op)).rightDerived (n +
            1)).app F x,
          ((Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          ((evaluation _ _).map
            (MorphismProperty.Over.homMk (A := Scheme.Etale.mk V.ι)
              (B := Scheme.Etale.mk (𝟙 X)) (V.ι) (Category.comp_id V.ι)).op)).rightDerived (n +
            1)).app F x))) ∧
        (∀ n : ℕ,
          Subsingleton ((cohomology AddCommGrpCat.{u + 1} U.toScheme n).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              ((upperStar AddCommGrpCat.{u + 1} U.ι).obj F))) →
          Subsingleton ((cohomology AddCommGrpCat.{u + 1} V.toScheme n).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              ((upperStar AddCommGrpCat.{u + 1} V.ι).obj F))) →
          (n = 0 ∨ ∃ m : ℕ, n = m + 1 ∧
            Subsingleton ((cohomology AddCommGrpCat.{u + 1} (U ⊓ V).toScheme m).obj
              ((DerivedCategory.singleFunctor _ 0).obj
                ((upperStar AddCommGrpCat.{u + 1} (U ⊓ V).ι).obj F)))) →
          Subsingleton ((cohomology AddCommGrpCat.{u + 1} X n).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  obtain ⟨⟨eX⟩, ⟨eU⟩, ⟨eV⟩, ⟨eUV⟩⟩ := etale_mayerVietoris_comparisons X U V
  obtain ⟨δ, hδ⟩ := etale_mayerVietoris_exact X U V hcover
  refine ⟨⟨eX⟩, ⟨eU⟩, ⟨eV⟩, ⟨eUV⟩, δ, ?_⟩
  intro F
  obtain ⟨hinj, hex⟩ := hδ F
  refine ⟨hinj, hex, ?_⟩
  intro n hU hV hprev
  have hU' := (Equiv.subsingleton_congr
    ((eU n).app F).addCommGroupIsoToAddEquiv.toEquiv).mpr hU
  have hV' := (Equiv.subsingleton_congr
    ((eV n).app F).addCommGroupIsoToAddEquiv.toEquiv).mpr hV
  have hX : Subsingleton (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X)))).rightDerived n).obj F) := by
    rcases hprev with rfl | ⟨m, rfl, hUV⟩
    · exact hinj.subsingleton
    · have hUV' := (Equiv.subsingleton_congr
        ((eUV m).app F).addCommGroupIsoToAddEquiv.toEquiv).mpr hUV
      refine ⟨fun x y => ?_⟩
      have hx := (hex m).2.2 x
      have hy := (hex m).2.2 y
      obtain ⟨a, ha⟩ := hx.mp (Subsingleton.elim _ _)
      obtain ⟨b, hb⟩ := hy.mp (Subsingleton.elim _ _)
      exact ha.symm.trans ((congrArg ((δ m).app F) (Subsingleton.elim a b)).trans hb)
  exact (Equiv.subsingleton_congr
    ((eX n).app F).addCommGroupIsoToAddEquiv.toEquiv).mp hX

end AlgebraicGeometry.Etale
