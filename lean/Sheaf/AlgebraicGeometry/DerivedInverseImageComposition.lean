/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc

/-!
# Composition and coherence of derived inverse images

Source: Stacks Project, Tag 0D6D, with Tags 03CB and 04VG.
(blueprint: lem-weil-pbc-derived-inverse-image-composition)

The source's composition isomorphisms point from the pullback of the composite to the
composite of the pullbacks; their inverses are the `c` and `cᴰ` of the node.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- Composition, identity, and coherence for inverse images of abelian etale sheaves and
on their bounded below derived categories. Source: Stacks Tags 0D6D, 03CB, 04VG
(blueprint: lem-weil-pbc-derived-inverse-image-composition).

Proof, following the six steps of the node:
1. Compare the two sheaf composition maps through the unit equations of
   lem-weil-pbc-inverse-image-composition. Naturality moves the direct-image comparisons
   past the units; lem-weil-pbc-direct-image-composition-coherence identifies the results.
   Uniqueness of the left-adjoint comparison gives associativity.
2. The identity comparison's unit equation and naturality show that each whiskered
   identity comparison solves the composition unit equation. Its uniqueness gives both
   sheaf unit laws.
3. Apply lem-weil-pbc-localization-universal-property to the termwise sheaf comparisons
   and the factorization isomorphisms of def-weil-pbc-derived-inverse-image. This gives
   unique natural isomorphisms on the unbounded derived categories with the stated formulas.
4. Restrict to the full bounded below subcategories, preserved by exact inverse image.
   For uniqueness, use lem-weil-pbc-dplus-injective-representative to identify every object
   with the image of a bounded below complex, and apply naturality. The equivalences below
   express existence (substitute the displayed isomorphism) and uniqueness together.
5. Compute both derived associativity composites on a representing complex. Naturality of
   the factorization comparisons rewrites them as the same three factorization maps followed
   by the termwise sheaf associativity maps from step 1. Localization detects equality.
6. Similarly, compute both derived unit composites on representatives, use the sheaf unit
   laws from step 2 and naturality, and descend equality through localization.

`HomotopyCategory.Plus` consists of homotopy-category objects with bounded below complexes.
Thus its localization `Qh` and the termwise natural transformations give precisely the
node's formulas for bounded below complexes, with the homotopy quotient implicit. -/
theorem derivedInverseImageComposition {X Y Z W : Scheme.{u}}
    (u₀ : Y ⟶ X) (v₀ : Z ⟶ Y) (w₀ : W ⟶ Z) :
    let A := AddCommGrpCat.{u + 1}
    let P := fun {S T : Scheme.{u}} (f : S ⟶ T) => upperStar A f
    let D := fun {S T : Scheme.{u}} (f : S ⟶ T) => (P f).mapDerivedCategoryPlus
    let c := fun {R S T : Scheme.{u}} (f : T ⟶ S) (g : S ⟶ R)
      (fg : T ⟶ R) (hfg : fg = f ≫ g) => (upperStarComp A f g fg hfg).symm
    let e := fun S : Scheme.{u} => upperStarId A S
    let cD := fun {R S T : Scheme.{u}} (f : T ⟶ S) (g : S ⟶ R)
      (fg : T ⟶ R) (hfg : fg = f ≫ g) => (upperStarCompDerivedPlus A f g fg hfg).symm
    let eD := fun S : Scheme.{u} => upperStarIdDerivedPlus A S
    (Functor.whiskerLeft (P u₀) (c w₀ v₀ (w₀ ≫ v₀) rfl).hom ≫
        (c (w₀ ≫ v₀) u₀ (w₀ ≫ v₀ ≫ u₀) (Category.assoc w₀ v₀ u₀).symm).hom =
      Functor.whiskerRight (c v₀ u₀ (v₀ ≫ u₀) rfl).hom (P w₀) ≫
        (c w₀ (v₀ ≫ u₀) (w₀ ≫ v₀ ≫ u₀) rfl).hom) ∧
    ((c u₀ (𝟙 X) u₀ (Category.comp_id u₀).symm).hom =
      Functor.whiskerRight (e X).hom (P u₀)) ∧
    ((c (𝟙 Y) u₀ u₀ (Category.id_comp u₀).symm).hom =
      Functor.whiskerLeft (P u₀) (e Y).hom) ∧
    (∀ t : D u₀ ⋙ D v₀ ≅ D (v₀ ≫ u₀),
      (∀ K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A),
        t.hom.app (DerivedCategory.Plus.Qh.obj K) ≫
            (P (v₀ ≫ u₀)).mapDerivedCategoryPlusFactorsh.hom.app K =
          (D v₀).map ((P u₀).mapDerivedCategoryPlusFactorsh.hom.app K) ≫
            (P v₀).mapDerivedCategoryPlusFactorsh.hom.app
              ((P u₀).mapHomotopyCategoryPlus.obj K) ≫
            DerivedCategory.Plus.Qh.map
              ((NatTrans.mapHomotopyCategoryPlus (c v₀ u₀ (v₀ ≫ u₀) rfl).hom).app K)) ↔
        t = cD v₀ u₀ (v₀ ≫ u₀) rfl) ∧
    (∀ t : D (𝟙 X) ≅ 𝟭 (DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)),
      (∀ K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A),
        t.hom.app (DerivedCategory.Plus.Qh.obj K) =
          (P (𝟙 X)).mapDerivedCategoryPlusFactorsh.hom.app K ≫
            DerivedCategory.Plus.Qh.map
              ((NatTrans.mapHomotopyCategoryPlus (e X).hom).app K)) ↔ t = eD X) ∧
    (Functor.whiskerLeft (D u₀) (cD w₀ v₀ (w₀ ≫ v₀) rfl).hom ≫
        (cD (w₀ ≫ v₀) u₀ (w₀ ≫ v₀ ≫ u₀) (Category.assoc w₀ v₀ u₀).symm).hom =
      Functor.whiskerRight (cD v₀ u₀ (v₀ ≫ u₀) rfl).hom (D w₀) ≫
        (cD w₀ (v₀ ≫ u₀) (w₀ ≫ v₀ ≫ u₀) rfl).hom) ∧
    ((cD u₀ (𝟙 X) u₀ (Category.comp_id u₀).symm).hom =
      Functor.whiskerRight (eD X).hom (D u₀)) ∧
    ((cD (𝟙 Y) u₀ u₀ (Category.id_comp u₀).symm).hom =
      Functor.whiskerLeft (D u₀) (eD Y).hom) := by
  -- Abstract the coefficient instances while checking the proof, then specialize to abelian groups.
  -- This avoids repeatedly unfolding their concrete constructions in the kernel.
  have general : ∀ (A : Type (u + 2)) [Category.{u + 1} A] [CategoryTheory.Abelian A]
      [CategoryTheory.IsGrothendieckAbelian.{u + 1} A],
      let P := fun {S T : Scheme.{u}} (f : S ⟶ T) => upperStar A f
      let D := fun {S T : Scheme.{u}} (f : S ⟶ T) => (P f).mapDerivedCategoryPlus
      let c := fun {R S T : Scheme.{u}} (f : T ⟶ S) (g : S ⟶ R)
        (fg : T ⟶ R) (hfg : fg = f ≫ g) => (upperStarComp A f g fg hfg).symm
      let e := fun S : Scheme.{u} => upperStarId A S
      let cD := fun {R S T : Scheme.{u}} (f : T ⟶ S) (g : S ⟶ R)
        (fg : T ⟶ R) (hfg : fg = f ≫ g) => (upperStarCompDerivedPlus A f g fg hfg).symm
      let eD := fun S : Scheme.{u} => upperStarIdDerivedPlus A S
      (Functor.whiskerLeft (P u₀) (c w₀ v₀ (w₀ ≫ v₀) rfl).hom ≫
          (c (w₀ ≫ v₀) u₀ (w₀ ≫ v₀ ≫ u₀) (Category.assoc w₀ v₀ u₀).symm).hom =
        Functor.whiskerRight (c v₀ u₀ (v₀ ≫ u₀) rfl).hom (P w₀) ≫
          (c w₀ (v₀ ≫ u₀) (w₀ ≫ v₀ ≫ u₀) rfl).hom) ∧
      ((c u₀ (𝟙 X) u₀ (Category.comp_id u₀).symm).hom =
        Functor.whiskerRight (e X).hom (P u₀)) ∧
      ((c (𝟙 Y) u₀ u₀ (Category.id_comp u₀).symm).hom =
        Functor.whiskerLeft (P u₀) (e Y).hom) ∧
      (∀ t : D u₀ ⋙ D v₀ ≅ D (v₀ ≫ u₀),
        (∀ K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A),
          t.hom.app (DerivedCategory.Plus.Qh.obj K) ≫
              (P (v₀ ≫ u₀)).mapDerivedCategoryPlusFactorsh.hom.app K =
            (D v₀).map ((P u₀).mapDerivedCategoryPlusFactorsh.hom.app K) ≫
              (P v₀).mapDerivedCategoryPlusFactorsh.hom.app
                ((P u₀).mapHomotopyCategoryPlus.obj K) ≫
              DerivedCategory.Plus.Qh.map
                ((NatTrans.mapHomotopyCategoryPlus (c v₀ u₀ (v₀ ≫ u₀) rfl).hom).app K)) ↔
          t = cD v₀ u₀ (v₀ ≫ u₀) rfl) ∧
      (∀ t : D (𝟙 X) ≅ 𝟭 (DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)),
        (∀ K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A),
          t.hom.app (DerivedCategory.Plus.Qh.obj K) =
            (P (𝟙 X)).mapDerivedCategoryPlusFactorsh.hom.app K ≫
              DerivedCategory.Plus.Qh.map
                ((NatTrans.mapHomotopyCategoryPlus (e X).hom).app K)) ↔ t = eD X) ∧
      (Functor.whiskerLeft (D u₀) (cD w₀ v₀ (w₀ ≫ v₀) rfl).hom ≫
          (cD (w₀ ≫ v₀) u₀ (w₀ ≫ v₀ ≫ u₀) (Category.assoc w₀ v₀ u₀).symm).hom =
        Functor.whiskerRight (cD v₀ u₀ (v₀ ≫ u₀) rfl).hom (D w₀) ≫
          (cD w₀ (v₀ ≫ u₀) (w₀ ≫ v₀ ≫ u₀) rfl).hom) ∧
      ((cD u₀ (𝟙 X) u₀ (Category.comp_id u₀).symm).hom =
        Functor.whiskerRight (eD X).hom (D u₀)) ∧
      ((cD (𝟙 Y) u₀ u₀ (Category.id_comp u₀).symm).hom =
        Functor.whiskerLeft (D u₀) (eD Y).hom)
    := by
      intro A _ _ _ P D c e cD eD
      dsimp -zeta only [P, D, c, e, cD, eD]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have h := congrArg Iso.inv (upperStarComp_assoc A w₀ v₀ u₀
          (w₀ ≫ v₀ ≫ u₀) rfl)
        apply NatTrans.ext
        funext M
        simpa using NatTrans.congr_app h.symm M
      · rw [upperStarComp_id_right]
        apply NatTrans.ext
        funext M
        simp
      · rw [upperStarComp_id_left]
        apply NatTrans.ext
        funext M
        simp
      · intro t
        have hc : ∀ K : HomotopyCategory.Plus
            (Sheaf X.smallEtaleTopology A),
            (upperStarCompDerivedPlus A v₀ u₀ (v₀ ≫ u₀) rfl).inv.app
                (DerivedCategory.Plus.Qh.obj K) ≫
              (upperStar A (v₀ ≫ u₀)).mapDerivedCategoryPlusFactorsh.hom.app K =
            (upperStar A v₀).mapDerivedCategoryPlus.map
                ((upperStar A u₀).mapDerivedCategoryPlusFactorsh.hom.app K) ≫
              (upperStar A v₀).mapDerivedCategoryPlusFactorsh.hom.app
                ((upperStar A u₀).mapHomotopyCategoryPlus.obj K) ≫
              DerivedCategory.Plus.Qh.map
                ((NatTrans.mapHomotopyCategoryPlus
                  (upperStarComp A v₀ u₀ (v₀ ≫ u₀) rfl).inv).app K) := by
          intro K
          apply (Iso.inv_comp_eq
            ((upperStarCompDerivedPlus A v₀ u₀ (v₀ ≫ u₀) rfl).app
              (DerivedCategory.Plus.Qh.obj K))).mpr
          erw [upperStarCompDerivedPlus_hom_app_factorsh_assoc A
            v₀ u₀ (v₀ ≫ u₀) rfl K]
          rw [← Functor.map_comp, ← NatTrans.comp_app,
            ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.hom_inv_id,
            NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app, DerivedCategory.Plus.Qh.map_id,
            Category.comp_id]
        constructor
        · intro ht
          apply Iso.ext
          refine Localization.natTrans_ext DerivedCategory.Plus.Qh
            (HomotopyCategory.Plus.quasiIso _) (fun K ↦ ?_)
          exact (Iso.cancel_iso_hom_right _ _
            ((upperStar A (v₀ ≫ u₀)).mapDerivedCategoryPlusFactorsh.app K)).mp
              ((ht K).trans (hc K).symm)
        · rintro rfl
          exact hc
      · intro t
        constructor
        · intro ht
          apply Iso.ext
          exact Localization.natTrans_ext DerivedCategory.Plus.Qh
            (HomotopyCategory.Plus.quasiIso _) (fun K ↦
              (ht K).trans (upperStarIdDerivedPlus_hom_app A X K).symm)
        · rintro rfl
          exact upperStarIdDerivedPlus_hom_app A X
      · have h := upperStarCompDerivedPlus_assoc A w₀ v₀ u₀
          (w₀ ≫ v₀) (v₀ ≫ u₀) (w₀ ≫ v₀ ≫ u₀) rfl rfl
          (Category.assoc w₀ v₀ u₀).symm
        simpa only [IsIso.inv_comp, Functor.inv_whiskerRight, Functor.inv_whiskerLeft,
          IsIso.Iso.inv_hom, Iso.symm_hom] using (IsIso.inv_eq_inv.mpr h).symm
      · symm
        apply (Iso.hom_comp_eq_id
          (upperStarCompDerivedPlus A u₀ (𝟙 X) u₀ (Category.comp_id u₀).symm)).mp
        apply NatTrans.ext
        funext M
        simpa using NatTrans.congr_app (upperStarCompDerivedPlus_id_right A u₀) M
      · symm
        apply (Iso.hom_comp_eq_id
          (upperStarCompDerivedPlus A (𝟙 Y) u₀ u₀ (Category.id_comp u₀).symm)).mp
        apply NatTrans.ext
        funext M
        simpa using NatTrans.congr_app (upperStarCompDerivedPlus_id_left A u₀) M
  exact general AddCommGrpCat.{u + 1}

end AlgebraicGeometry.Etale
