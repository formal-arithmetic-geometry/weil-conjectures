/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.DerivedInverseImageComposition
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.AlgebraicGeometry.RelativeDerivedImageSingleLimit
import WeilConjectures.AlgebraicGeometry.AbelianLimitStageInduction
import WeilConjectures.AlgebraicGeometry.RelativePullbackCoefficientSystem

/-! # Relative continuity for bounded-below derived direct images

Source: Stacks Project, Tag 0GIU, lemma-relative-colimit-general-complexes, and
Tag 0EYM, opening paragraphs of the proof of lemma-relative-colimit-general
(blueprint: lem-sf-relative-derived-image-limit).

The existential diagram and cocone have their objects, transitions and legs prescribed
by equations. Thus their existence includes the diagram and cocone laws, and their
colimit property asserts that the canonical comparison is an isomorphism.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar

/-- The degree-`p` map of a commutative square followed by its coefficient morphism.
The first factor is the inverse of the exact-inverse-image cohomology comparison;
the second is cohomology of the canonical derived mate and the coefficient map.
Source: Stacks Tags 0GIU and 0EYM, canonical maps in the opening proof paragraphs
(blueprint: lem-sf-relative-derived-image-limit). -/
noncomputable def relativeDerivedImageCohomologyMap
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {b : Y' ⟶ Y} (sq : CommSq a f' f b)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (K' : DerivedCategory.Plus (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (φ : (upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus.obj K ⟶ K')
    (p : ℤ) :
    (upperStar AddCommGrpCat.{u + 1} b).obj
      ((DerivedCategory.Plus.homologyFunctor _ p).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj K)) ⟶
    (DerivedCategory.Plus.homologyFunctor _ p).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').obj K') :=
  ((upperStar AddCommGrpCat.{u + 1} b).mapDerivedCategoryPlusHomologyFunctorIso p).hom.app
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj K) ≫
    (DerivedCategory.Plus.homologyFunctor _ p).map
      (((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app K) ≫
        (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').map φ)

/-- The pullback of the one fixed complex to a stage in the tail above `i₀`.
Source: Stacks Tag 0GIU, the definition of `K_i`
(blueprint: lem-sf-relative-derived-image-limit). -/
noncomputable def relativeDerivedImageCoefficient
    {I : Type u} [Preorder I] (DU : Iᵒᵖ ⥤ Scheme.{u}) (i₀ : I)
    (K₀ : DerivedCategory.Plus
      (Sheaf (DU.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1}))
    (i : Set.Ici i₀) :
    DerivedCategory.Plus (Sheaf (DU.obj (op i.val)).smallEtaleTopology
      AddCommGrpCat.{u + 1}) :=
  (upperStar AddCommGrpCat.{u + 1}
    (DU.map (homOfLE i.property : i₀ ⟶ i.val).op)).mapDerivedCategoryPlus.obj
    K₀

/-- The stage object `b_i⁻¹ H^p(Rg_i,* K_i)` on the common limit base.
Source: Stacks Tag 0GIU, the displayed colimit
(blueprint: lem-sf-relative-derived-image-limit). -/
noncomputable def relativeDerivedImageStage
    {I : Type u} [Preorder I] (DU DB : Iᵒᵖ ⥤ Scheme.{u}) (η : DU ⟶ DB)
    (cB : Cone DB) (i₀ : I)
    (K₀ : DerivedCategory.Plus
      (Sheaf (DU.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1}))
    (p : ℤ) (i : Set.Ici i₀) : Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (upperStar AddCommGrpCat.{u + 1} (cB.π.app (op i.val))).obj
    ((DerivedCategory.Plus.homologyFunctor _ p).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} (η.app (op i.val))).obj
        (relativeDerivedImageCoefficient DU i₀ K₀ i)))

/-- The canonical identification of an iterated stage pullback with the later coefficient.
Source: Stacks Tag 0GIU, canonical identifications of the complexes `K_i`
(blueprint: lem-sf-relative-derived-image-limit). -/
noncomputable def relativeDerivedImageCoefficientMap
    {I : Type u} [Preorder I] (DU : Iᵒᵖ ⥤ Scheme.{u}) (i₀ : I)
    (K₀ : DerivedCategory.Plus
      (Sheaf (DU.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1}))
    {i j : Set.Ici i₀} (h : i ⟶ j) :
    (upperStar AddCommGrpCat.{u + 1}
      (DU.map (homOfLE (leOfHom h) : i.val ⟶ j.val).op)).mapDerivedCategoryPlus.obj
      (relativeDerivedImageCoefficient DU i₀ K₀ i) ⟶
    relativeDerivedImageCoefficient DU i₀ K₀ j :=
  (upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
    (DU.map (homOfLE (leOfHom h) : i.val ⟶ j.val).op) (DU.map (homOfLE i.property : i₀ ⟶ i.val).op)
    (h₁₂ := DU.map (homOfLE j.property : i₀ ⟶ j.val).op)
    (hh₁₂ :=
      (congrArg (fun k : op j.val ⟶ op i₀ ↦ DU.map k)
        (Subsingleton.elim (homOfLE j.property : i₀ ⟶ j.val).op
          ((homOfLE (leOfHom h) : i.val ⟶ j.val).op ≫
            (homOfLE i.property : i₀ ⟶ i.val).op))).trans
        (DU.map_comp (homOfLE (leOfHom h) : i.val ⟶ j.val).op
          (homOfLE i.property : i₀ ⟶ i.val).op))).inv.app K₀

/-- The prescribed transition, obtained from inverse-image composition and the
counit-adjoint comparison for the transition square. The coefficient map is the
canonical composition isomorphism `a_ji⁻¹ K_i ≅ K_j`.
Source: Stacks Tags 0GIU and 0EYM, canonical transition maps
(blueprint: lem-sf-relative-derived-image-limit). -/
noncomputable def relativeDerivedImageTransition
    {I : Type u} [Preorder I] (DU DB : Iᵒᵖ ⥤ Scheme.{u}) (η : DU ⟶ DB)
    (cB : Cone DB) (i₀ : I)
    (K₀ : DerivedCategory.Plus
      (Sheaf (DU.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1}))
    (p : ℤ) {i j : Set.Ici i₀} (h : i ⟶ j) :
    relativeDerivedImageStage DU DB η cB i₀ K₀ p i ⟶
      relativeDerivedImageStage DU DB η cB i₀ K₀ p j :=
  (upperStarComp AddCommGrpCat.{u + 1} (cB.π.app (op j.val))
    (DB.map (homOfLE (leOfHom h) : i.val ⟶ j.val).op) (cB.π.app (op i.val))
      (cB.w (homOfLE (leOfHom h) : i.val ⟶ j.val).op).symm).hom.app
        ((DerivedCategory.Plus.homologyFunctor _ p).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} (η.app (op i.val))).obj
            (relativeDerivedImageCoefficient DU i₀ K₀ i))) ≫
    (upperStar AddCommGrpCat.{u + 1} (cB.π.app (op j.val))).map
      (relativeDerivedImageCohomologyMap
        (a := DU.map (homOfLE (leOfHom h) : i.val ⟶ j.val).op)
        (f' := η.app (op j.val)) (f := η.app (op i.val))
        (b := DB.map (homOfLE (leOfHom h) : i.val ⟶ j.val).op)
        ⟨η.naturality (homOfLE (leOfHom h) : i.val ⟶ j.val).op⟩
        (relativeDerivedImageCoefficient DU i₀ K₀ i)
        (relativeDerivedImageCoefficient DU i₀ K₀ j)
        (relativeDerivedImageCoefficientMap DU i₀ K₀ h) p)

/-- The prescribed cocone leg. Its derived map is the limit-square mate followed
by the canonical identification `a_i⁻¹ K_i ≅ a_i₀⁻¹ K₀`.
Source: Stacks Tags 0GIU and 0EYM, canonical cocone maps
(blueprint: lem-sf-relative-derived-image-limit). -/
noncomputable def relativeDerivedImageLeg
    {I : Type u} [Preorder I] (DU DB : Iᵒᵖ ⥤ Scheme.{u}) (η : DU ⟶ DB)
    (cU : Cone DU) (cB : Cone DB) (g : cU.pt ⟶ cB.pt)
    (hg : ∀ i : Iᵒᵖ, cU.π.app i ≫ η.app i = g ≫ cB.π.app i)
    (i₀ : I)
    (K₀ : DerivedCategory.Plus
      (Sheaf (DU.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1}))
    (p : ℤ) (i : Set.Ici i₀) :
    relativeDerivedImageStage DU DB η cB i₀ K₀ p i ⟶
    (DerivedCategory.Plus.homologyFunctor _ p).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} g).obj
        ((upperStar AddCommGrpCat.{u + 1} (cU.π.app (op i₀))).mapDerivedCategoryPlus.obj K₀)) :=
  relativeDerivedImageCohomologyMap
    (a := cU.π.app (op i.val)) (f' := g) (f := η.app (op i.val))
    (b := cB.π.app (op i.val)) ⟨hg (op i.val)⟩
    (relativeDerivedImageCoefficient DU i₀ K₀ i)
    ((upperStar AddCommGrpCat.{u + 1} (cU.π.app (op i₀))).mapDerivedCategoryPlus.obj K₀)
    ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
      (cU.π.app (op i.val)) (DU.map (homOfLE i.property : i₀ ⟶ i.val).op) (cU.π.app (op i₀))
      (cU.w (homOfLE i.property : i₀ ⟶ i.val).op).symm).inv.app K₀) p

/-- Relative continuity of bounded-below derived direct images, including existence
of the directed diagram and the canonical cocone.

Source: Stacks Tag 0GIU, lemma-relative-colimit-general-complexes, with the canonical
maps of Tag 0EYM (blueprint: lem-sf-relative-derived-image-limit).

Proof:
1. Form the system of derived stage functors on the directed tail above `i₀`.
   Derived inverse-image associativity, base-change pasting and the unit laws give
   its transitions and limit-stage cocone. These transformations commute with shifts.
2. For a sheaf in degree zero, apply relative sheaf continuity, Tag 0EYM, on this
   tail. Canonical inverse-image composition identifies the coefficient colimit
   with the sheaf pulled back from `i₀` to the limit. The exact-pullback cohomology
   and single-functor comparisons identify every transition and every cocone leg.
   Negative degrees vanish. Shift compatibility gives every sheaf in one degree.
3. Below a common lower bound, stage and limit-stage cohomology vanish. For the
   induction step use the truncation triangle at `a+1`: its lower term is pure in
   degree `a`, while its upper term has lower bound `a+1`. Apply each triangulated
   stage functor, cohomology, and exact filtered colimits. The natural comparison
   commutes with connecting maps. The five lemma gives invertibility in degree `p`
   from the four outside comparisons in degrees `p-1`, `p` and `p+1`.
4. Finite induction on the distance from a lower bound to `p` proves that the
   canonical colimit comparison is invertible for every bounded-below complex.
5. Reindex by the double-op equivalence and transport through the exact-pullback
   cohomology comparisons. Their composition coherence and the base unit law show
   that the resulting diagram and cocone have precisely the maps displayed below.
-/
theorem relativeDerivedImage_limit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (DU DB : Iᵒᵖ ⥤ Scheme.{u}) (η : DU ⟶ DB)
    [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (DU.map h)]
    [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (DB.map h)]
    [∀ i : Iᵒᵖ, QuasiCompact (η.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (η.app i)]
    (cU : Cone DU) (hcU : IsLimit cU) (cB : Cone DB) (hcB : IsLimit cB)
    (g : cU.pt ⟶ cB.pt)
    (hg : ∀ i : Iᵒᵖ, cU.π.app i ≫ η.app i = g ≫ cB.π.app i)
    (i₀ : I)
    (K₀ : DerivedCategory.Plus
      (Sheaf (DU.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1})) (p : ℤ) :
    ∃ (D : Set.Ici i₀ ⥤ Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
      (e : ∀ i : Set.Ici i₀, D.obj i ≅ relativeDerivedImageStage DU DB η cB i₀ K₀ p i)
      (c : Cocone D),
      (∀ (i j : Set.Ici i₀) (h : i ⟶ j),
        D.map h = (e i).hom ≫ relativeDerivedImageTransition DU DB η cB i₀ K₀ p h ≫
          (e j).inv) ∧
      (∃ t : c.pt ≅ (DerivedCategory.Plus.homologyFunctor _ p).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} g).obj
            ((upperStar AddCommGrpCat.{u + 1} (cU.π.app (op i₀))).mapDerivedCategoryPlus.obj
              K₀)),
        (∀ i : Set.Ici i₀, c.ι.app i ≫ t.hom =
          (e i).hom ≫ relativeDerivedImageLeg DU DB η cU cB g hg i₀ K₀ p i) ∧
        Nonempty (IsColimit c)) := by
  let A := AddCommGrpCat.{u + 1}
  let S := relativeLimitStageSystem DU DB η cU cB g hg i₀
  let : Nonempty (Set.Ici i₀) := ⟨⟨i₀, le_rfl⟩⟩
  have hcomparison : IsIso (AbelianLimitStageSystem.comparison A S K₀ p) :=
    AbelianLimitStageSystem.isIso_comparison_of_single A S
      (fun F q ↦ relativeDerivedImage_single_limit DU DB η cU hcU cB hcB g hg i₀ F q) K₀ p
  let D₀ := AbelianLimitStageSystem.diagram A S K₀ p
  let c₀ := AbelianLimitStageSystem.cocone A S K₀ p
  let D := opOp (Set.Ici i₀) ⋙ D₀
  let c := c₀.whisker (opOp (Set.Ici i₀))
  let Z := (DerivedCategory.Plus.homologyFunctor _ p).obj
    ((rightDerivedLowerStarPlus A g).obj
      ((upperStar A (cU.π.app (op i₀))).mapDerivedCategoryPlus.obj K₀))
  let χ (i : Set.Ici i₀) :=
    ((upperStar A (cB.π.app (op i.val))).mapDerivedCategoryPlusHomologyFunctorIso p).app
      ((rightDerivedLowerStarPlus A (η.app (op i.val))).obj
        (relativeDerivedImageCoefficient DU i₀ K₀ i))
  let χ₀ := ((upperStar A (𝟙 cB.pt)).mapDerivedCategoryPlusHomologyFunctorIso p).app
    ((rightDerivedLowerStarPlus A g).obj
      ((upperStar A (cU.π.app (op i₀))).mapDerivedCategoryPlus.obj K₀))
  let t := χ₀.symm ≪≫ (upperStarId A cB.pt).app Z
  refine ⟨D, fun i ↦ (χ i).symm, c, ?_, t, ?_, ?_⟩
  · intro i j h
    apply (cancel_epi (χ i).hom).mp
    simp only [Iso.symm_hom, Iso.symm_inv, Iso.hom_inv_id_assoc]
    exact AbelianLimitStage.transition_homology A (S.map h.op) K₀ p
  · intro i
    apply (cancel_epi (χ i).hom).mp
    simp only [Iso.symm_hom, Iso.hom_inv_id_assoc]
    have ht := AbelianLimitStage.transition_homology A (S.π (op i)) K₀ p
    change ((χ i).hom ≫ (DerivedCategory.Plus.homologyFunctor _ p).map
        ((AbelianLimitStage.transition A (S.π (op i))).app K₀)) ≫
        χ₀.inv ≫ ((upperStarId A cB.pt).app Z).hom = _
    erw [ht]
    dsimp only [S, relativeLimitStageSystem, χ₀]
    simp only [Iso.app_inv, Category.assoc, Iso.hom_inv_id_app_assoc]
    dsimp only [relativeDerivedImageLeg, relativeDerivedImageCohomologyMap, χ, A, Z]
    rw [upperStarComp_id_left]
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.rightUnitor_inv_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
      Category.id_comp, Iso.app_hom]
    erw [NatTrans.naturality, Iso.inv_hom_id_app_assoc]
    rfl
  · have : IsIso ((colimit.isColimit D₀).desc c₀) := hcomparison
    have hc₀ : IsColimit c₀ := (colimit.isColimit D₀).ofPointIso
    exact ⟨hc₀.whiskerEquivalence (opOpEquivalence (Set.Ici i₀)).symm⟩

end AlgebraicGeometry.Etale
