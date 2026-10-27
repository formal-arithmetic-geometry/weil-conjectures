/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Topology.Stratification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.SixFunctors.ComparisonOpenTensorCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Etale-to-pro-etale comparison of the direct-image projection morphism

Source: Stacks Project, Tags 09A6, 07A4 and 0E48; main-20261015 blueprint,
finite proper base change proof, paragraph (3), canonical-map transport
(blueprint: lem-sfb-projection-comparison-etale-proetale).

The two routes are components of a single natural transformation on the full
subcategory of admissible pairs. This records both their equality and its
naturality, including arbitrary morphisms in both inputs. All operations are
ordinary uncompleted constant-coefficient operations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [local irreducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.leftDerivedFunctor

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

open CategoryTheory.Functor

private lemma normalize_counit_square
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (F F0 : D ⥤ C) (G G0 : D' ⥤ C') (N : D ⥤ D') (M : C ⥤ C')
    (ie : F ≅ F0) (ip : G ≅ G0) (a : F ⋙ M ≅ N ⋙ G)
    (s : F0 ⋙ M ≅ N ⋙ G0)
    (ht : ∀ Z : D, s.hom.app Z ≫ ip.inv.app (N.obj Z) =
      M.map (ie.inv.app Z) ≫ a.hom.app Z)
    {K : C} {Z W : D} {T : D'} (c : Z ≅ W) (b : N.obj Z ⟶ T)
    (eps : F.obj W ⟶ K) (eps' : G.obj T ⟶ M.obj K)
    (h : s.hom.app Z ≫ G0.map b ≫ ip.inv.app T ≫ eps' =
      M.map (F0.map c.hom) ≫ M.map (ie.inv.app W) ≫ M.map eps) :
    a.inv.app W ≫ M.map eps = G.map (N.map c.inv ≫ b) ≫ eps' := by
  rw [ip.inv.naturality_assoc, reassoc_of% (ht Z)] at h
  rw [← M.map_comp_assoc, ie.inv.naturality, M.map_comp, Category.assoc] at h
  have hh := (cancel_epi (M.map (ie.inv.app Z))).1 h
  rw [← cancel_epi (a.hom.app W), Iso.hom_inv_id_app_assoc]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := a.hom.naturality c.inv
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, hh]
  rw [← M.map_comp_assoc, ← F.map_comp, c.inv_hom_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]

namespace AlgebraicGeometry.ProEtale

private lemma map_plus_comp_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusCompIso F G).inv.app K) =
      (Functor.mapDerivedCategoryCompIso F G).inv.app K.obj := by
  exact congrArg Iso.inv (show DerivedCategory.Plus.ι.mapIso
    ((Functor.mapDerivedCategoryPlusCompIso F G).app K) =
      (Functor.mapDerivedCategoryCompIso F G).app K.obj from
    Iso.ext (Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app F G K))

private lemma included_pullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map ((fixedComparisonPullbackPlus A p).hom.app K) =
      (Functor.mapDerivedCategorySquareIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) p).symm).hom.app
          K.obj := by
  simp only [fixedComparisonPullbackPlus, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, map_plus_comp_inv,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
    Functor.mapDerivedCategorySquareIso]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma comparison_direct_image_eq_mate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (mateEquiv (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (comparisonOpenDerivedPullbackIso A p).inv).app K.obj =
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
      ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.inv.app K) ≫
    DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus A p).app K) ≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj K) := by
  apply ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, mateEquiv_counit, Functor.map_comp, Category.assoc]
  have h := congrArg DerivedCategory.Plus.ι.map
    (fixedComparisonDirectImageMatePlus_counit A p K)
  have he : DerivedCategory.Plus.ι.map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) p).counit.app K) =
      (Etale.upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.map
        ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
      ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).ofNatIsoLeft
        (Etale.upperStar (ModuleCat A) p).leftDerivedFunctorIsoMapDerivedCategory).counit.app
          K.obj := by
    unfold Etale.derivedUpperStarLowerStarAdjunctionPlus Adjunction.derivedAdjunctionPlus
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_inv, Iso.refl_hom,
      NatTrans.id_app, Category.id_comp]
    rfl
  have hp : DerivedCategory.Plus.ι.map
      ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) p).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj K)) =
      (upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.map
        ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj K)) ≫
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).ofNatIsoLeft
        (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctorIsoMapDerivedCategory).counit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K.obj) := by
    unfold derivedUpperStarLowerStarAdjunctionPlus Adjunction.derivedAdjunctionPlus
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_inv, Iso.refl_hom,
      NatTrans.id_app, Category.id_comp]
    rfl
  simp only [Functor.map_comp] at h
  change _ ≫ (upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.map
    (DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus A p).app K)) ≫ _ =
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus
          (ModuleCat.{u + 1} A) p).counit.app K)) at h
  rw [he, hp] at h
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.map_comp] at h
  let Fe := Etale.upperStar (ModuleCat.{u + 1} A) p
  let Fp := upperStar (ModuleCat.{u + 1} A) p
  let FX := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let FY := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
  let ie := Fe.leftDerivedFunctorIsoMapDerivedCategory
  let ip := Fp.leftDerivedFunctorIsoMapDerivedCategory
  let a := comparisonOpenDerivedPullbackIso A p
  have ht (Z : Etale.DerivedCategoryModule A Y) :
      (Functor.mapDerivedCategorySquareIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) p).symm).hom.app Z ≫
        ip.inv.app (FY.obj Z) = FX.map (ie.inv.app Z) ≫ a.hom.app Z := by
    simp only [a, comparisonOpenDerivedPullbackIso, supportComparison_eq,
      Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Etale.leftDerivedUpperStarIsoMapDerivedCategory, ie, Fe, FX, Category.assoc,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    dsimp only [ip, Fp, FY, leftDerivedUpperStarIsoMapDerivedCategory]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [included_pullback] at h
  let sq := Functor.mapDerivedCategorySquareIso
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) p).symm
  let c := (Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.app K
  let bb := DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus A p).app K) ≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj K)
  have hh := normalize_counit_square Fe.leftDerivedFunctor Fe.mapDerivedCategory
    Fp.leftDerivedFunctor Fp.mapDerivedCategory FY FX ie ip a sq ht c bb
    ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).counit.app K.obj)
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).counit.app (FX.obj K.obj))
    (by
      simp only [bb, CategoryTheory.Functor.map_comp, Category.assoc]
      exact h)
  simp only [bb, CategoryTheory.Functor.map_comp, Category.assoc] at hh
  exact hh

private lemma comparison_direct_image_inclusion
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
      ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.inv.app K) ≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlusCompatibility.inv.app
      ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) p).obj K) ≫
    DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus A p).app K) ≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj K) ≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlusCompatibility.hom.app
        K) =
    (mateEquiv (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (comparisonOpenDerivedPullbackIso A p).inv).app K.obj := by
  simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact (comparison_direct_image_eq_mate A p K).symm

/-- The admissible pairs: K and K tensor p* N are bounded below; N is unrestricted.
This is a property of pairs in the existing unbounded derived categories.
Source: Stacks Tags 09A6 and 0E48; finite proper base change proof, paragraph (3)
(blueprint: lem-sfb-projection-comparison-etale-proetale). -/
def sfbProjectionComparisonAdmissible (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    ObjectProperty (Etale.DerivedCategoryModule A X × Etale.DerivedCategoryModule A Y) :=
  fun B ↦ (∃ n : ℤ, B.1.IsGE n) ∧
    ∃ n : ℤ, (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj B.1).obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj B.2)).IsGE n

/-- The common source F_Y(R_e K tensor N), functorially on admissible pairs.
Source: Stacks Tag 0E48; finite proper base change proof, paragraph (3)
(blueprint: lem-sfb-projection-comparison-etale-proetale). -/
def sfbProjectionComparisonSource (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (sfbProjectionComparisonAdmissible A p).FullSubcategory ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) :=
  (sfbProjectionComparisonAdmissible A p).ι ⋙
    Functor.uncurry.obj (Etale.derivedTensorRightDerivedLowerStar (ModuleCat.{u + 1} A) p) ⋙
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory

/-- The common target R_p(F_X K tensor v F_Y N), functorially on admissible pairs.
Source: Stacks Tag 0E48; finite proper base change proof, paragraph (3)
(blueprint: lem-sfb-projection-comparison-etale-proetale). -/
def sfbProjectionComparisonTarget (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (sfbProjectionComparisonAdmissible A p).FullSubcategory ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) :=
  (sfbProjectionComparisonAdmissible A p).ι ⋙
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.prod
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory) ⋙
    Functor.uncurry.obj
      (rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar (ModuleCat.{u + 1} A) p)

/-- The compact admissibility interface is exactly the two bounds in the node.
Source: Stacks Tags 09A6 and 0E48; finite proper base change proof, paragraph (3)
(blueprint: lem-sfb-projection-comparison-etale-proetale).
Proof: unfold the admissibility property; its two conjuncts are these two bounds. -/
theorem sfbProjectionComparisonAdmissible_iff (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (B : Etale.DerivedCategoryModule A X × Etale.DerivedCategoryModule A Y) :
    sfbProjectionComparisonAdmissible A p B ↔
      (∃ n : ℤ, B.1.IsGE n) ∧
        ∃ n : ℤ, (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj B.1).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj B.2)).IsGE n := by
  rfl

/-- The source interface denotes exactly F_Y(R_e K tensor N), on objects and maps.
Source: Stacks Tag 0E48; finite proper base change proof, paragraph (3)
(blueprint: lem-sfb-projection-comparison-etale-proetale).
Proof: unfold the source interface; it is this composite of existing functors. -/
theorem sfbProjectionComparisonSource_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    sfbProjectionComparisonSource A p =
      (sfbProjectionComparisonAdmissible A p).ι ⋙
        Functor.uncurry.obj
          (Etale.derivedTensorRightDerivedLowerStar (ModuleCat.{u + 1} A) p) ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory := by
  rfl

/-- The target interface denotes exactly R_p(F_X K tensor v F_Y N), on objects and maps.
Source: Stacks Tag 0E48; finite proper base change proof, paragraph (3)
(blueprint: lem-sfb-projection-comparison-etale-proetale).
Proof: unfold the target interface; it is this composite of existing functors. -/
theorem sfbProjectionComparisonTarget_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    sfbProjectionComparisonTarget A p =
      (sfbProjectionComparisonAdmissible A p).ι ⋙
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.prod
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory) ⋙
        Functor.uncurry.obj
          (rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar (ModuleCat.{u + 1} A) p) := by
  rfl

/-- The canonical etale and pro-etale projection morphisms agree through the
specified comparison maps, naturally in both inputs. The first component formula
is F_Y(pi_e), then b_L, then R_p(h); the second is t_Y, then b_K tensor 1,
then pi_p. Here comparisonOpenTensorIso is defined for every scheme morphism:
its hom is exactly t_X followed by 1 tensor the canonical pullback comparison.
The direct-image morphism is fixedComparisonDirectImageMatePlus included into
the unbounded categories using the standard D+ compatibility isomorphisms.
The five arrows implementing that inclusion are written out at K and L.
Thus neither comparison is an arbitrary isomorphism between the endpoints.

Source: Stacks Tags 09A6, 07A4 and 0E48; main-20261015 blueprint, finite proper
base change proof, paragraph (3)
(blueprint: lem-sfb-projection-comparison-etale-proetale).

Proof:
1. Transport the existing tensor-compatible fixed-coefficient derived comparison
along the horizontal exact-functor comparison isomorphisms. Its tensorators become
exactly the published mapDerivedCategory tensor comparisons, and its pullback
square is comparisonOpenDerivedPullbackIso.
2. Include the specified bounded-below mate's counit identity into the unbounded
categories. The formulas for included restricted counits and pullback comparisons,
followed by cancellation and naturality, identify it with the unbounded mate.
Apply this at both K and L; no bound on N is required.
3. Apply the general tensor-compatible projection-mate identity to the unbounded
derived adjunctions. Their projection maps are definitionally the published ones,
and the target tensor comparison is comparisonOpenTensorIso. Substitute step 2.
4. Compose the natural tensorator, tensor of the mate with identity, and pro-etale
projection transformation. Uncurry and restrict to admissible pairs. This gives
the common natural transformation and both displayed component formulas.
No properness, constructibility, Tor amplitude, or invertibility of either
projection morphism enters this argument. -/
theorem projection_comparison_etale_proetale (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p] :
    ∃ alpha : sfbProjectionComparisonSource A p ⟶ sfbProjectionComparisonTarget A p,
      ∀ B : (sfbProjectionComparisonAdmissible A p).FullSubcategory,
        alpha.app B =
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
            (((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p).app
              B.obj.1).app B.obj.2) ≫
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
            ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.inv.app
              ⟨(((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj B.obj.1).obj
                  ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj B.obj.2)),
                B.property.2⟩) ≫
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlusCompatibility.inv.app
            ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) p).obj
              ⟨(((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj B.obj.1).obj
                  ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj B.obj.2)),
                B.property.2⟩)) ≫
          DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus A p).app
            ⟨(((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj B.obj.1).obj
                  ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj B.obj.2)),
                B.property.2⟩) ≫
          (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj
              ⟨(((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj B.obj.1).obj
                  ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj B.obj.2)),
                B.property.2⟩) ≫
          (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
            ((Functor.mapDerivedCategoryPlusCompatibility
                (comparisonUpperStar (ModuleCat.{u + 1} A) X)).hom.app
              ⟨(((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj B.obj.1).obj
                  ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj B.obj.2)),
                B.property.2⟩) ≫
          (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
            (comparisonOpenTensorIso A p B.obj.1 B.obj.2).hom ∧
        alpha.app B =
          ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
            (ModuleCat.{u + 1} A)
            ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj B.obj.1)).app
              B.obj.2).hom ≫
          ((derivedTensor (ModuleCat.{u + 1} A) Y).map
            (
              (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
                ((Functor.rightDerivedFunctorPlusCompatibility
                    (Etale.lowerStar (ModuleCat.{u + 1} A) p)).inv.app
                  ⟨B.obj.1, B.property.1⟩) ≫
              ((Functor.mapDerivedCategoryPlusCompatibility
                  (comparisonUpperStar (ModuleCat.{u + 1} A) Y)).inv.app
                ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) p).obj
                  ⟨B.obj.1, B.property.1⟩)) ≫
              DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus A p).app
                ⟨B.obj.1, B.property.1⟩) ≫
              (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app
                ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj
                  ⟨B.obj.1, B.property.1⟩) ≫
              (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
                ((Functor.mapDerivedCategoryPlusCompatibility
                    (comparisonUpperStar (ModuleCat.{u + 1} A) X)).hom.app
                  ⟨B.obj.1, B.property.1⟩))).app
              ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj B.obj.2) ≫
          (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p).app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
              B.obj.1)).app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj B.obj.2)) := by
  let FX := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let FY := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
  let Re := (Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor
  let Rp := (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor
  let b := (mateEquiv
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (comparisonOpenDerivedPullbackIso A p).inv).natTrans
  let pre := (whiskeringLeft (Etale.DerivedCategoryModule A Y)
    (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))).obj FY
  let t := Functor.whiskerLeft Re (comparisonTensorNatIso A Y).hom
  let z := Functor.whiskerRight
    (Functor.whiskerRight b (derivedTensor (ModuleCat.{u + 1} A) Y)) pre
  let q := Functor.whiskerLeft FX (Functor.whiskerRight
    (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p) pre)
  let alpha0 := Functor.uncurry.map (t ≫ z ≫ q)
  let alpha : sfbProjectionComparisonSource A p ⟶ sfbProjectionComparisonTarget A p :=
    { app := fun B ↦ alpha0.app B.obj
      naturality := by
        intro B C f
        have hn := alpha0.naturality f.hom
        change FY.map
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).map
            (Re.map f.hom.1)).app B.obj.2 ≫
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).obj
              (Re.obj C.obj.1)).map f.hom.2) ≫ _ = _
        rw [FY.map_comp]
        exact hn }
  refine ⟨alpha, ?_⟩
  intro B
  have h := Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (comparison_tensor_compatible A p) B.obj.1 B.obj.2
  simp only [← Iso.app_hom] at h
  simp only [comparison_tensor_app, Iso.app_hom, Iso.symm_inv] at h
  have hbK := comparison_direct_image_inclusion A p ⟨B.obj.1, B.property.1⟩
  have hbL := comparison_direct_image_inclusion A p
    ⟨(((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj B.obj.1).obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj B.obj.2)),
      B.property.2⟩
  have ha : alpha.app B =
      ((comparisonTensorNatIso A Y).hom.app (Re.obj B.obj.1)).app B.obj.2 ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map (b.app B.obj.1)).app
        (FY.obj B.obj.2) ≫
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p).app
        (FX.obj B.obj.1)).app (FY.obj B.obj.2) := by
    rfl
  simp only [← Iso.app_hom] at ha
  simp only [comparison_tensor_app, Iso.app_hom] at ha
  change FY.map (((Etale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} A) p).app B.obj.1).app B.obj.2) ≫
    b.app (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj B.obj.1).obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj B.obj.2)) ≫
    Rp.map (comparisonOpenTensorIso A p B.obj.1 B.obj.2).hom = _ at h
  change _ = b.app B.obj.1 at hbK
  change _ = b.app (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj B.obj.1).obj
    ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj B.obj.2)) at hbL
  constructor
  · erw [reassoc_of% hbL]
    exact ha.trans h.symm
  · erw [hbK]
    exact ha

end AlgebraicGeometry.ProEtale
