/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSupportedKernelAdjunction
public import WeilConjectures.RingTheory.IndEtaleUniverseTransport
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Adjunction.Mates

import WeilConjectures.AlgebraicGeometry.ClosedDirectImagePlusCoherence
import WeilConjectures.AlgebraicGeometry.ClosedSupportPlusLocalization
import WeilConjectures.AlgebraicGeometry.IndEtaleOpenLocalizationComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension

/-!
# Ind-etale base change for closed etale support

Source: Stacks Project, Tags 03Q9, 09XQ and 0A45
(blueprint: lem-per-ind-etale-closed-support-base-change).

The comparison is constructed as the mate of inverse finite exchange, with the actual
bounded-below right derived supported inverse image. All categories have A-module values.
Complementary open immersions are explicit so the existing support construction is reused.

## Main definitions and statement

- `closedDirectImageBaseChangePlus`: exact, termwise closed direct-image exchange.
- `closedSupportBaseChangePlus`: its canonical adjunction mate.
- `indEtale_closedSupport_baseChange`: invertibility, counit, shifts and pasting.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Functor CategoryTheory.TwoSquare

-- The next two generic proofs are the coefficient-independent private helpers of
-- WeilConjectures.AlgebraicGeometry.DerivedAdjunctionCommShift, reused for support adjunctions.
-- The bounded below inclusion is faithful and its lift comparison isos commute with shifts.
private theorem plusHomotopyUnit_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R) :
    NatTrans.CommShift adj.mapHomotopyCategoryPlus.unit ℤ := by
  have heq : Functor.whiskerRight adj.mapHomotopyCategoryPlus.unit
      (HomotopyCategory.Plus.ι C) =
      (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv ≫
        Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
          (adj.mapHomotopyCategory (.up ℤ)).unit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight ((HomotopyCategory.plus D).liftCompιIso _ _).inv
          (R.mapHomotopyCategory (.up ℤ)) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L.mapHomotopyCategoryPlus
          ((HomotopyCategory.plus C).liftCompιIso _ _).inv ≫
        (Functor.associator _ _ _).inv := by
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      ObjectProperty.liftCompιIso, Iso.refl_inv, NatTrans.id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp,
      Category.comp_id, Category.comp_id, Category.comp_id]
    dsimp only [Functor.comp_obj, ObjectProperty.ι_obj]
    simp only [Category.comp_id]
  have : NatTrans.CommShift (Functor.whiskerRight adj.mapHomotopyCategoryPlus.unit
      (HomotopyCategory.Plus.ι C)) ℤ := by
    rw [heq]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ (HomotopyCategory.Plus.ι C)

-- Compute the derived unit on the localization image, then use essential surjectivity.
private theorem derivedUnit_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [Limits.PreservesFiniteLimits L] [Limits.PreservesFiniteColimits L] (adj : L ⊣ R) :
    NatTrans.CommShift adj.derivedPlus.unit ℤ := by
  have := plusHomotopyUnit_commShift adj
  have heq : Functor.whiskerLeft DerivedCategory.Plus.Qh adj.derivedPlus.unit =
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight adj.mapHomotopyCategoryPlus.unit DerivedCategory.Plus.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L.mapHomotopyCategoryPlus R.rightDerivedFunctorPlusUnit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.inv R.rightDerivedFunctorPlus ≫
        (Functor.associator _ _ _).hom := by
    refine NatTrans.ext (funext fun K ↦ ?_)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Category.id_comp]
    simp only [Category.comp_id]
    rw [← cancel_mono (R.rightDerivedFunctorPlus.map
      (L.mapDerivedCategoryPlusFactorsh.hom.app K)),
      Adjunction.derivedPlus_unit_app_fac]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    dsimp only [Functor.comp_obj]
    simp only [Category.comp_id]
    exact (Category.id_comp _).symm
  have : NatTrans.CommShift
      (Functor.whiskerLeft DerivedCategory.Plus.Qh adj.derivedPlus.unit) ℤ := by
    rw [heq]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Plus.Qh
    (fun X ↦ ⟨DerivedCategory.Plus.Qh.objPreimage X,
      (DerivedCategory.Plus.Qh.objObjPreimageIso X).inv, inferInstance⟩)


namespace CategoryTheory.Functor

private theorem plusCompatibility_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    NatTrans.CommShift F.mapDerivedCategoryPlusCompatibility.hom ℤ := by
  change NatTrans.CommShift
    (DerivedCategory.TStructure.t.plus.liftCompιIso
      (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory)
      (fun X ↦ (F.mapDerivedCategoryPlus.obj X).2)).hom ℤ
  infer_instance

private theorem plusNatIso_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    NatTrans.CommShift (mapDerivedCategoryPlusNatIso e).hom ℤ := by
  have he : whiskerRight (mapDerivedCategoryPlusNatIso e).hom DerivedCategory.Plus.ι =
      F.mapDerivedCategoryPlusCompatibility.hom ≫
        whiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryNatIso e).hom ≫
          G.mapDerivedCategoryPlusCompatibility.inv := by
    apply NatTrans.ext
    funext X
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    rw [ι_map_mapDerivedCategoryPlusNatIso_hom_app]
    dsimp only [mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Functor.comp_obj]
    erw [Category.id_comp, Category.comp_id]
  have : NatTrans.CommShift
      (whiskerRight (mapDerivedCategoryPlusNatIso e).hom DerivedCategory.Plus.ι) ℤ := by
    rw [he]
    have := plusCompatibility_commShift F
    have := plusCompatibility_commShift G
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ DerivedCategory.Plus.ι

private theorem plusCompIso_commShift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)] :
    NatTrans.CommShift (mapDerivedCategoryPlusCompIso F G).hom ℤ := by
  have he : whiskerRight (mapDerivedCategoryPlusCompIso F G).hom DerivedCategory.Plus.ι =
      (F ⋙ G).mapDerivedCategoryPlusCompatibility.hom ≫
        whiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryCompIso F G).hom ≫
        (associator _ _ _).inv ≫
        whiskerRight F.mapDerivedCategoryPlusCompatibility.inv G.mapDerivedCategory ≫
        (associator _ _ _).hom ≫
        whiskerLeft F.mapDerivedCategoryPlus G.mapDerivedCategoryPlusCompatibility.inv ≫
        (associator _ _ _).inv := by
    apply NatTrans.ext
    funext X
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      associator_hom_app, associator_inv_app]
    rw [ι_map_mapDerivedCategoryPlusCompIso_hom_app]
    dsimp only [mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Functor.comp_obj]
    erw [Category.id_comp, CategoryTheory.Functor.map_id]
    repeat erw [Category.comp_id]
  have : NatTrans.CommShift
      (whiskerRight (mapDerivedCategoryPlusCompIso F G).hom DerivedCategory.Plus.ι) ℤ := by
    rw [he]
    have := plusCompatibility_commShift F
    have := plusCompatibility_commShift G
    have := plusCompatibility_commShift (F ⋙ G)
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ DerivedCategory.Plus.ι


end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Closed direct-image exchange, localized termwise on bounded-below complexes.
Source: Stacks Project, Tag 04CA, finite exchange and exact closed direct image
(blueprint: lem-per-ind-etale-closed-support-base-change). -/
noncomputable def closedDirectImageBaseChangePlus
    (A : Type (u + 1)) [CommRing A]
    {Z Z' T T' : Scheme.{u}} (i : Z ⟶ T) (i' : Z' ⟶ T')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (h : Z' ⟶ Z) (g : T' ⟶ T) (sq : IsPullback h i' i g) :
    (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus ≅
      (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} A) i').mapDerivedCategoryPlus :=
  have := isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} A) sq
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (asIso (baseChangeMap (ModuleCat.{u + 1} A)
      sq.toCommSq)) ≪≫ Functor.mapDerivedCategoryPlusCompIso _ _

/-- The canonical closed-support comparison: mate of inverse closed direct-image exchange
under the bounded-below derived support adjunctions. The right adjoints are precisely
`R⁺(i⁻¹ ker(id → j_*j⁻¹))`, with their resolution-normalized counits.
Source: Stacks Project, Tags 09XQ and 0A45
(blueprint: lem-per-ind-etale-closed-support-base-change). -/
noncomputable def closedSupportBaseChangePlus
    (A : Type (u + 1)) [CommRing A]
    {Z Z' T T' U U' : Scheme.{u}} (i : Z ⟶ T) (i' : Z' ⟶ T')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (j : U ⟶ T) (j' : U' ⟶ T') [IsOpenImmersion j] [IsOpenImmersion j']
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hij' : Set.range i'.base = (Set.range j'.base)ᶜ)
    (h : Z' ⟶ Z) (g : T' ⟶ T) (sq : IsPullback h i' i g) :
    (closedUpperShriek (ModuleCat.{u + 1} A) i j).rightDerivedFunctorPlus ⋙
        (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategoryPlus ⟶
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus ⋙
        (closedUpperShriek (ModuleCat.{u + 1} A) i' j').rightDerivedFunctorPlus :=
  (mateEquiv
    (lowerStarClosedUpperShriekAdjunction (ModuleCat.{u + 1} A) i j hij).derivedPlus
    (lowerStarClosedUpperShriekAdjunction (ModuleCat.{u + 1} A) i' j' hij').derivedPlus
    (TwoSquare.mk _ _ _ _ (closedDirectImageBaseChangePlus A i i' h g sq).inv)).natTrans

/-- Ind-etale base change for the closed-support right adjoint on all D⁺ of constant
A-module etale sheaves, without constructibility or invertibility assumptions.
The mate is invertible, commutes with shifts, satisfies the closed counit equation,
and pastes under successive affine locally ind-etale base changes.

Source: Stacks Project, Tags 03Q9, 09XQ and 0A45
(blueprint: lem-per-ind-etale-closed-support-base-change).

Proof:
1. The complementary open j is qcqs, since T is Noetherian; its base change is the
   complement of i' (closed/open base change and Noetherian open-subscheme lemmas).
2. The supported kernel adjunction restricts to A-linear maps. Closed direct image
   is exact, and module sheaves have enough injectives. Derive this adjunction on D⁺
   (lem-trf-bounded-below-derived-adjunction).
3. Identify it with the ambient right adjoint by uniqueness and the standard
   t-structure. Use lem-exc-closed-support-triangle with its counit and open unit.
4. Finite exchange supplies the closed direct-image isomorphism. Invertible ordinary
   closed counits imply that i'_* reflects isomorphisms on D⁺.
5. The mate definition is the transpose of inverse exchange followed by g^* of the
   closed counit; the adjunction bijection proves exactly the asserted counit identity.
6. Apply lem-per-ind-etale-qcqs-direct-image-base-change to j and j^*K. This identifies
   the third terms of the two support triangles, without constructibility assumptions.
7. Open-closed disjointness and the open derived adjunction give Hom(B[r], C') = 0
   for all r, where B is the pulled-back supported term and C' the open direct image.
8. The counit identity supplies the first square, and the ordinary exchange mate
   supplies the open-unit square. Triangle-morphism extension with Hom(B[1], C') = 0
   gives a morphism of the actual support triangles, including the connecting square.
9. Two-out-of-three makes i'_*(beta) invertible; reflection by i'_* proves the claim.
   Every construction lies in the A-module categories, hence all comparisons are linear.
10. Ordinary closed exchange pastes by inverse-image coherence and mate pasting.
    Localize termwise and take mates again to obtain the asserted composition identity.
11. Exact inverse/direct images have termwise shift comparisons. Uniqueness of the
    adjoint shift structure identifies the support shift with the right-derived shift.
    Transpose the shifted counit equation to obtain the stated shift compatibility. -/
theorem indEtale_closedSupport_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z Z' T T' U U' : Scheme.{u}} [IsNoetherian T] [IsNoetherian T']
    (i : Z ⟶ T) (i' : Z' ⟶ T') [IsClosedImmersion i] [IsClosedImmersion i']
    (j : U ⟶ T) (j' : U' ⟶ T') [IsOpenImmersion j] [IsOpenImmersion j']
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hij' : Set.range i'.base = (Set.range j'.base)ᶜ)
    (h : Z' ⟶ Z) (g : T' ⟶ T) [IsAffineHom g]
    (hg : ∀ V : T.Opens, IsAffineOpen V →
      RingHom.IndEtaleAcrossUniverses (g.app V).hom)
    (sq : IsPullback h i' i g) :
    IsIso (closedSupportBaseChangePlus A i i' j j' hij hij' h g sq) ∧
      NatTrans.CommShift (closedSupportBaseChangePlus A i i' j j' hij hij' h g sq) ℤ ∧
      (∀ K : _root_.DerivedCategory.Plus
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (closedDirectImageBaseChangePlus A i i' h g sq).hom.app
            ((closedUpperShriek (ModuleCat.{u + 1} A) i j).rightDerivedFunctorPlus.obj K) ≫
          (lowerStar (ModuleCat.{u + 1} A) i').mapDerivedCategoryPlus.map
            ((closedSupportBaseChangePlus A i i' j j' hij hij' h g sq).app K) ≫
          (lowerStarClosedUpperShriekAdjunction (ModuleCat.{u + 1} A)
            i' j' hij').derivedPlus.counit.app
              ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.obj K) =
        (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.map
          ((lowerStarClosedUpperShriekAdjunction (ModuleCat.{u + 1} A)
            i j hij).derivedPlus.counit.app K)) ∧
      (∀ (Z'' T'' U'' : Scheme.{u}) [IsNoetherian T'']
          (i'' : Z'' ⟶ T'') [IsClosedImmersion i'']
          (j'' : U'' ⟶ T'') [IsOpenImmersion j'']
          (hij'' : Set.range i''.base = (Set.range j''.base)ᶜ)
          (h₂ : Z'' ⟶ Z') (g₂ : T'' ⟶ T') [IsAffineHom g₂]
          (_hg₂ : ∀ V : T'.Opens, IsAffineOpen V →
            RingHom.IndEtaleAcrossUniverses (g₂.app V).hom)
          (sq₂ : IsPullback h₂ i'' i' g₂)
          (K : _root_.DerivedCategory.Plus
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))),
        (upperStarCompDerivedPlus (ModuleCat.{u + 1} A) h₂ h).hom.app
            ((closedUpperShriek (ModuleCat.{u + 1} A) i j).rightDerivedFunctorPlus.obj K) ≫
          (upperStar (ModuleCat.{u + 1} A) h₂).mapDerivedCategoryPlus.map
            ((closedSupportBaseChangePlus A i i' j j' hij hij' h g sq).app K) ≫
          (closedSupportBaseChangePlus A i' i'' j' j'' hij' hij'' h₂ g₂ sq₂).app
            ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.obj K) =
        (closedSupportBaseChangePlus A i i'' j j'' hij hij'' (h₂ ≫ h) (g₂ ≫ g)
          (sq₂.paste_horiz sq)).app K ≫
          (closedUpperShriek (ModuleCat.{u + 1} A) i'' j'').rightDerivedFunctorPlus.map
            ((upperStarCompDerivedPlus (ModuleCat.{u + 1} A) g₂ g).hom.app K)) ∧
      (∀ K : _root_.DerivedCategory.Plus
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (closedSupportBaseChangePlus A i i j j hij hij (𝟙 Z) (𝟙 T)
            (IsPullback.id_horiz i)).app K ≫
          (closedUpperShriek (ModuleCat.{u + 1} A) i j).rightDerivedFunctorPlus.map
            ((upperStarIdDerivedPlus (ModuleCat.{u + 1} A) T).hom.app K) =
        (upperStarIdDerivedPlus (ModuleCat.{u + 1} A) Z).hom.app
          ((closedUpperShriek (ModuleCat.{u + 1} A) i j).rightDerivedFunctorPlus.obj K))  := by
  let C := ModuleCat.{u + 1} A
  let F' := (lowerStar C i').mapDerivedCategoryPlus
  let G := (upperStar C g).mapDerivedCategoryPlus
  let H := (upperStar C h).mapDerivedCategoryPlus
  let R := (closedUpperShriek C i j).rightDerivedFunctorPlus
  let adj := (lowerStarClosedUpperShriekAdjunction C i j hij).derivedPlus
  let adj' := (lowerStarClosedUpperShriekAdjunction C i' j' hij').derivedPlus
  let c := closedDirectImageBaseChangePlus A i i' h g sq
  let β := closedSupportBaseChangePlus A i i' j j' hij hij' h g sq
  have hcounit (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology C)) :
      c.hom.app (R.obj K) ≫ F'.map (β.app K) ≫
        adj'.counit.app (G.obj K) = G.map (adj.counit.app K) := by
    have hm : F'.map (β.app K) ≫ adj'.counit.app (G.obj K) =
        c.inv.app (R.obj K) ≫ G.map (adj.counit.app K) :=
      mateEquiv_counit adj adj' (TwoSquare.mk _ _ _ _ c.inv) K
    rw [hm, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have hiso : IsIso β := by
    have hreflect : F'.ReflectsIsomorphisms := by
      constructor
      intro X Y f hf
      rw [DerivedCategory.Plus.isIso_iff]
      intro n
      have : IsIso ((lowerStar C i').map
          ((DerivedCategory.Plus.homologyFunctor _ n).map f)) :=
        (NatIso.isIso_map_iff
          ((lowerStar C i').mapDerivedCategoryPlusHomologyFunctorIso n) f).2 (by
            rw [Functor.comp_map]
            infer_instance)
      exact isIso_of_reflects_iso _ (lowerStar C i')
    have hβ (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology C)) :
        IsIso (β.app K) := by
      obtain ⟨δ, hδ⟩ := (closedSupportPlus_localization A i j hij).1 K
      obtain ⟨δ', hδ'⟩ := (closedSupportPlus_localization A i' j' hij').1 (G.obj K)
      obtain ⟨E, hE⟩ := indEtale_openLocalization_comparison
        A i i' j j' hij hij' h g hg sq K
      let t := Triangle.mk (adj.counit.app K)
        ((upperStarLowerStarAdjunction C j).derivedPlus.unit.app K) δ
      let t' := Triangle.mk (adj'.counit.app (G.obj K))
        ((upperStarLowerStarAdjunction C j').derivedPlus.unit.app (G.obj K)) δ'
      have ht : G.mapTriangle.obj t ∈ distTriang _ :=
        G.map_distinguished t hδ
      let a := c.hom.app (R.obj K) ≫ F'.map (β.app K)
      have hfirst : a ≫ t'.mor₁ = (G.mapTriangle.obj t).mor₁ ≫ 𝟙 (G.obj K) := by
        change (c.hom.app (R.obj K) ≫ F'.map (β.app K)) ≫
          adj'.counit.app (G.obj K) = G.map (adj.counit.app K) ≫ 𝟙 _
        rw [Category.comp_id, Category.assoc]
        exact hcounit K
      have horth : Subsingleton
          (((G.mapTriangle.obj t).obj₁)⟦(1 : ℤ)⟧ ⟶ t'.obj₃) := by
        let e := (shiftFunctor _ (1 : ℤ)).mapIso (c.app (R.obj K))
        have hs : Subsingleton
            ((F'.obj (H.obj (R.obj K)))⟦(1 : ℤ)⟧ ⟶ t'.obj₃) :=
          (closedSupportPlus_localization A i' j' hij').2
            (H.obj (R.obj K))
            ((upperStar C j').mapDerivedCategoryPlus.obj (G.obj K)) 1
        refine ⟨fun f g => (Iso.homCongr e (Iso.refl t'.obj₃)).injective ?_⟩
        exact @Subsingleton.elim _ hs _ _
      obtain ⟨τ, hτ₁, hτ₂, hτ₃, _⟩ :=
        ((Pretriangulated.triangle_morphism_extension (G.mapTriangle.obj t) t'
          ht hδ' (𝟙 (G.obj K))).2.1 horth).2.2 a E.hom hfirst
          (by
            change G.map ((upperStarLowerStarAdjunction C j).derivedPlus.unit.app K) ≫
              E.hom = 𝟙 _ ≫
                (upperStarLowerStarAdjunction C j').derivedPlus.unit.app (G.obj K)
            rw [Category.id_comp]
            exact hE)
      have : IsIso τ.hom₂ := by
        rw [hτ₂]
        exact IsIso.id _
      have : IsIso τ.hom₃ := by rw [hτ₃]; infer_instance
      have : IsIso τ.hom₁ := Pretriangulated.isIso₁_of_isIso₂₃ τ ht hδ' (by infer_instance)
        (by infer_instance)
      have : IsIso a := by rwa [hτ₁] at this
      have : IsIso (F'.map (β.app K)) :=
        (isIso_comp_left_iff (c.hom.app (R.obj K)) _).1 this
      exact isIso_of_reflects_iso (β.app K) F'
    exact NatIso.isIso_of_isIso_app β
  have hshift : NatTrans.CommShift β ℤ := by
    have : adj.CommShift ℤ := Adjunction.CommShift.mk' _ ℤ
      (derivedUnit_commShift (lowerStarClosedUpperShriekAdjunction C i j hij))
    have : adj'.CommShift ℤ := Adjunction.CommShift.mk' _ ℤ
      (derivedUnit_commShift (lowerStarClosedUpperShriekAdjunction C i' j' hij'))
    have hc : NatTrans.CommShift c.hom ℤ := by
      have := isIso_baseChangeMap_of_isFinite C sq
      let : PreservesFiniteLimits (lowerStar C i ⋙ upperStar C g) :=
        comp_preservesFiniteLimits _ _
      let : PreservesFiniteColimits (lowerStar C i ⋙ upperStar C g) :=
        comp_preservesFiniteColimits _ _
      let : PreservesFiniteLimits (upperStar C h ⋙ lowerStar C i') :=
        comp_preservesFiniteLimits _ _
      let : PreservesFiniteColimits (upperStar C h ⋙ lowerStar C i') :=
        comp_preservesFiniteColimits _ _
      have := Functor.plusCompIso_commShift (lowerStar C i) (upperStar C g)
      have := Functor.plusCompIso_commShift (upperStar C h) (lowerStar C i')
      have := Functor.plusNatIso_commShift (asIso (baseChangeMap C sq.toCommSq))
      dsimp only [c, closedDirectImageBaseChangePlus, Iso.trans_hom, Iso.symm_hom]
      infer_instance
    exact NatTrans.CommShift.mateEquiv adj adj' (TwoSquare.mk _ _ _ _ c.inv)
  refine ⟨hiso, hshift, hcounit, ?_, ?_⟩
  · intro Z'' T'' U'' _ i'' _ j'' _ hij'' h₂ g₂ _ _ sq₂ K
    have hcoh := (closedDirectImagePlus_coherence A).1 i i' i'' h g h₂ g₂ sq sq₂
    change TwoSquare.mk _ _ _ _
      (closedDirectImageBaseChangePlus A i i'' (h₂ ≫ h) (g₂ ≫ g)
        (sq₂.paste_horiz sq)).inv = _ at hcoh
    have heq := congrArg (fun w =>
      (mateEquiv adj
        (lowerStarClosedUpperShriekAdjunction C i'' j'' hij'').derivedPlus w).app K) hcoh
    rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp adj adj'] at heq
    simp only [TwoSquare.whiskerRight_app, TwoSquare.whiskerLeft_app,
      TwoSquare.vComp_app, Functor.comp_obj, Category.assoc] at heq
    change (closedSupportBaseChangePlus A i i'' j j'' hij hij'' (h₂ ≫ h) (g₂ ≫ g)
        (sq₂.paste_horiz sq)).app K =
      (upperStarCompDerivedPlus C h₂ h).hom.app (R.obj K) ≫
        (upperStar C h₂).mapDerivedCategoryPlus.map
          ((closedSupportBaseChangePlus A i i' j j' hij hij' h g sq).app K) ≫
        (closedSupportBaseChangePlus A i' i'' j' j'' hij' hij'' h₂ g₂ sq₂).app (G.obj K) ≫
        (closedUpperShriek C i'' j'').rightDerivedFunctorPlus.map
          ((upperStarCompDerivedPlus C g₂ g).inv.app K) at heq
    rw [← cancel_mono ((closedUpperShriek C i'' j'').rightDerivedFunctorPlus.map
      ((upperStarCompDerivedPlus C g₂ g).inv.app K))]
    dsimp only [C]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id]
    exact heq.symm.trans (Category.comp_id _).symm
  · intro K
    have hcoh := (closedDirectImagePlus_coherence A).2 i
    change TwoSquare.mk _ _ _ _
      (closedDirectImageBaseChangePlus A i i (𝟙 Z) (𝟙 T)
        (IsPullback.id_horiz i)).inv = _ at hcoh
    have heq := congrArg (fun w => (mateEquiv adj adj w).app K) hcoh
    rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_unitors] at heq
    simp only [TwoSquare.whiskerRight_app, TwoSquare.whiskerLeft_app,
      NatTrans.comp_app, Functor.rightUnitor_hom_app,
      Functor.leftUnitor_inv_app, Category.comp_id] at heq
    change (closedSupportBaseChangePlus A i i j j hij hij (𝟙 Z) (𝟙 T)
      (IsPullback.id_horiz i)).app K = _ at heq
    rw [heq]
    simp only [C, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id]
    rw [Category.comp_id]
    exact Category.comp_id _

end AlgebraicGeometry.Etale
