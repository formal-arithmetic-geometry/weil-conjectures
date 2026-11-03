/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! # Condensed module exchange along scheme isomorphisms

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done/
def-tw-frobenius-action.md, well-definedness of ordinary and compact-support transport.
The source asserts the actions; the ringed-site transport argument is agent-written.
(blueprint: lem-sf-condensed-isomorphism-square-exchange).

The ordinary exchange is the existing canonical derived mate. The open comparison is
specified by equality with the inverse mate, and its derived comparison by the termwise
localization equation. All derived categories here are ordinary and unbounded.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Exact equivalences and invertibility of the actual derived direct-image exchange.
Source: def-tw-frobenius-action, ordinary transport; agent ringed-site argument
(blueprint: lem-sf-condensed-isomorphism-square-exchange).

Proof:
1. For a scheme isomorphism e, pullback upperStar e is an equivalence of the actual module
   categories (isEquivalence_upperStar_of_isIso, def-sfb-module-upper-star-comp): its
   inverse is upperStar along e⁻¹, with unit and counit built from upperStarId and
   upperStarComp. upperStar is additive and preserves finite limits and finite colimits
   (sk-def-sfb-module-pushforward-pullback). This gives the six underived clauses for u, v.
2. The left derived functor of an exact additive equivalence is an equivalence
   (def-sfb-left-derived-exact), so moduleObjectDerivedPullback u and v are equivalences.
3. The two derived compositors and the square equality give the specified square
   comparison theta (prop-sfb-module-left-derived-upper-star-comp). Apply
   lem-weil-mate-iso-along-equivalences to the derived adjunctions, with G = Lv*
   and G' = Lu*. Its mate is precisely moduleObjectDerivedExchange, so that arrow
   itself is invertible. No properness or restrictions on complexes enter. -/
theorem condensed_isomorphism_square_exchange
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {u : X' ⟶ X} {v : Y' ⟶ Y} [IsIso u] [IsIso v]
    (sq : CommSq u f' f v) :
    (upperStar Λ.X u).IsEquivalence ∧
    PreservesFiniteLimits (upperStar Λ.X u) ∧
    PreservesFiniteColimits (upperStar Λ.X u) ∧
    (upperStar Λ.X v).IsEquivalence ∧
    PreservesFiniteLimits (upperStar Λ.X v) ∧
    PreservesFiniteColimits (upperStar Λ.X v) ∧
    IsIso (moduleObjectDerivedExchange Λ.X sq) := by
  let : (moduleObjectDerivedPullback Λ.X u).IsEquivalence := by
    unfold moduleObjectDerivedPullback
    infer_instance
  let : (moduleObjectDerivedPullback Λ.X v).IsEquivalence := by
    unfold moduleObjectDerivedPullback
    infer_instance
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  exact isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (derivedUpperStarLowerStarAdjunction Λ.X f)
    (derivedUpperStarLowerStarAdjunction Λ.X f')
    (moduleObjectDerivedPullback Λ.X v)
    (moduleObjectDerivedPullback Λ.X u)
    (moduleObjectDerivedPullbackSquareComparison Λ.X sq)

private theorem exact_square_normalization
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : F ⋙ G ≅ H ⋙ I) :
    let eD := (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso H I
    ∀ K : CochainComplex A ℤ,
      eD.hom.app (DerivedCategory.Q.obj K) ≫
          I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
          I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
          G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K ≫
              (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K ≫
              (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ I)) (.up ℤ)).inv.app K) := by
  dsimp only
  intro K
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F
    G).hom.app (DerivedCategory.Q.obj K))).1
  apply (cancel_mono (DerivedCategory.Q.map
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (H ⋙ I))
      (.up ℤ)).hom.app K))).1
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp,
    Functor.mapDerivedCategoryCompIso_fac,
    Functor.mapDerivedCategoryCompIso_fac_assoc,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]

private theorem exact_inverse_mate_exchange
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [F.IsEquivalence] [I.IsEquivalence]
    (R : C ⥤ A) (S : D ⥤ B) (adj : H ⊣ R) (adj' : G ⊣ S)
    (beta : R ⋙ F ≅ I ⋙ S) :
    ∃ e : F ⋙ G ≅ H ⋙ I,
      e.hom = ((mateEquiv adj adj').symm beta.hom).natTrans ∧
      ∃ eD : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
          H.mapDerivedCategory ⋙ I.mapDerivedCategory,
        ∀ K : CochainComplex A ℤ,
          eD.hom.app (DerivedCategory.Q.obj K) ≫
              I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
              I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
            G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
              G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
              DerivedCategory.Q.map
                ((Functor.mapHomologicalComplexCompIso
                    (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K ≫
                  (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K ≫
                  (Functor.mapHomologicalComplexCompIso
                    (Iso.refl (H ⋙ I)) (.up ℤ)).inv.app K) := by
  have hα := isIso_inverseMate_of_equivalences adj adj' beta
  let e := asIso (((mateEquiv adj adj').symm beta.hom).natTrans)
  refine ⟨e, rfl, ?_⟩
  refine ⟨(Functor.mapDerivedCategoryCompIso F G).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso H I, ?_⟩
  exact exact_square_normalization F G H I e

/-- The canonical open-extension inverse mate is invertible, and its termwise derived
comparison is invertible with the specified localization normalization. The inverse of
`e` is the comparison in the opposite direction in the node.
Source: def-tw-frobenius-action, compact-support transport; agent ringed-site argument
(blueprint: lem-sf-condensed-isomorphism-square-exchange).

Proof:
1. Step 1 of condensed_isomorphism_square_exchange gives equivalences u* and v*.
   Both open extensions are exact and have the specified adjunctions to pullback.
2. Invert upperStarSquareComparison to obtain beta : j* u* ≅ v* j'*.
   Apply lem-stage3-inverse-mate-equivalences to these adjunctions and equivalences.
   The inverse mate is therefore invertible; take e to be this actual transformation
   equipped with its inverse, not an arbitrary isomorphism of endpoint functors.
3. The composites u* followed by j'! and j! followed by v* are exact and additive.
   Let eD be the inverse exact derived composition comparison for (u*, j'!), then the
   derived natural isomorphism of e (lem-sfb-exact-derived-natural-iso), then the exact
   derived composition comparison for (j!, v*) (lem-sfb-exact-derived-composition).
4. For the equation on a complex K, precompose with the source composition comparison
   and postcompose with the localized termwise composition comparison of the target;
   both are isomorphisms, so this is reversible. The factorization formulas of these
   comparisons and of the derived natural isomorphism
   (lem-weil-pbc-exact-functor-derived-factorization) reduce both sides to the same map
   up to the image of an isomorphism followed by its inverse, which cancels. -/
theorem condensed_isomorphism_square_open_exchange
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y X' Y' : Scheme.{u}} {j : X ⟶ Y} {j' : X' ⟶ Y'}
    [IsOpenImmersion j] [IsOpenImmersion j']
    {u : X' ⟶ X} {v : Y' ⟶ Y} [IsIso u] [IsIso v]
    (sq : CommSq u j' j v) :
    ∃ e : upperStar Λ.X u ⋙ openImmersionLowerShriek Λ.X j' ≅
        openImmersionLowerShriek Λ.X j ⋙ upperStar Λ.X v,
      e.hom = ((mateEquiv
        (openImmersionLowerShriekUpperStarAdjunction Λ.X j)
        (openImmersionLowerShriekUpperStarAdjunction Λ.X j')).symm
          (TwoSquare.mk _ _ _ _ (upperStarSquareComparison Λ.X sq).inv)).natTrans ∧
      ∃ eD : (upperStar Λ.X u).mapDerivedCategory ⋙
            (openImmersionLowerShriek Λ.X j').mapDerivedCategory ≅
          (openImmersionLowerShriek Λ.X j).mapDerivedCategory ⋙
            (upperStar Λ.X v).mapDerivedCategory,
        ∀ K : CochainComplex
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj Λ.X X)) ℤ,
          eD.hom.app (DerivedCategory.Q.obj K) ≫
              (upperStar Λ.X v).mapDerivedCategory.map
                ((openImmersionLowerShriek Λ.X j).mapDerivedCategoryFactors.hom.app K) ≫
              (upperStar Λ.X v).mapDerivedCategoryFactors.hom.app
                (((openImmersionLowerShriek Λ.X j).mapHomologicalComplex (.up ℤ)).obj K) =
            (openImmersionLowerShriek Λ.X j').mapDerivedCategory.map
                ((upperStar Λ.X u).mapDerivedCategoryFactors.hom.app K) ≫
              (openImmersionLowerShriek Λ.X j').mapDerivedCategoryFactors.hom.app
                (((upperStar Λ.X u).mapHomologicalComplex (.up ℤ)).obj K) ≫
              DerivedCategory.Q.map
                ((Functor.mapHomologicalComplexCompIso
                    (Iso.refl (upperStar Λ.X u ⋙ openImmersionLowerShriek Λ.X j'))
                    (.up ℤ)).hom.app K ≫
                  (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K ≫
                  (Functor.mapHomologicalComplexCompIso
                    (Iso.refl (openImmersionLowerShriek Λ.X j ⋙ upperStar Λ.X v))
                    (.up ℤ)).inv.app K) := by
  exact exact_inverse_mate_exchange (upperStar Λ.X u)
    (openImmersionLowerShriek Λ.X j') (openImmersionLowerShriek Λ.X j)
    (upperStar Λ.X v) (upperStar Λ.X j) (upperStar Λ.X j')
    (openImmersionLowerShriekUpperStarAdjunction Λ.X j)
    (openImmersionLowerShriekUpperStarAdjunction Λ.X j')
    (upperStarSquareComparison Λ.X sq).symm

end AlgebraicGeometry.ProEtale.CondensedRing
