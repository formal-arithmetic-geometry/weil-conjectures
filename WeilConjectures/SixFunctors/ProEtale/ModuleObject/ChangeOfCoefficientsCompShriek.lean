/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ComapUpperStarIsoMate
public import WeilConjectures.CategoryTheory.Adjunction.ConjugateIsoComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsComp

/-!
# Compatibility of the (Shriek) comparison with the composition of coefficient changes

Let `a : Λ ⟶ Λ'` and `b : Λ' ⟶ Λ''` be morphisms of commutative condensed rings, with composite
`c = a ≫ b`, along which the coefficient changes are flat. This file proves that the (Shriek)
comparisons `Rf_! ⋙ T^Y ⟶ T^X ⋙ Rf_!` (`ProEtale.CondensedRing.derivedLowerShriekHom`) compose:
the comparison for `c` is the composite of the comparisons for `a` and `b`, up to the
transitivity isomorphisms `T_c ≅ T_a ⋙ T_b` of the derived extensions of scalars
(`ProEtale.CondensedRing.derivedLowerShriekHom_comp_app`).

Following the blueprint, `Rf_! = Rg_* ∘ Dj_!` for the chosen compactification and the
comparison is the composite of the (Push) comparison for `g`, which is transitive by
`ProEtale.CondensedRing.derivedPushHom_comp_app`, and of the (Shriek) isomorphism for the open
immersion `j`, which is transitive because it is the conjugate of the isomorphisms
`Dj^* ⋙ D(Res) ≅ D(Res) ⋙ Dj^*`, which compose:

* the underived isomorphisms `f^* ⋙ Res ≅ Res ⋙ f^*` compose
  (`ProEtale.CondensedRing.comapUpperStarIso_hom_app_of_comp_eq`), since their mates are the
  isomorphisms `f_* ⋙ Res ≅ Res ⋙ f_*` (`ProEtale.CondensedRing.comapUpperStarIso_mate`), which
  compose (`ProEtale.CondensedRing.comapLowerStarIso_hom_app_of_comp_eq`);
* hence so do the derived ones (`ProEtale.CondensedRing.derivedComapUpperStarIso_hom_app_comp`),
  and so do their conjugates
  (`ProEtale.CondensedRing.derivedOpenImmersionShriekIso_hom_app_comp`), by
  `Adjunction.conjugateIsoEquiv_symm_hom_app_eq_comp`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Abelian

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] [MonObj Λ''] [IsCommMonObj Λ'']
  (a : Λ ⟶ Λ') [IsMonHom a] (b : Λ' ⟶ Λ'') [IsMonHom b] (c : Λ ⟶ Λ'') [IsMonHom c]

section UpperStar

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The isomorphisms `f^* ⋙ Res ≅ Res ⋙ f^*` compose: the one for `c = a ≫ b` is the composite of
those for `a` and `b`, up to the composition isomorphisms of the restrictions of scalars. -/
lemma comapUpperStarIso_hom_app_of_comp_eq (hc : a ≫ b = c)
    (N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ'' Y)) :
    (comapUpperStarIso c f).hom.app N ≫
        (f)^*⟦Λ⟧.map ((comapCoefficientMapCompIso a b c hc Y).inv.app N) =
      (comapCoefficientMapCompIso a b c hc X).inv.app ((f)^*⟦Λ''⟧.obj N) ≫
        (Mod.comap (coefficientMap a X)).map ((comapUpperStarIso b f).hom.app N) ≫
        (comapUpperStarIso a f).hom.app ((Mod.comap (coefficientMap b Y)).obj N) := by
  have hm := compCoherence_of_mateEquiv_app_comp (upperStarLowerStarAdjunction Λ'' f)
    (upperStarLowerStarAdjunction Λ' f) (upperStarLowerStarAdjunction Λ f)
    (comapCoefficientMapCompIso a b c hc Y).symm (comapCoefficientMapCompIso a b c hc X).symm
    (TwoSquare.mk _ _ _ _ (comapUpperStarIso b f).inv)
    (TwoSquare.mk _ _ _ _ (comapUpperStarIso a f).inv)
    (TwoSquare.mk _ _ _ _ (comapUpperStarIso c f).inv) (fun K => by
      rw [comapUpperStarIso_mate, comapUpperStarIso_mate, comapUpperStarIso_mate]
      dsimp only [TwoSquare.natTrans, TwoSquare.mk]
      rw [comapLowerStarIso_hom_app_of_comp_eq a b c f hc K]
      simp only [Iso.symm_hom, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id]
      dsimp only [Functor.comp_obj]
      simp only [Category.comp_id]) N
  dsimp only [TwoSquare.natTrans, TwoSquare.mk, Iso.symm_hom] at hm
  rw [← cancel_epi ((comapUpperStarIso c f).inv.app N), Iso.inv_hom_id_app_assoc,
    reassoc_of% hm]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

/-- The isomorphisms `Df^* ⋙ D(Res) ≅ D(Res) ⋙ Df^*` compose: the one for `c = a ≫ b` is the
composite of those for `a` and `b`, up to the composition isomorphisms
`Mod.mapDerivedCategoryComapCompIso` of the restrictions of scalars. -/
theorem derivedComapUpperStarIso_hom_app_comp (hc : a ≫ b = c)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ'' Y))) :
    (derivedComapUpperStarIso c f).hom.app K =
      (Mod.mapDerivedCategoryComapCompIso (coefficientMap a X) (coefficientMap b X)
          (coefficientMap c X) (coefficientMap_comp_eq a b c hc X)).inv.app
          (D((f)^*⟦Λ''⟧).obj K) ≫
        D(Mod.comap (coefficientMap a X)).map ((derivedComapUpperStarIso b f).hom.app K) ≫
        (derivedComapUpperStarIso a f).hom.app (D(Mod.comap (coefficientMap b Y)).obj K) ≫
        D((f)^*⟦Λ⟧).map ((Mod.mapDerivedCategoryComapCompIso (coefficientMap a Y)
          (coefficientMap b Y) (coefficientMap c Y)
          (coefficientMap_comp_eq a b c hc Y)).hom.app K) := by
  have H := Functor.mapDerivedCategorySquareIso_hom_app_comp (comapUpperStarIso b f)
    (comapUpperStarIso a f) (comapUpperStarIso c f) (comapCoefficientMapCompIso a b c hc X).symm
    (comapCoefficientMapCompIso a b c hc Y).symm
    (comapUpperStarIso_hom_app_of_comp_eq a b c f hc) K
  have hT : ∀ (Z : Scheme.{u}), (Functor.mapDerivedCategoryTriangleIso
      (comapCoefficientMapCompIso a b c hc Z).symm).hom =
      (Mod.mapDerivedCategoryComapCompIso (coefficientMap a Z) (coefficientMap b Z)
        (coefficientMap c Z) (coefficientMap_comp_eq a b c hc Z)).inv := by
    intro Z
    simp only [Functor.mapDerivedCategoryTriangleIso, Mod.mapDerivedCategoryComapCompIso,
      Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapDerivedCategoryNatIso_symm]
  rw [hT, hT] at H
  rw [← cancel_mono (D((f)^*⟦Λ⟧).map ((Mod.mapDerivedCategoryComapCompIso (coefficientMap a Y)
    (coefficientMap b Y) (coefficientMap c Y) (coefficientMap_comp_eq a b c hc Y)).inv.app K))]
  refine H.trans ?_
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]
  dsimp only [Functor.comp_obj]
  simp only [Category.comp_id]
  rfl

end UpperStar

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The (Shriek) isomorphisms `Dj_! ⋙ T ≅ T ⋙ Dj_!` for an open immersion `j` compose: the one
for `c = a ≫ b` is the composite of those for `a` and `b`, up to the transitivity isomorphisms
`T_c ≅ T_a ⋙ T_b` of the derived extensions of scalars (`Mod.derivedExtendScalarsCompIso`). -/
theorem derivedOpenImmersionShriekIso_hom_app_comp (hc : a ≫ b = c)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))) :
    (derivedOpenImmersionShriekIso c j).hom.app K =
      (Mod.derivedExtendScalarsCompIso (coefficientMap a X) (coefficientMap b X)
          (coefficientMap c X) (coefficientMap_comp_eq a b c hc X)).hom.app
          (D((j)_!open⟦Λ⟧).obj K) ≫
        L(Mod.extendScalars (coefficientMap b X)).map
          ((derivedOpenImmersionShriekIso a j).hom.app K) ≫
        (derivedOpenImmersionShriekIso b j).hom.app
          (L(Mod.extendScalars (coefficientMap a U)).obj K) ≫
        D((j)_!open⟦Λ''⟧).map ((Mod.derivedExtendScalarsCompIso (coefficientMap a U)
          (coefficientMap b U) (coefficientMap c U)
          (coefficientMap_comp_eq a b c hc U)).inv.app K) :=
  Adjunction.conjugateIsoEquiv_symm_hom_app_eq_comp
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap c X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b U))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap c U))
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'' j)
    (derivedComapUpperStarIso a j) (derivedComapUpperStarIso b j) (derivedComapUpperStarIso c j)
    (Mod.mapDerivedCategoryComapCompIso _ _ _ (coefficientMap_comp_eq a b c hc X))
    (Mod.mapDerivedCategoryComapCompIso _ _ _ (coefficientMap_comp_eq a b c hc U))
    (derivedComapUpperStarIso_hom_app_comp a b c j hc) K

end OpenImmersion

section LowerShriek

variable [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap b X))]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap c X))]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

omit [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap b X))]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap c X))] in
/-- The components of the (Shriek) comparison: the (Push) comparison for the proper part `g` of
the chosen compactification, followed by `Rg_*` of the (Shriek) isomorphism for its open part. -/
lemma derivedLowerShriekHom_app
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (derivedLowerShriekHom a f).app K =
      (derivedPushHom a (HasCompactification.compactification f).g).app
          (D(((HasCompactification.compactification f).i)_!open⟦Λ⟧).obj K) ≫
        R(((HasCompactification.compactification f).g)_*⟦Λ'⟧).map
          ((derivedOpenImmersionShriekIso a (HasCompactification.compactification f).i).hom.app
            K) := by
  simp only [derivedLowerShriekHom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]

/-- Blueprint `proposition-six-operations-change-coefficients--10`: **(Shriek) is compatible
with the composition of coefficient changes.** For `c = a ≫ b`, the comparison
`Rf_! ⋙ T_c ⟶ T_c ⋙ Rf_!` is the composite of the comparisons for `a` and `b`, up to the
transitivity isomorphisms `T_c ≅ T_a ⋙ T_b` of the derived extensions of scalars
(`Mod.derivedExtendScalarsCompIso`) on `Y` and on `X`. -/
theorem derivedLowerShriekHom_comp_app (hc : a ≫ b = c)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (derivedLowerShriekHom c f).app K =
      (Mod.derivedExtendScalarsCompIso (coefficientMap a Y) (coefficientMap b Y)
          (coefficientMap c Y) (coefficientMap_comp_eq a b c hc Y)).hom.app
          (R(f)_!⟦Λ⟧.obj K) ≫
        L(Mod.extendScalars (coefficientMap b Y)).map ((derivedLowerShriekHom a f).app K) ≫
        (derivedLowerShriekHom b f).app (L(Mod.extendScalars (coefficientMap a X)).obj K) ≫
        R(f)_!⟦Λ''⟧.map ((Mod.derivedExtendScalarsCompIso (coefficientMap a X)
          (coefficientMap b X) (coefficientMap c X)
          (coefficientMap_comp_eq a b c hc X)).inv.app K) := by
  simp only [derivedLowerShriekHom_app]
  simp only [derivedPushHom_comp_app a b c (HasCompactification.compactification f).g hc,
    derivedOpenImmersionShriekIso_hom_app_comp a b c (HasCompactification.compactification f).i hc]
  have hn := (derivedPushHom b (HasCompactification.compactification f).g).naturality
    ((derivedOpenImmersionShriekIso a (HasCompactification.compactification f).i).hom.app K)
  simp only [Functor.comp_map] at hn
  have hθ : R(((HasCompactification.compactification f).g)_*⟦Λ''⟧).map
        ((Mod.derivedExtendScalarsCompIso (coefficientMap a _) (coefficientMap b _)
          (coefficientMap c _) (coefficientMap_comp_eq a b c hc
            (HasCompactification.compactification f).Z)).inv.app
          (D(((HasCompactification.compactification f).i)_!open⟦Λ⟧).obj K)) ≫
      R(((HasCompactification.compactification f).g)_*⟦Λ''⟧).map
        ((Mod.derivedExtendScalarsCompIso (coefficientMap a _) (coefficientMap b _)
          (coefficientMap c _) (coefficientMap_comp_eq a b c hc
            (HasCompactification.compactification f).Z)).hom.app
          (D(((HasCompactification.compactification f).i)_!open⟦Λ⟧).obj K)) = 𝟙 _ := by
    simp [← Functor.map_comp]
  simp only [Functor.map_comp, Category.assoc, reassoc_of% hθ,
    reassoc_of% hn]
  rfl

end LowerShriek

end AlgebraicGeometry.ProEtale.CondensedRing
