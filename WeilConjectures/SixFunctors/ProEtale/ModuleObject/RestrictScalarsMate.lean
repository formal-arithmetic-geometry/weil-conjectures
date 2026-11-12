/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionOpenLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionPullUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SquareComparisonCoherence

/-!

# Restriction of scalars and the derived pushforward, as mates

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, not necessarily flat, and
`f : X ⟶ Y` a morphism of schemes. Write `Res = D(Res_a)` for the levelwise restriction of
scalars, `τ_f : Res ⋙ Lf^*_Λ ≅ Lf^*_{Λ'} ⋙ Res` for its commutation with the derived
pullbacks (`ProEtale.CondensedRing.derivedComapLeftDerivedUpperStarIso`) and
`ρ_f : Rf_*^{Λ'} ⋙ Res ≅ Res ⋙ Rf_*^Λ` for its commutation with the derived pushforwards
(`ProEtale.CondensedRing.rightDerivedLowerStarComapIso`), the conjugate of (Pull) along the
composite adjunctions. This file shows:

* `τ_f` is the mate of (Pull) along the adjunctions `L(Ext) ⊣ Res`
  (`ProEtale.CondensedRing.mateEquiv_derivedUpperStarExtendScalarsIso_hom`);
* hence `ρ_f` is the mate of `τ_f` along the adjunctions `Lf^* ⊣ Rf_*`
  (`ProEtale.CondensedRing.rightDerivedLowerStarComapIso_hom_eq_mateEquiv`), by the iterated mate
  law `CategoryTheory.iterated_mateEquiv_conjugateEquiv`;
* the commutations `τ` satisfy the cube condition of `CategoryTheory.mateEquiv_app_cube` for the
  pullback square comparisons of a commutative square of schemes
  (`ProEtale.CondensedRing.derivedComapLeftDerivedUpperStarIso_cube`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) {G : A ⥤ C} {H : B ⥤ D} {R' : D ⥤ C}

/-- A natural transformation `β : R ⋙ G ⟶ H ⋙ R'` out of a composite with a right adjoint `R` is
determined by its components at the objects `L (R N)`: `β_N = G(η_{R N}) ≫ β_{L R N} ≫ R'(H ε_N)`,
by naturality and the triangle identity. -/
lemma app_eq_map_unit_comp_app_comp_map_counit (β : R ⋙ G ⟶ H ⋙ R') (N : B) :
    β.app N = G.map (adj.unit.app (R.obj N)) ≫ β.app (L.obj (R.obj N)) ≫
      R'.map (H.map (adj.counit.app N)) := by
  have h := β.naturality (adj.counit.app N)
  dsimp only [Functor.comp_obj, Functor.comp_map] at h
  rw [← h, ← G.map_comp_assoc, adj.right_triangle_components]
  simp

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

section Mate

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option maxHeartbeats 1000000 in
-- composites of derived functors on module objects are slow to unify
/-- The commutation `τ_f : Res ⋙ Lf^*_Λ ≅ Lf^*_{Λ'} ⋙ Res` of the restriction of scalars with the
derived pullbacks is the mate of (Pull) `Lf^* ⋙ L(Ext) ≅ L(Ext) ⋙ Lf^*` along the adjunctions
`L(Ext) ⊣ Res`. -/
lemma mateEquiv_derivedUpperStarExtendScalarsIso_hom :
    mateEquiv (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
        (derivedUpperStarExtendScalarsIso a f).hom =
      (derivedComapLeftDerivedUpperStarIso a f).hom := by
  ext N
  have h := upperStar_map_unit_comp_derivedComapLeftDerivedUpperStarIso_hom_app a f
    (D(Mod.comap (coefficientMap a Y)).obj N)
  have hm := unit_mateEquiv (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (derivedUpperStarExtendScalarsIso a f).hom (D(Mod.comap (coefficientMap a Y)).obj N)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at h hm
  rw [Adjunction.app_eq_map_unit_comp_app_comp_map_counit
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)),
    Adjunction.app_eq_map_unit_comp_app_comp_map_counit
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
      (derivedComapLeftDerivedUpperStarIso a f).hom]
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% hm, reassoc_of% h]

/-- **Restriction of scalars commutes with the derived pushforward, as a mate**: the commutation
`ρ_f : Rf_*^{Λ'} ⋙ Res ≅ Res ⋙ Rf_*^Λ` (`rightDerivedLowerStarComapIso`) is the mate of the
commutation `τ_f : Res ⋙ Lf^*_Λ ≅ Lf^*_{Λ'} ⋙ Res` along the adjunctions `Lf^* ⊣ Rf_*`. -/
lemma rightDerivedLowerStarComapIso_hom_eq_mateEquiv :
    (rightDerivedLowerStarComapIso a f).hom =
      (mateEquiv (derivedUpperStarLowerStarAdjunction Λ' f)
        (derivedUpperStarLowerStarAdjunction Λ f)
        (derivedComapLeftDerivedUpperStarIso a f).hom).natTrans := by
  rw [← mateEquiv_derivedUpperStarExtendScalarsIso_hom, iterated_mateEquiv_conjugateEquiv]
  rfl

/-- The mate of `τ_f` along the adjunctions `Lf^* ⊣ Rf_*` is an isomorphism. -/
instance isIso_mateEquiv_derivedComapLeftDerivedUpperStarIso_hom :
    IsIso (mateEquiv (derivedUpperStarLowerStarAdjunction Λ' f)
      (derivedUpperStarLowerStarAdjunction Λ f)
      (derivedComapLeftDerivedUpperStarIso a f).hom).natTrans := by
  rw [← rightDerivedLowerStarComapIso_hom_eq_mateEquiv]
  infer_instance

end Mate

/-- The commutations `τ` of the restriction of scalars with the derived pullbacks commute with
the `eqToHom`s induced by an equality `u = v` of morphisms of schemes. -/
lemma derivedComapLeftDerivedUpperStarIso_hom_app_eqToHom {X Y : Scheme.{u}} {u v : X ⟶ Y}
    (e : u = v)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y))) :
    (derivedComapLeftDerivedUpperStarIso a u).hom.app M ≫
        D(Mod.comap (coefficientMap a X)).map
          (eqToHom (by rw [e] : L((u)^*⟦Λ'⟧).obj M = L((v)^*⟦Λ'⟧).obj M)) =
      eqToHom (by rw [e] : L((u)^*⟦Λ⟧).obj (D(Mod.comap (coefficientMap a Y)).obj M) =
          L((v)^*⟦Λ⟧).obj (D(Mod.comap (coefficientMap a Y)).obj M)) ≫
        (derivedComapLeftDerivedUpperStarIso a v).hom.app M := by
  subst e
  simp

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

set_option maxHeartbeats 1000000 in
-- unifying objects of the derived categories given by composites of derived pullbacks is slow
/-- The cube condition of `CategoryTheory.mateEquiv_app_cube` for the derived pullbacks with
coefficients `Λ'` and `Λ` along a commutative square, their pullback square comparisons and the
commutations `τ` of the restriction of scalars with the derived pullbacks: both composites
`Lf'^* Lg^* (Res M) ⟶ Res (Lg'^* Lf^* M)` agree. -/
lemma derivedComapLeftDerivedUpperStarIso_cube (sq : CommSq g' f' f g)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y))) :
    L((f')^*⟦Λ⟧).map ((derivedComapLeftDerivedUpperStarIso a g).hom.app M) ≫
        (derivedComapLeftDerivedUpperStarIso a f').hom.app (L((g)^*⟦Λ'⟧).obj M) ≫
        D(Mod.comap (coefficientMap a X')).map ((pullbackSquareComparison Λ' sq).hom.app M) =
      (pullbackSquareComparison Λ sq).hom.app (D(Mod.comap (coefficientMap a Y)).obj M) ≫
        L((g')^*⟦Λ⟧).map ((derivedComapLeftDerivedUpperStarIso a f).hom.app M) ≫
        (derivedComapLeftDerivedUpperStarIso a g').hom.app (L((f)^*⟦Λ'⟧).obj M) := by
  have H₁ := derivedComapLeftDerivedUpperStarIso_comp_hom_app a f' g M
  have H₂ := derivedComapLeftDerivedUpperStarIso_comp_hom_app a g' f M
  have H₃ := derivedComapLeftDerivedUpperStarIso_hom_app_eqToHom a sq.w.symm M
  rw [← cancel_epi ((leftDerivedUpperStarComp Λ f' g).hom.app
    (D(Mod.comap (coefficientMap a Y)).obj M))]
  simp only [pullbackSquareComparison_hom_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% H₁, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% H₃, ← H₂, Iso.hom_inv_id_app_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
