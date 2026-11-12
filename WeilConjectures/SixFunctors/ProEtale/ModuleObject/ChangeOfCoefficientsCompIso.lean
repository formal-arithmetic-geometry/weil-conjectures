/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateVCompOfIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullCube
public import WeilConjectures.WeilSheaf.SmoothPurityCoefficientPullComp

/-!
# The direct image comparison for a composite coefficient change

Let `a : Λ ⟶ Λ'` and `b : Λ' ⟶ Λ''` be morphisms of commutative condensed rings, not necessarily
flat, with composite `c = a ≫ b`, and let `f : X ⟶ Y` be a morphism of schemes. The comparison
`Rf_* ⋙ T ⟶ T ⋙ Rf_*` between derived pushforward and derived extension of scalars
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom`) for `c` is the composite of the
comparisons for `a` and `b`, up to the transitivity isomorphisms `T_c ≅ T_a ⋙ T_b`
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom_app_of_coefficient_comp`). This
follows from the corresponding compatibility of the pullback isomorphisms
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso_hom_app_of_coefficient_comp`) by mate
calculus.

Consequently the comparison for `c` is invertible at `K` as soon as the comparison for `a` is
invertible at `K` and the comparison for `b` is invertible at `T_a K`
(`ProEtale.CondensedRing.isIso_derivedUpperStarExtendScalarsPushHom_app_of_coefficient_comp`),
and similarly for the flat comparison `ProEtale.CondensedRing.derivedPushHom`
(`ProEtale.CondensedRing.isIso_derivedPushHom_app_of_comp`). This is blueprint
`lemma-change-coefficients-direct-image--6`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [MonObj Λ''] [IsCommMonObj Λ'']
  (a : Λ ⟶ Λ') [IsMonHom a] (b : Λ' ⟶ Λ'') [IsMonHom b]
  (c : Λ ⟶ Λ'') [IsMonHom c] {X Y : Scheme.{u}} (f : X ⟶ Y)

omit [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ'] [MonObj Λ''] [IsCommMonObj Λ'']
  [IsMonHom a] [IsMonHom b] [IsMonHom c] in
private lemma inv_eq_of_hom_eq_comp {C : Type*} [Category* C] {O₁ O₂ O₃ O₄ O₅ : C}
    (e : O₁ ≅ O₅) (e₁ : O₁ ≅ O₂) (e₂ : O₂ ≅ O₃) (e₃ : O₃ ≅ O₄) (e₄ : O₄ ≅ O₅)
    (h : e.hom = e₁.hom ≫ e₂.hom ≫ e₃.hom ≫ e₄.hom) :
    e.inv = e₄.inv ≫ e₃.inv ≫ e₂.inv ≫ e₁.inv := by
  rw [← cancel_epi e.hom, e.hom_inv_id, h]
  simp

/-- The inverse of the pullback isomorphism for a composite coefficient change `c = a ≫ b` is the
composite of the inverses of those for `a` and `b`. -/
lemma derivedUpperStarExtendScalarsIso_inv_app_of_coefficient_comp (hc : a ≫ b = c)
    (K : DerivedCategory
      (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (derivedUpperStarExtendScalarsIso c f).inv.app K =
      L((f)^*⟦Λ''⟧).map ((Mod.derivedExtendScalarsCompIso
        (coefficientMap a Y) (coefficientMap b Y) (coefficientMap c Y)
        (coefficientMap_comp_eq a b c hc Y)).hom.app K) ≫
      (derivedUpperStarExtendScalarsIso b f).inv.app
        (L(Mod.extendScalars (coefficientMap a Y)).obj K) ≫
      L(Mod.extendScalars (coefficientMap b X)).map
        ((derivedUpperStarExtendScalarsIso a f).inv.app K) ≫
      (Mod.derivedExtendScalarsCompIso (coefficientMap a X) (coefficientMap b X)
        (coefficientMap c X) (coefficientMap_comp_eq a b c hc X)).inv.app
        (L((f)^*⟦Λ⟧).obj K) :=
  inv_eq_of_hom_eq_comp ((derivedUpperStarExtendScalarsIso c f).app K)
    ((Mod.derivedExtendScalarsCompIso (coefficientMap a X) (coefficientMap b X)
      (coefficientMap c X) (coefficientMap_comp_eq a b c hc X)).app (L((f)^*⟦Λ⟧).obj K))
    (L(Mod.extendScalars (coefficientMap b X)).mapIso
      ((derivedUpperStarExtendScalarsIso a f).app K))
    ((derivedUpperStarExtendScalarsIso b f).app (L(Mod.extendScalars (coefficientMap a Y)).obj K))
    (L((f)^*⟦Λ''⟧).mapIso ((Mod.derivedExtendScalarsCompIso
        (coefficientMap a Y) (coefficientMap b Y) (coefficientMap c Y)
        (coefficientMap_comp_eq a b c hc Y)).app K).symm)
    (derivedUpperStarExtendScalarsIso_hom_app_of_coefficient_comp a b c f hc K)

/-- **The direct image comparison is compatible with the composition of coefficient changes.**
For `c = a ≫ b` (no flatness assumed), the comparison `Rf_* ⋙ T_c ⟶ T_c ⋙ Rf_*` at `K` is the
composite of the comparison for `a` at `K` and the comparison for `b` at `T_a K`, up to the
transitivity isomorphisms `T_c ≅ T_a ⋙ T_b` (`Mod.derivedExtendScalarsCompIso`) on `Y` and on
`X`. -/
theorem derivedUpperStarExtendScalarsPushHom_app_of_coefficient_comp (hc : a ≫ b = c)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (derivedUpperStarExtendScalarsPushHom c f).app K =
      (Mod.derivedExtendScalarsCompIso (coefficientMap a Y) (coefficientMap b Y)
          (coefficientMap c Y) (coefficientMap_comp_eq a b c hc Y)).hom.app
          (R((f)_*⟦Λ⟧).obj K) ≫
        L(Mod.extendScalars (coefficientMap b Y)).map
          ((derivedUpperStarExtendScalarsPushHom a f).app K) ≫
        (derivedUpperStarExtendScalarsPushHom b f).app
          (L(Mod.extendScalars (coefficientMap a X)).obj K) ≫
        R((f)_*⟦Λ''⟧).map ((Mod.derivedExtendScalarsCompIso (coefficientMap a X)
          (coefficientMap b X) (coefficientMap c X)
          (coefficientMap_comp_eq a b c hc X)).inv.app K) :=
  mateEquiv_app_eq_comp_of_vComp_iso (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ' f) (derivedUpperStarLowerStarAdjunction Λ'' f)
    (Mod.derivedExtendScalarsCompIso _ _ _ (coefficientMap_comp_eq a b c hc Y))
    (Mod.derivedExtendScalarsCompIso _ _ _ (coefficientMap_comp_eq a b c hc X))
    (derivedUpperStarExtendScalarsIso a f).inv (derivedUpperStarExtendScalarsIso b f).inv
    (derivedUpperStarExtendScalarsIso c f).inv
    (derivedUpperStarExtendScalarsIso_inv_app_of_coefficient_comp a b c f hc) K

/-- Blueprint `lemma-change-coefficients-direct-image--6` (**composite coefficient maps**): for a
composite `c = a ≫ b` of coefficient changes (no flatness assumed), the comparison
`(Rf_* K)_{Λ''} ⟶ Rf_*(K_{Λ''})` is an isomorphism as soon as the comparison
`(Rf_* K)_{Λ'} ⟶ Rf_*(K_{Λ'})` for `a` at `K` and the comparison for `b` at `K_{Λ'}` are
isomorphisms. By induction this covers finite composites. -/
theorem isIso_derivedUpperStarExtendScalarsPushHom_app_of_coefficient_comp (hc : a ≫ b = c)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    [IsIso ((derivedUpperStarExtendScalarsPushHom a f).app K)]
    [IsIso ((derivedUpperStarExtendScalarsPushHom b f).app
      (L(Mod.extendScalars (coefficientMap a X)).obj K))] :
    IsIso ((derivedUpperStarExtendScalarsPushHom c f).app K) := by
  rw [derivedUpperStarExtendScalarsPushHom_app_of_coefficient_comp a b c f hc]
  infer_instance

section Flat

variable [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap b X))]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap c X))]

/-- Blueprint `lemma-change-coefficients-direct-image--6` for flat coefficient changes: for a
composite `c = a ≫ b`, the comparison `ProEtale.CondensedRing.derivedPushHom c f` is invertible
at `K` as soon as the comparison for `a` is invertible at `K` and the comparison for `b` is
invertible at `T_a K`. -/
theorem isIso_derivedPushHom_app_of_comp (hc : a ≫ b = c)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    [IsIso ((derivedPushHom a f).app K)]
    [IsIso ((derivedPushHom b f).app (L(Mod.extendScalars (coefficientMap a X)).obj K))] :
    IsIso ((derivedPushHom c f).app K) := by
  rw [derivedPushHom_comp_app a b c f hc]
  infer_instance

end Flat

end AlgebraicGeometry.ProEtale.CondensedRing
