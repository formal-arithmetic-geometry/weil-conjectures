/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.ReductionTateTwistOne
public import WeilConjectures.TateTwist.EtaleTateSheafPowOne

/-!
# The change of coefficients of `Λ_X(1)` on the tensor powers of the Tate sheaf

Let `ρ : Λ →+* Λ'` be a morphism of finite coefficient rings with characteristics `n = n' e`.
Through the identifications `Λ_X(1) ≅ (tateSheafPow Λ X 1)[0]`
(`AlgebraicGeometry.Etale.tateObjectNatIsoSingleFunctor`), the change of coefficients
`Λ_X(1) ⟶ Res Λ'_X(1)` of the Tate twists (`AlgebraicGeometry.Etale.tateTwistObjectOneChangeMap`)
is induced by a morphism of sheaves `tateSheafPow Λ X 1 ⟶ Res (tateSheafPow Λ' X 1)`
(`AlgebraicGeometry.Etale.tateSheafPowOneChangeMap`): the unit of the extension of scalars along
`ρ` followed by `Λ' ⊗_Λ (μ_n ⊗ Λ) ≅ μ_{n'} ⊗ Λ'`.
-/

@[expose] public section

universe u

open CategoryTheory

/-- A categorical rearrangement: if `c = (i.hom ≫ S u ≫ θ_N) ≫ G (S' r ≫ o'⁻¹)` and
`t = i ≪≫ S n`, `t'.hom = o'.hom ≫ S' (s⁻¹ ≫ n')`, then
`t⁻¹ ≫ c = S (n⁻¹ ≫ u ≫ R (r ≫ s⁻¹ ≫ n')) ≫ θ ≫ G t'⁻¹`. -/
lemma CategoryTheory.inv_comp_eq_map_comp_app_comp_map {C C' D D' : Type*} [Category* C]
    [Category* C'] [Category* D] [Category* D'] (S : C ⥤ D) (S' : C' ⥤ D') (R : C' ⥤ C)
    (G : D' ⥤ D) (θ : R ⋙ S ⟶ S' ⋙ G) {T : D} {T' : D'} {A P : C} {N M A' P' : C'}
    (t : T ≅ S.obj P) (i : T ≅ S.obj A) (n : A ≅ P) (u : A ⟶ R.obj N) (r : N ⟶ M) [IsIso r]
    (o' : T' ≅ S'.obj M) (s : A' ≅ M) (n' : A' ≅ P') (t' : T' ≅ S'.obj P') (c : T ⟶ G.obj T')
    (k : P ⟶ R.obj P') (ht : t = i ≪≫ S.mapIso n) (ht' : t'.hom = o'.hom ≫ S'.map (s.inv ≫ n'.hom))
    (hc : c = (i.hom ≫ S.map u ≫ θ.app N) ≫ G.map ((S'.mapIso (asIso r) ≪≫ o'.symm).hom))
    (hk : k = n.inv ≫ u ≫ R.map (r ≫ s.inv ≫ n'.hom)) :
    t.inv ≫ c = S.map k ≫ θ.app P' ≫ G.map t'.inv := by
  subst ht hc hk
  have ht'' : t'.inv = S'.map (n'.inv ≫ s.hom) ≫ o'.inv := by
    rw [← cancel_epi t'.hom, Iso.hom_inv_id, ht', Category.assoc, ← S'.map_comp_assoc]
    simp
  have hθ := θ.naturality (r ≫ s.inv ≫ n'.hom)
  simp only [Functor.comp_map] at hθ
  rw [ht'', S.map_comp, S.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hθ]
  simp

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (X : Scheme.{u})
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] [NeZero (ringChar Λ)]
  [NeZero (ringChar Λ')] (e : ℕ) (he : ringChar Λ = ringChar Λ' * e)

/-- The change of coefficients `tateSheafPow Λ X 1 ⟶ Res (tateSheafPow Λ' X 1)` of the Tate
sheaves: the unit of the extension of scalars along `ρ`, followed by
`Λ' ⊗_Λ (μ_n ⊗ Λ) ≅ μ_{n'} ⊗ Λ'` (`tateTwistSheafOneReductionMap`, the `e`-th power map). -/
noncomputable def tateSheafPowOneChangeMap :
    tateSheafPow Λ X 1 ⟶ (Sheaf.restrictScalars X.smallEtaleTopology ρ).obj (tateSheafPow Λ' X 1) :=
  (tateTwistSheafNatIso Λ X 1).inv ≫
    (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).unit.app _ ≫
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).map
        (tateTwistSheafOneReductionMap X e he ≫ (tateTwistSheafOneIso X Λ').inv ≫
          (tateTwistSheafNatIso Λ' X 1).hom)

/-- **The change of coefficients of `Λ_X(1)` on the Tate sheaves**: through
`Λ_X(1) ≅ (tateSheafPow Λ X 1)[0]`, `tateTwistObjectOneChangeMap` is the morphism of sheaves
`tateSheafPowOneChangeMap` placed in degree zero. -/
lemma tateObjectNatIsoSingleFunctor_inv_comp_tateTwistObjectOneChangeMap :
    (tateObjectNatIsoSingleFunctor Λ X 1).inv ≫ tateTwistObjectOneChangeMap ρ X e he =
      (DerivedCategory.singleFunctor _ 0).map (tateSheafPowOneChangeMap ρ X e he) ≫
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
          (tateSheafPow Λ' X 1) ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          (tateObjectNatIsoSingleFunctor Λ' X 1).inv :=
  inv_comp_eq_map_comp_app_comp_map _ _ _ _
    ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv
    (tateObjectNatIsoSingleFunctor Λ X 1) (tateTwistObjectIsoSingleFunctor Λ X 1)
    (tateTwistSheafNatIso Λ X 1) _ (tateTwistSheafOneReductionMap X e he (ρ := ρ))
    (tateTwistObjectOneIso X Λ') (tateTwistSheafOneIso X Λ') (tateTwistSheafNatIso Λ' X 1)
    (tateObjectNatIsoSingleFunctor Λ' X 1) _ _ (tateObjectNatIsoSingleFunctor.eq_1 Λ X 1)
    (tateObjectNatIsoSingleFunctor_one_hom Λ' X)
    (tateTwistObjectOneChangeMap_eq_unit (ρ := ρ) X e he)
    (tateSheafPowOneChangeMap.eq_1 ρ X e he)

end AlgebraicGeometry.Etale
