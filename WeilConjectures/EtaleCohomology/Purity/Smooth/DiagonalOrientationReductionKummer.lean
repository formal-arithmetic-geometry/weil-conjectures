/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass
public import WeilConjectures.EtaleCohomology.TateTwist.ReductionTateTwistOne

/-!
# The reduction of coefficients carries Kummer classes to Kummer classes

Let `ρ : Λ →+* Λ'` be a surjective morphism of finite coefficient rings with principal kernel
whose characteristics satisfy `n = n' e` (the reduction `𝒪_E/ℓⁿ⁺² → 𝒪_E/ℓⁿ⁺¹`, `e = ℓ`), and
`Ψ = - ⊗ᴸ_Λ Λ'` the derived extension of scalars, left adjoint to the restriction of scalars
`Res`. Through the identifications `Ψ Λ_X ≅ Λ'_X` and `σ : Ψ Λ_X(1) ≅ Λ'_X(1)` adjoint to the
changes of coefficients `Λ_X ⟶ Res Λ'_X` and `Λ_X(1) ⟶ Res Λ'_X(1)` (the `e`-th power map),
`Ψ` carries the Kummer class `κ(v) : Λ_X ⟶ Λ_X(1)[1]` of a unit `v` to the Kummer class over `Λ'`
(`AlgebraicGeometry.Etale.map_kummerClass_comp_shift`, the hypothesis `hκ` of
`AlgebraicGeometry.Etale.MonoidalSupportedCoefficientChange.preservesKummerBoundaries`, blueprint
`det-sp-purity-coefficient-change`). Both sides are maps out of `Ψ Λ_X`, so they are compared
through their transposes `Λ_X ⟶ Res(Λ'_X(1)[1])`, where it is the compatibility of the Kummer
sequences on sheaves (`AlgebraicGeometry.Etale.kummerClassOf_comp_tateTwistObjectOneChangeMap`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A] [F.CommShift A] [G.CommShift A]
  [adj.CommShift A]

/-- The transpose of a morphism `F(X⟦a⟧) ≅ (F X)⟦a⟧ ⟶ Y⟦a⟧` under an adjunction commuting with
shifts is the shift of the transpose, followed by `(G Y)⟦a⟧ ≅ G(Y⟦a⟧)`. -/
lemma homEquiv_commShiftIso_hom_app_comp_shift_map (a : A) {X : C} {Y : D} (g : F.obj X ⟶ Y) :
    adj.homEquiv _ _ ((F.commShiftIso a).hom.app X ≫ g⟦a⟧') =
      (adj.homEquiv _ _ g)⟦a⟧' ≫ (G.commShiftIso a).inv.app Y := by
  have h := (G.commShiftIso a).inv.naturality g
  dsimp at h
  rw [homEquiv_unit, homEquiv_unit, G.map_comp, (shiftFunctor C a).map_comp, Category.assoc, h,
    shift_unit_app_assoc, Iso.hom_inv_id_app_assoc]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a}) (X : Scheme.{u})
  [NeZero (ringChar Λ)] [NeZero (ringChar Λ')] (e : ℕ) (he : ringChar Λ = ringChar Λ' * e)
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X]

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity

**The reduction of coefficients carries Kummer classes to Kummer classes**: through the
identifications `c : Ψ Λ_X ≅ Λ'_X` and `σ : Ψ Λ_X(1) ≅ Λ'_X(1)` adjoint to the changes of
coefficients `Λ_X ⟶ Res Λ'_X` and `Λ_X(1) ⟶ Res Λ'_X(1)`, the image under `Ψ` of the Kummer class
`κ(v) : Λ_X ⟶ Λ_X(1)[1]`, read in `Λ'_X(1)[1]` through `Ψ(Λ_X(1)[1]) ≅ (Ψ Λ_X(1))[1] ≅ Λ'_X(1)[1]`,
is the Kummer class `κ(v)` over `Λ'`. -/
theorem map_kummerClass_comp_shift
    (σ : (derivedExtendScalars hρ ha X).obj (tateObject Λ X 1) ≅ tateObject Λ' X 1)
    (hσ : σ.hom = ((derivedExtendScalarsAdjunction hρ ha X).homEquiv (tateObject Λ X 1)
      (tateObject Λ' X 1)).symm (tateTwistObjectOneChangeMap ρ X e he))
    (c : (derivedExtendScalars hρ ha X).obj (constantComplex Λ X) ≅ constantComplex Λ' X)
    (hc : c.hom = ((derivedExtendScalarsAdjunction hρ ha X).homEquiv _ _).symm
      (constantComplexChangeMap ρ X))
    (v : Γ(X, ⊤)ˣ) :
    (derivedExtendScalars hρ ha X).map (kummerClass Λ v) ≫
        ((derivedExtendScalars hρ ha X).commShiftIso (1 : ℤ)).hom.app _ ≫ σ.hom⟦(1 : ℤ)⟧' =
      c.hom ≫ kummerClass Λ' v := by
  apply ((derivedExtendScalarsAdjunction hρ ha X).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_commShiftIso_hom_app_comp_shift_map, Adjunction.homEquiv_naturality_right,
    hσ, hc, Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← Category.assoc]
  -- `kummerClass` and `tateObject` are, by definition, `kummerClassOf` and `tateTwistObject`
  erw [kummerClassOf_comp_tateTwistObjectOneChangeMap ρ X e he v]
  rw [Category.assoc, Category.assoc]
  erw [Iso.hom_inv_id_app, Category.comp_id]
  rfl

end AlgebraicGeometry.Etale
