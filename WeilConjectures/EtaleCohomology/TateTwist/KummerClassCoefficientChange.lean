/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.KummerBoundaryRestrictScalarsMap

/-!
# The Kummer classes under a change of coefficients

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings whose characteristics satisfy
`n = n' e`. The change of coefficients of the Tate twists `Λ_X(1) ⟶ Res Λ'_X(1)`
(`AlgebraicGeometry.Etale.tateTwistObjectOneChangeMap`, the `e`-th power map) and of the constant
complexes `Λ_X ⟶ Res Λ'_X` (`AlgebraicGeometry.Etale.constantComplexChangeMap`) are compatible
with the Kummer classes
(`AlgebraicGeometry.Etale.kummerClassOf_comp_tateTwistObjectOneChangeMap`): the change of
coefficients of the Kummer class of a unit is its Kummer class. This follows from the
compatibility of the Kummer boundaries
(`AlgebraicGeometry.Etale.kummerδ_comp_changeMap_restrictScalars`).

Both changes of coefficients are written through the isomorphism
`(Res F)[0] ≅ Res (F[0])` (`AlgebraicGeometry.Etale.singleFunctorRestrictScalarsIso`), whose type
is stated with the derived restriction of scalars `Sheaf.derivedRestrictScalars`: this keeps
every factor in one presentation, so that the compatibility is a cheap instance of the categorical
lemma `CategoryTheory.comp_shift_map_eq_of_eq`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory

/-- A categorical form of the compatibility of Kummer classes with a change of coefficients: for
a functor `G : T' ⥤ T` commuting with the shifts, if `κ = c ≫ a ≫ tinv⟦1⟧'`,
`τ = thom ≫ m₁ ≫ i₁ ≫ G tinv'`, `χ = c ≫ m₃ ≫ i₃ ≫ G cinv'` and `κ' = chom' ≫ b ≫ tinv'⟦1⟧'`
with `tinv ≫ thom = 𝟙` and `cinv' ≫ chom' = 𝟙`, then the square of the boundaries
`a ≫ (m₁ ≫ i₁)⟦1⟧' = m₃ ≫ i₃ ≫ G b ≫ (G.commShiftIso 1).hom` gives
`κ ≫ τ⟦1⟧' = χ ≫ G κ' ≫ (G.commShiftIso 1).hom`. -/
lemma comp_shift_map_eq_of_eq {T T' T₀ : Type*} [Category* T] [Category* T'] [Category* T₀]
    [HasShift T ℤ] [HasShift T' ℤ] (G : T' ⥤ T) [G.CommShift ℤ] (S₀ : T₀ ⥤ T') {Z₁ Z₃ : T₀}
    {P Q A B R₁ R₃ : T} {P' Q' : T'}
    {κ : P ⟶ Q⟦(1 : ℤ)⟧} {c : P ⟶ A} {a : A ⟶ B⟦(1 : ℤ)⟧} {tinv : B ⟶ Q}
    (hκ : κ = c ≫ a ≫ tinv⟦(1 : ℤ)⟧')
    {τ : Q ⟶ G.obj Q'} {thom : Q ⟶ B} {m₁ : B ⟶ R₁} {i₁ : R₁ ⟶ G.obj (S₀.obj Z₁)}
    {tinv' : S₀.obj Z₁ ⟶ Q'}
    (hτ : τ = thom ≫ m₁ ≫ i₁ ≫ G.map tinv')
    {χ : P ⟶ G.obj P'} {m₃ : A ⟶ R₃} {i₃ : R₃ ⟶ G.obj (S₀.obj Z₃)} {cinv' : S₀.obj Z₃ ⟶ P'}
    (hχ : χ = c ≫ m₃ ≫ i₃ ≫ G.map cinv')
    {κ' : P' ⟶ Q'⟦(1 : ℤ)⟧} {chom' : P' ⟶ S₀.obj Z₃} {b : S₀.obj Z₃ ⟶ (S₀.obj Z₁)⟦(1 : ℤ)⟧}
    (hκ' : κ' = chom' ≫ b ≫ tinv'⟦(1 : ℤ)⟧')
    (ht : tinv ≫ thom = 𝟙 B) (hc : cinv' ≫ chom' = 𝟙 _)
    (hK : a ≫ (m₁ ≫ i₁)⟦(1 : ℤ)⟧' = m₃ ≫ i₃ ≫ G.map b ≫ (G.commShiftIso (1 : ℤ)).hom.app _) :
    κ ≫ τ⟦(1 : ℤ)⟧' = χ ≫ G.map κ' ≫ (G.commShiftIso (1 : ℤ)).hom.app Q' := by
  subst hκ hτ hχ hκ'
  simp only [Functor.map_comp, Category.assoc] at hK ⊢
  rw [← Functor.map_comp_assoc (shiftFunctor T (1 : ℤ)) tinv, ht, Functor.map_id, Category.id_comp,
    ← Functor.map_comp_assoc G cinv', hc, Functor.map_id, Category.id_comp,
    Functor.commShiftIso_hom_naturality, reassoc_of% hK]

end CategoryTheory

namespace AlgebraicGeometry.Etale

open Scheme

section

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X : Scheme.{u}}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] (e : ℕ)
  (he : ringChar Λ = ringChar Λ' * e)

/-- `AlgebraicGeometry.Etale.kummerδ_comp_changeMap_restrictScalars`, stated with the
isomorphisms `AlgebraicGeometry.Etale.singleFunctorRestrictScalarsIso`. -/
lemma kummerδ_comp_changeMap_singleFunctorRestrictScalarsIso
    {C : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : C ⟶ X.gmSheaf)
    (hC : ∀ x : X, Projective ((X.uliftPointSmallEtale x).sheafFiber.obj C)) :
    kummerδ Λ φ hC ≫ ((DerivedCategory.singleFunctor _ 0).map
        ((extendScalars Λ X).map (rootsOfUnityPow _ e _ he) ≫
          (extendScalarsChangeMap ρ X).app _) ≫
        (singleFunctorRestrictScalarsIso ρ X (X.rootsOfUnitySheaf (ringChar Λ'))).hom)⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor _ 0).map ((extendScalarsChangeMap ρ X).app C) ≫
        (singleFunctorRestrictScalarsIso ρ X C).hom ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (kummerδ Λ' φ hC) ≫
          ((Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).commShiftIso
            (1 : ℤ)).hom.app _ :=
  shift_map_comp_eq_of_comp_eq_of_heq
    (kummerδ_comp_changeMap_eq_kummerδRestrictScalars ρ e he φ hC)
    (singleFunctorRestrictScalarsIso_hom_comp_map_kummerδ ρ φ hC)
    rfl rfl HEq.rfl HEq.rfl HEq.rfl

end

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (X : Scheme.{u})
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X]
  [NeZero (ringChar Λ)] [NeZero (ringChar Λ')] (e : ℕ) (he : ringChar Λ = ringChar Λ' * e)

/-- The change of coefficients `Λ_X ⟶ Res Λ'_X` of the constant complexes, through the
identifications `Λ_X ≅ (Λ ⊗ ℤ)[0]` of the Kummer classes
(`AlgebraicGeometry.Etale.constantComplexIsoSingleFunctorExtendScalarsInt`). -/
noncomputable def constantComplexChangeMap :
    constantComplex Λ X ⟶
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).obj (constantComplex Λ' X) :=
  (constantComplexIsoSingleFunctorExtendScalarsInt X Λ).hom ≫
    (DerivedCategory.singleFunctor _ 0).map ((extendScalarsChangeMap ρ X).app _) ≫
      (singleFunctorRestrictScalarsIso ρ X _).hom ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          (constantComplexIsoSingleFunctorExtendScalarsInt X Λ').inv

/-- The change of coefficients `Λ_X(1) ⟶ Res Λ'_X(1)` of the Tate twists: through
`Λ_X(1) ≅ (μ_n ⊗ Λ)[0]` (`AlgebraicGeometry.Etale.tateTwistObjectOneIso`), the `e`-th power map
`μ_n ⟶ μ_{n'}` (`n = n' e`) followed by the change of coefficients `μ_{n'} ⊗ Λ ⟶ μ_{n'} ⊗ Λ'`. -/
noncomputable def tateTwistObjectOneChangeMap :
    tateTwistObject Λ X 1 ⟶
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).obj (tateTwistObject Λ' X 1) :=
  (tateTwistObjectOneIso X Λ).hom ≫
    (DerivedCategory.singleFunctor _ 0).map
      ((extendScalars Λ X).map (rootsOfUnityPow _ e _ he) ≫ (extendScalarsChangeMap ρ X).app _) ≫
      (singleFunctorRestrictScalarsIso ρ X _).hom ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (tateTwistObjectOneIso X Λ').inv

/-- **The change of coefficients of a Kummer class is the Kummer class**, with scalars restricted:
for `ρ : Λ →+* Λ'` with `n = n' e`, the Kummer class `κ(u) : Λ_X ⟶ Λ_X(1)[1]` followed by the
change of coefficients of the Tate twist (`tateTwistObjectOneChangeMap`, the `e`-th power map)
is the change of coefficients of the constant complex followed by the restriction of scalars of
the Kummer class `κ(u) : Λ'_X ⟶ Λ'_X(1)[1]`. -/
theorem kummerClassOf_comp_tateTwistObjectOneChangeMap (v : Γ(X, ⊤)ˣ) :
    kummerClassOf X Λ v ≫ (tateTwistObjectOneChangeMap ρ X e he)⟦(1 : ℤ)⟧' =
      constantComplexChangeMap ρ X ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (kummerClassOf X Λ' v) ≫
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).commShiftIso (1 : ℤ)).hom.app _ :=
  comp_shift_map_eq_of_eq (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ)
    (DerivedCategory.singleFunctor _ 0)
    (kummerClassOf_def X Λ v)
    (tateTwistObjectOneChangeMap.eq_1 ρ X e he)
    (constantComplexChangeMap.eq_1 ρ X) (kummerClassOf_def X Λ' v)
    (tateTwistObjectOneIso X Λ).inv_hom_id
    (constantComplexIsoSingleFunctorExtendScalarsInt X Λ').inv_hom_id
    (kummerδ_comp_changeMap_singleFunctorRestrictScalarsIso ρ e he (unitToGmSheaf v)
      (fun x ↦ projective_sheafFiber_constantSheafInt (X.uliftPointSmallEtale x)))

/-- The defining formula of `tateTwistObjectOneChangeMap` (stated through its equation lemma, so
that it is literally the stored body: re-elaborating the body costs a large kernel check). -/
theorem tateTwistObjectOneChangeMap_eq : type_of% @tateTwistObjectOneChangeMap.eq_1.{u} :=
  @tateTwistObjectOneChangeMap.eq_1.{u}

-- the body is heavy: only access it through `tateTwistObjectOneChangeMap_eq`
attribute [irreducible] tateTwistObjectOneChangeMap

end AlgebraicGeometry.Etale
