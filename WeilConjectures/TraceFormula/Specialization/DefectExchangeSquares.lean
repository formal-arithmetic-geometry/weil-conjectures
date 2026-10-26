/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.TraceFormula.Specialization.DefectCentreMap
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorTriangulated

/-!

# The exchange squares of the zero-section map

Let `f : X' ⟶ X` be a morphism of `k`-schemes, `Z = V(I) ⊆ X`, `Z' = f⁻¹ Z` and `f_Z : Z' ⟶ Z`
the restriction of `f`. Write `ε_{X,Z}(L) : Le^* Ψ_X(L) ⟶ Ψ_Z(Li^* L)` for the zero-section map
(`ProEtale.CondensedRing.zeroSectionMap`), `f̃ : 𝒟_{Z'} X' ⟶ 𝒟_Z X` and `f̃_Z : Z' × S ⟶ Z × S` for
the morphisms of models induced by `f`, with special fibres `f_s` and `g_s`.

This file proves, for arbitrary coefficients, the commutative squares of the proof of blueprint
`det-sp-defect-proper-smooth`:

* the *pullback square* (`ProEtale.CondensedRing.zeroSectionMap_upperStar_square`): through the
  pullback exchanges `α_{f̃}` and `α_{f̃_Z}`, `Lg_s^* ε_{X,Z}(L)` corresponds to `ε_{X',Z'}(Lf^* L)`;
  it is the square law of the pullback exchanges
  (`ProEtale.CondensedRing.NearbyCyclesModel.Hom.pullbackExchange_square`) for
  `f̃ ∘ ẽ' = ẽ ∘ f̃_Z`;
* the *pushforward square* (`ProEtale.CondensedRing.zeroSectionMap_lowerStar_square`): through the
  pushforward exchanges `χ_{f̃}`, `χ_{f̃_Z}` and the base change morphisms of the squares
  `e' ≫ f_s = g_s ≫ e` and `i' ≫ f = f_Z ≫ i`, `ε_{X,Z}(Rf_* L')` corresponds to
  `Rg_{s*} ε_{X',Z'}(L')`; both sides have the same adjoint for `Lg_s^* ⊣ Rg_{s*}`, by the pullback
  square.

It also proves the triangulated step of blueprint `det-sp-defect-closed-vanishing`
(`ProEtale.CondensedRing.nonempty_specializationDefect_iso_of_distTriang`): for a distinguished
triangle `A ⟶ B ⟶ D ⟶ A[1]` with `Ψ_Z(Li^* A) = 0` and `ε_{X,Z}(D)` invertible,
`C_{X,Z}(A) ≅ C_{X,Z}(B)`, both being `Le^* Ψ_X(A)[1]`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X X' : Over (Spec (.of k))} (f : X' ⟶ X)
  (I : X.left.IdealSheafData) (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### The commutative squares of the zero sections -/

/-- The square `i' ≫ f = f_Z ≫ i` of the centres. -/
lemma centreι_comp_eq_centreMap_comp :
    (centreι X' (I.comap f.left)).left ≫ f.left = (centreMap f I).left ≫ (centreι X I).left :=
  (congrArg CommaMorphism.left (centreMap_centreι f I)).symm

/-- The square `e' ≫ f_s = g_s ≫ e` of the zero sections of the special fibres. -/
lemma zeroSectionSpecialFibreMap_comp_eq :
    (zeroSectionSpecialFibreMap X' (I.comap f.left) k').left ≫
        (comapSpecialFibreMap f I k').left =
      (centreSpecialFibreMap f I k').left ≫ (zeroSectionSpecialFibreMap X I k').left :=
  (isPullback_zeroSectionSpecialFibreMap f I k').w

/-- **The pullback square of the zero-section maps**: through the pullback exchanges of
`f̃ : 𝒟_{Z'} X' ⟶ 𝒟_Z X` and `f̃_Z : Z' × S ⟶ Z × S`,
`α_{ẽ'}(Lf^* K) ∘ Le'^* α_{f̃}(K) ∘ θ = Ψ_{Z'}(θ) ∘ α_{f̃_Z}(Li^* K) ∘ Lg_s^* ε_{X,Z}(K)`, where the
`θ` are the comparisons of the squares `e' ≫ f_s = g_s ≫ e` and `i' ≫ f = f_Z ≫ i`. -/
lemma zeroSectionMap_upperStar_square
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :
    (pullbackSquareComparison Λ (⟨zeroSectionSpecialFibreMap_comp_eq f I k'⟩ :
        CommSq (zeroSectionSpecialFibreMap X' (I.comap f.left) k').left
          (centreSpecialFibreMap f I k').left (comapSpecialFibreMap f I k').left
          (zeroSectionSpecialFibreMap X I k').left)).hom.app
        (((deformationModel X I k').nearbyCycles Λ).obj K) ≫
      L(((zeroSectionSpecialFibreMap X' (I.comap f.left) k').left)^*⟦Λ⟧).map
        (((comapDeformationModelHom f I k').pullbackExchange Λ).app K) ≫
      zeroSectionMap X' (I.comap f.left) k' Λ (L((f.left)^*⟦Λ⟧).obj K) =
    L(((centreSpecialFibreMap f I k').left)^*⟦Λ⟧).map (zeroSectionMap X I k' Λ K) ≫
      ((centreDeformationModelHom f I k').pullbackExchange Λ).app
        (L(((centreι X I).left)^*⟦Λ⟧).obj K) ≫
      ((deformationModel (centre X' (I.comap f.left)) ⊥ k').nearbyCycles Λ).map
        ((pullbackSquareComparison Λ (⟨centreι_comp_eq_centreMap_comp f I⟩ :
          CommSq (centreι X' (I.comap f.left)).left (centreMap f I).left f.left
            (centreι X I).left)).hom.app K) :=
  NearbyCyclesModel.Hom.pullbackExchange_square Λ
    (zeroSectionDeformationModelHom X' (I.comap f.left) k') (comapDeformationModelHom f I k')
    (centreDeformationModelHom f I k') (zeroSectionDeformationModelHom X I k')
    (zeroSectionDeformationModelHom_total_comp f I k')
    (zeroSectionDeformationModelHom_generic_comp f I k')
    (centreι_comp_eq_centreMap_comp f I) (zeroSectionSpecialFibreMap_comp_eq f I k') K



/-- The abstract shape of `zeroSectionMap_lowerStar_square`: for adjunctions `f^* ⊣ f_*`,
`f_Z^* ⊣ f_{Z*}`, `f_s^* ⊣ f_{s*}`, `g_s^* ⊣ g_{s*}`, natural transformations `α`, `χ` related by
the counit identities, zero-section maps `ε`, `ε'`, comparisons `θ_i`, `θ_e` satisfying the
pullback square, and base change morphisms `β_i`, `β_e` (the exchanges of `θ_i`, `θ_e`), the
pushforward square commutes. -/
lemma zeroSectionMap_lowerStar_square_aux {DX DX' DZ DZ' SX SX' SZ SZ' : Type*} [Category DX]
    [Category DX'] [Category DZ] [Category DZ'] [Category SX] [Category SX'] [Category SZ]
    [Category SZ'] {fu : DX ⥤ DX'} {fl : DX' ⥤ DX} {fZu : DZ ⥤ DZ'} {fZl : DZ' ⥤ DZ}
    {fsu : SX ⥤ SX'} {fsl : SX' ⥤ SX} {gsu : SZ ⥤ SZ'} {gsl : SZ' ⥤ SZ}
    {iu : DX ⥤ DZ} {iu' : DX' ⥤ DZ'} {eu : SX ⥤ SZ} {eu' : SX' ⥤ SZ'}
    {ΨX : DX ⥤ SX} {ΨX' : DX' ⥤ SX'} {ΨZ : DZ ⥤ SZ} {ΨZ' : DZ' ⥤ SZ'}
    (af : fu ⊣ fl) (afZ : fZu ⊣ fZl) (afs : fsu ⊣ fsl) (ags : gsu ⊣ gsl)
    (αf : ΨX ⋙ fsu ⟶ fu ⋙ ΨX') (χf : fl ⋙ ΨX ⟶ ΨX' ⋙ fsl)
    (αg : ΨZ ⋙ gsu ⟶ fZu ⋙ ΨZ') (χg : fZl ⋙ ΨZ ⟶ ΨZ' ⋙ gsl)
    (ε : ∀ K, eu.obj (ΨX.obj K) ⟶ ΨZ.obj (iu.obj K))
    (ε' : ∀ K, eu'.obj (ΨX'.obj K) ⟶ ΨZ'.obj (iu'.obj K))
    (hε' : ∀ {K L : DX'} (φ : K ⟶ L), eu'.map (ΨX'.map φ) ≫ ε' L = ε' K ≫ ΨZ'.map (iu'.map φ))
    (θe : eu ⋙ gsu ≅ fsu ⋙ eu') (θi : iu ⋙ fZu ≅ fu ⋙ iu')
    (βi : fl ⋙ iu ⟶ iu' ⋙ fZl) (βe : fsl ⋙ eu ⟶ eu' ⋙ gsl)
    (hβi : ∀ K, fZu.map (βi.app K) ≫ afZ.counit.app (iu'.obj K) =
      θi.hom.app (fl.obj K) ≫ iu'.map (af.counit.app K))
    (hβe : ∀ K, gsu.map (βe.app K) ≫ ags.counit.app (eu'.obj K) =
      θe.hom.app (fsl.obj K) ≫ eu'.map (afs.counit.app K))
    (hχf : ∀ E, fsu.map (χf.app E) ≫ afs.counit.app (ΨX'.obj E) =
      αf.app (fl.obj E) ≫ ΨX'.map (af.counit.app E))
    (hχg : ∀ E, gsu.map (χg.app E) ≫ ags.counit.app (ΨZ'.obj E) =
      αg.app (fZl.obj E) ≫ ΨZ'.map (afZ.counit.app E))
    (hsq : ∀ K, θe.hom.app (ΨX.obj K) ≫ eu'.map (αf.app K) ≫ ε' (fu.obj K) =
      gsu.map (ε K) ≫ αg.app (iu.obj K) ≫ ΨZ'.map (θi.hom.app K))
    (L' : DX') :
    ε (fl.obj L') ≫ ΨZ.map (βi.app L') ≫ χg.app (iu'.obj L') =
      eu.map (χf.app L') ≫ βe.app (ΨX'.obj L') ≫ gsl.map (ε' L') := by
  apply (ags.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, hχg,
    Adjunction.counit_naturality]
  have hL := αg.naturality (βi.app L')
  simp only [Functor.comp_map] at hL
  rw [reassoc_of% hL, ← ΨZ'.map_comp, hβi, reassoc_of% (hβe (ΨX'.obj L'))]
  have hθ := θe.hom.naturality (χf.app L')
  simp only [Functor.comp_map] at hθ
  have hε := hε' (af.counit.app L')
  simp only [Functor.id_obj, Functor.comp_obj] at hε
  rw [reassoc_of% hθ, ← eu'.map_comp_assoc, hχf, eu'.map_comp, Category.assoc, hε,
    reassoc_of% (hsq (fl.obj L'))]
  simp only [Functor.map_comp, Category.assoc]

/-- **The pushforward square of the zero-section maps**: through the pushforward exchanges `χ` of
`f̃ : 𝒟_{Z'} X' ⟶ 𝒟_Z X` and `f̃_Z : Z' × S ⟶ Z × S` and the base change morphisms `β` of the
squares `i' ≫ f = f_Z ≫ i` and `e' ≫ f_s = g_s ≫ e`,
`χ_{f̃_Z}(Li'^* L') ∘ Ψ_Z(β(L')) ∘ ε_{X,Z}(Rf_* L') = Rg_{s*} ε_{X',Z'}(L') ∘ β(Ψ_{X'} L') ∘
Le^* χ_{f̃}(L')`. Both sides have the same adjoint for `Lg_s^* ⊣ Rg_{s*}`, by the pullback square
`zeroSectionMap_upperStar_square` and the counit identities of the exchanges. -/
lemma zeroSectionMap_lowerStar_square
    (L' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X'.left) Ab.{u + 1})
      (condensedRingObj Λ X'.left))) :
    zeroSectionMap X I k' Λ (R((f.left)_*⟦Λ⟧).obj L') ≫
        ((deformationModel (centre X I) ⊥ k').nearbyCycles Λ).map
          ((baseChangeMap Λ (⟨centreι_comp_eq_centreMap_comp f I⟩ :
            CommSq (centreι X' (I.comap f.left)).left (centreMap f I).left f.left
              (centreι X I).left)).app L') ≫
        ((centreDeformationModelHom f I k').pushforwardExchange Λ).app
          (L(((centreι X' (I.comap f.left)).left)^*⟦Λ⟧).obj L') =
      L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).map
          (((comapDeformationModelHom f I k').pushforwardExchange Λ).app L') ≫
        (baseChangeMap Λ (⟨zeroSectionSpecialFibreMap_comp_eq f I k'⟩ :
          CommSq (zeroSectionSpecialFibreMap X' (I.comap f.left) k').left
            (centreSpecialFibreMap f I k').left (comapSpecialFibreMap f I k').left
            (zeroSectionSpecialFibreMap X I k').left)).app
          (((deformationModel X' (I.comap f.left) k').nearbyCycles Λ).obj L') ≫
        R(((centreSpecialFibreMap f I k').left)_*⟦Λ⟧).map
          (zeroSectionMap X' (I.comap f.left) k' Λ L') :=
  zeroSectionMap_lowerStar_square_aux (derivedUpperStarLowerStarAdjunction Λ f.left)
    (derivedUpperStarLowerStarAdjunction Λ (centreMap f I).left)
    (derivedUpperStarLowerStarAdjunction Λ (comapSpecialFibreMap f I k').left)
    (derivedUpperStarLowerStarAdjunction Λ (centreSpecialFibreMap f I k').left)
    ((comapDeformationModelHom f I k').pullbackExchange Λ)
    ((comapDeformationModelHom f I k').pushforwardExchange Λ)
    ((centreDeformationModelHom f I k').pullbackExchange Λ)
    ((centreDeformationModelHom f I k').pushforwardExchange Λ)
    (zeroSectionMap X I k' Λ) (zeroSectionMap X' (I.comap f.left) k' Λ)
    (zeroSectionMap_naturality X' (I.comap f.left) k' Λ)
    (pullbackSquareComparison Λ (⟨zeroSectionSpecialFibreMap_comp_eq f I k'⟩ :
      CommSq (zeroSectionSpecialFibreMap X' (I.comap f.left) k').left
        (centreSpecialFibreMap f I k').left (comapSpecialFibreMap f I k').left
        (zeroSectionSpecialFibreMap X I k').left))
    (pullbackSquareComparison Λ (⟨centreι_comp_eq_centreMap_comp f I⟩ :
      CommSq (centreι X' (I.comap f.left)).left (centreMap f I).left f.left (centreι X I).left))
    (baseChangeMap Λ (⟨centreι_comp_eq_centreMap_comp f I⟩ :
      CommSq (centreι X' (I.comap f.left)).left (centreMap f I).left f.left (centreι X I).left))
    (baseChangeMap Λ (⟨zeroSectionSpecialFibreMap_comp_eq f I k'⟩ :
      CommSq (zeroSectionSpecialFibreMap X' (I.comap f.left) k').left
        (centreSpecialFibreMap f I k').left (comapSpecialFibreMap f I k').left
        (zeroSectionSpecialFibreMap X I k').left))
    (Adjunction.exchangeRight_app_comp_counit' _ _ _ _ rfl)
    (Adjunction.exchangeRight_app_comp_counit' _ _ _ _ rfl)
    ((comapDeformationModelHom f I k').map_pushforwardExchange_app_comp_counit_app Λ)
    ((centreDeformationModelHom f I k').map_pushforwardExchange_app_comp_counit_app Λ)
    (zeroSectionMap_upperStar_square f I k' Λ) L'

end AlgebraicGeometry.ProEtale.CondensedRing
