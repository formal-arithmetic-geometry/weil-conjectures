/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralUpperShriekCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibility
public import WeilConjectures.TraceFormula.ExternalProductExtendScalars
public import WeilConjectures.TraceFormula.GraphPieces
public import WeilConjectures.TraceFormula.IntegralCompactPullback
public import WeilConjectures.TraceFormula.RationalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeUpperStarComp

/-!

# Frobenius operators under the extension of scalars `𝒪_E ⟶ ℚ̄_ℓ`

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`, and write
`T_X = ℚ̄_ℓ ⊗ᴸ_{𝒪_E} - : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧`
(`ProEtale.CondensedRing.boundedConstructibleIntegersToPadicAlgCl`). For a Frobenius
correspondence `θ : LΦ^* K ⟶ K` with `𝒪_E`-coefficients, this file compares the operators of `θ`
(`ProEtale.CondensedRing.PadicIntegersRingObj.frobeniusCompactOperator`,
`ProEtale.CondensedRing.PadicIntegersRingObj.graphStalkMap`) with those of its extension of
scalars `ψ = σ⁻¹ ∘ T_X θ : LΦ^* T_X K ⟶ T_X K`
(`ProEtale.CondensedRing.frobeniusCoefficientIntegersToPadicAlgCl`):

* the iterates: `T_X θ_m = σ_m ∘ ψ_m` for `m ≥ 1`
  (`ProEtale.CondensedRing.map_frobeniusCoefficientIterate_integersToPadicAlgCl`);
* the operators on compactly supported cohomology: through the comparison
  `T(RΓ_c(X, K)) ≅ RΓ_c(X, T_X K)`, `T(T_{c_m}(θ_m)) = T_{c_m}(ψ_m)`
  (`ProEtale.CondensedRing.map_frobeniusCompactOperator_integersToPadicAlgCl`);
* the stalk maps: through `T(K_x) ≅ (T_X K)_x`, `T(θ_{m,x}) = ψ_{m,x}`
  (`ProEtale.CondensedRing.map_graphStalkMap_integersToPadicAlgCl`).

These rest on the coherence of the pullback comparisons `σ_f : T_X (Lf^* K) ≅ Lf^* (T_Y K)` with
the composition isomorphisms (`ProEtale.CondensedRing.upperStarIntegersToPadicAlgClObjIso_hom_comp`)
and on the compatibility of the pullback on compactly supported cohomology `h^♯` with the
coefficient change (`ProEtale.CondensedRing.map_compactPullback_app_integersToPadicAlgCl`).

## Implementation details

The last compatibility is stated but not proved here (it is a `sorry`): it unwinds to the
compatibility of the comparison (Shriek) with the identification `Rh_! ≅ Rh_*` of a proper `h`
and with the composition isomorphisms of the lower shriek, both of which are built from the
independence of the lower shriek from the compactification.

The comparisons are stated componentwise (`upperStarIntegersToPadicAlgClObjIso`,
`lowerShriekIntegersToPadicAlgClObjIso`), with objects written as `G.obj (F.obj K)` rather than
`(F ⋙ G).obj K`: unifying the two forms unfolds the derived pullbacks and is very slow.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : PadicAlgCl.FiniteIntermediateField ℓ)

-- The coefficient ring `𝒪_E`.
set_option quotPrecheck false in
local notation "𝒪" => Profinite.padicIntegersRingObj ℓ E.1

-- The coefficient ring `ℚ̄_ℓ`.
set_option quotPrecheck false in
local notation "ℚ̄" => Profinite.padicAlgClRingObj ℓ

section Comparison

variable {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- **(Pull)** for `𝒪_E ⟶ ℚ̄_ℓ` at an object: `T_X (Lf^* K) ≅ Lf^* (T_Y K)`. -/
noncomputable def upperStarIntegersToPadicAlgClObjIso (f : X ⟶ Y)
    (K : Dᵇc(Y.left)⟦𝒪⟧) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj
        ((boundedConstructibleUpperStar 𝒪 ℓ f).obj K) ≅
      (boundedConstructibleUpperStar ℚ̄ ℓ f).obj
        ((boundedConstructibleIntegersToPadicAlgCl ℓ E Y).obj K) :=
  (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E f).app K

/-- **(Shriek)** for `𝒪_E ⟶ ℚ̄_ℓ`: `Rf_!^{𝒪_E} ⋙ T_Y ≅ T_X ⋙ Rf_!^{ℚ̄_ℓ}`, the comparison for
`𝒪_E ⟶ E` followed by the one for `E ⟶ ℚ̄_ℓ`. -/
noncomputable def boundedConstructibleLowerShriekIntegersToPadicAlgClIso (f : X ⟶ Y) :
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 f ⋙
        boundedConstructibleIntegersToPadicAlgCl ℓ E Y ≅
      boundedConstructibleIntegersToPadicAlgCl ℓ E X ⋙ boundedConstructibleLowerShriek ℓ f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedConstructibleLowerShriekExtendScalarsIso ℓ E f)
      (constructibleToPadicAlgCl Y.left ℓ E) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (boundedConstructibleExtendScalars X.left ℓ E)
      (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f) ≪≫
    (Functor.associator _ _ _).symm

/-- **(Shriek)** for `𝒪_E ⟶ ℚ̄_ℓ` at an object: `T_Y (Rf_! K) ≅ Rf_! (T_X K)`. -/
noncomputable def lowerShriekIntegersToPadicAlgClObjIso (f : X ⟶ Y)
    (K : Dᵇc(X.left)⟦𝒪⟧) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E Y).obj
        ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 f).obj K) ≅
      (boundedConstructibleLowerShriek ℓ f).obj
        ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K) :=
  (boundedConstructibleLowerShriekIntegersToPadicAlgClIso E f).app K

/-- The pullback comparison for `𝒪_E ⟶ ℚ̄_ℓ` is the one for `𝒪_E ⟶ E` followed by the one for
`E ⟶ ℚ̄_ℓ`. -/
lemma upperStarIntegersToPadicAlgClObjIso_hom_eq (f : X ⟶ Y) (K : Dᵇc(Y.left)⟦𝒪⟧) :
    (upperStarIntegersToPadicAlgClObjIso E f K).hom =
      (boundedConstructibleToPadicAlgCl X.left ℓ E).map
          ((boundedConstructibleUpperStarExtendScalarsIso ℓ E f).hom.app K) ≫
        (boundedConstructibleUpperStarToPadicAlgClIso ℓ E f).hom.app
          ((boundedConstructibleExtendScalars Y.left ℓ E).obj K) := by
  simp [upperStarIntegersToPadicAlgClObjIso, boundedConstructibleUpperStarIntegersToPadicAlgClIso]
  rfl

/-- The composite of the pullback comparisons for `𝒪_E ⟶ E` and `E ⟶ ℚ̄_ℓ` is compatible with the
composition isomorphisms. -/
lemma upperStarIntegersToPadicAlgCl_comp_aux (f : X ⟶ Y) (g : Y ⟶ Z) (K : Dᵇc(Z.left)⟦𝒪⟧) :
    ((boundedConstructibleToPadicAlgCl X.left ℓ E).map
          ((boundedConstructibleUpperStarExtendScalarsIso ℓ E (f ≫ g)).hom.app K) ≫
        (boundedConstructibleUpperStarToPadicAlgClIso ℓ E (f ≫ g)).hom.app
          ((boundedConstructibleExtendScalars Z.left ℓ E).obj K)) ≫
      (boundedConstructibleUpperStarComp ℚ̄ ℓ f g).hom.app
          ((boundedConstructibleToPadicAlgCl Z.left ℓ E).obj
            ((boundedConstructibleExtendScalars Z.left ℓ E).obj K)) =
      (boundedConstructibleToPadicAlgCl X.left ℓ E).map
          ((boundedConstructibleExtendScalars X.left ℓ E).map
            ((boundedConstructibleUpperStarComp 𝒪 ℓ f g).hom.app K)) ≫
        ((boundedConstructibleToPadicAlgCl X.left ℓ E).map
            ((boundedConstructibleUpperStarExtendScalarsIso ℓ E f).hom.app
              ((boundedConstructibleUpperStar 𝒪 ℓ g).obj K)) ≫
          (boundedConstructibleUpperStarToPadicAlgClIso ℓ E f).hom.app
            ((boundedConstructibleExtendScalars Y.left ℓ E).obj
              ((boundedConstructibleUpperStar 𝒪 ℓ g).obj K))) ≫
        (boundedConstructibleUpperStar ℚ̄ ℓ f).map
          ((boundedConstructibleToPadicAlgCl Y.left ℓ E).map
              ((boundedConstructibleUpperStarExtendScalarsIso ℓ E g).hom.app K) ≫
            (boundedConstructibleUpperStarToPadicAlgClIso ℓ E g).hom.app
              ((boundedConstructibleExtendScalars Z.left ℓ E).obj K)) := by
  have hn := (boundedConstructibleUpperStarToPadicAlgClIso ℓ E f).hom.naturality
    ((boundedConstructibleUpperStarExtendScalarsIso ℓ E g).hom.app K)
  simp only [Functor.comp_map] at hn
  have hA := congrArg (boundedConstructibleToPadicAlgCl X.left ℓ E).map
    (boundedConstructibleUpperStarExtendScalarsIso_hom_app_comp E f g K)
  simp only [Functor.map_comp] at hA
  simp only [Category.assoc, boundedConstructibleUpperStarToPadicAlgClIso_hom_app_comp,
    reassoc_of% hA, Functor.map_comp, reassoc_of% hn]

/-- The pullback comparisons for `𝒪_E ⟶ ℚ̄_ℓ` are compatible with the composition isomorphisms
`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`. -/
theorem upperStarIntegersToPadicAlgClObjIso_hom_comp (f : X ⟶ Y)
    (g : Y ⟶ Z) (K : Dᵇc(Z.left)⟦𝒪⟧) :
    (upperStarIntegersToPadicAlgClObjIso E (f ≫ g) K).hom ≫
        (boundedConstructibleUpperStarComp ℚ̄ ℓ f g).hom.app
          ((boundedConstructibleIntegersToPadicAlgCl ℓ E Z).obj K) =
      (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map
          ((boundedConstructibleUpperStarComp 𝒪 ℓ f g).hom.app K) ≫
        (upperStarIntegersToPadicAlgClObjIso E f
          ((boundedConstructibleUpperStar 𝒪 ℓ g).obj K)).hom ≫
        (boundedConstructibleUpperStar ℚ̄ ℓ f).map
          (upperStarIntegersToPadicAlgClObjIso E g K).hom := by
  simp only [upperStarIntegersToPadicAlgClObjIso_hom_eq]
  exact upperStarIntegersToPadicAlgCl_comp_aux E f g K

/-- Naturality of the pullback comparison for `𝒪_E ⟶ ℚ̄_ℓ`. -/
lemma upperStarIntegersToPadicAlgClObjIso_hom_naturality (f : X ⟶ Y)
    {K L : Dᵇc(Y.left)⟦𝒪⟧} (a : K ⟶ L) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map
        ((boundedConstructibleUpperStar 𝒪 ℓ f).map a) ≫
        (upperStarIntegersToPadicAlgClObjIso E f L).hom =
      (upperStarIntegersToPadicAlgClObjIso E f K).hom ≫
        (boundedConstructibleUpperStar ℚ̄ ℓ f).map
          ((boundedConstructibleIntegersToPadicAlgCl ℓ E Y).map a) :=
  (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E f).hom.naturality a

/-- Naturality of the lower shriek comparison for `𝒪_E ⟶ ℚ̄_ℓ`. -/
lemma lowerShriekIntegersToPadicAlgClObjIso_hom_naturality (f : X ⟶ Y)
    {K L : Dᵇc(X.left)⟦𝒪⟧} (a : K ⟶ L) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E Y).map
        ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 f).map a) ≫
        (lowerShriekIntegersToPadicAlgClObjIso E f L).hom =
      (lowerShriekIntegersToPadicAlgClObjIso E f K).hom ≫
        (boundedConstructibleLowerShriek ℓ f).map
          ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).map a) :=
  (boundedConstructibleLowerShriekIntegersToPadicAlgClIso E f).hom.naturality a

/-- **The pullback on compactly supported cohomology commutes with `𝒪_E ⟶ ℚ̄_ℓ`**: for a proper
`h : Y ⟶ X`, through the comparisons (Shriek) and (Pull), the extension of scalars of the
pullback `h^♯ : RΓ_c(X, K) ⟶ RΓ_c(Y, Lh^* K)` with `𝒪_E`-coefficients is the pullback `h^♯` of
`T_X K`. -/
theorem map_compactPullback_app_integersToPadicAlgCl (h : Y ⟶ X) [IsProper h.left]
    (K : Dᵇc(X.left)⟦𝒪⟧) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)).map
          ((PadicIntegersRingObj.compactPullback ℓ E.1 h).app K) ≫
        (lowerShriekIntegersToPadicAlgClObjIso E (toPoint Y)
          ((boundedConstructibleUpperStar 𝒪 ℓ h).obj K)).hom ≫
        (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
          (upperStarIntegersToPadicAlgClObjIso E h K).hom =
      (lowerShriekIntegersToPadicAlgClObjIso E (toPoint X) K).hom ≫
        (compactPullback ℓ h).app ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K) := by
  sorry

/-- `upperStarIntegersToPadicAlgClObjIso_hom_comp`, composed with a morphism `q`. -/
lemma upperStarIntegersToPadicAlgClObjIso_hom_comp_assoc (f : X ⟶ Y)
    (g : Y ⟶ Z) (K : Dᵇc(Z.left)⟦𝒪⟧) {W : Dᵇc(X.left)⟦ℚ̄⟧}
    (q : (boundedConstructibleUpperStar ℚ̄ ℓ f).obj
      ((boundedConstructibleUpperStar ℚ̄ ℓ g).obj
        ((boundedConstructibleIntegersToPadicAlgCl ℓ E Z).obj K)) ⟶ W) :
    (upperStarIntegersToPadicAlgClObjIso E (f ≫ g) K).hom ≫
        (boundedConstructibleUpperStarComp ℚ̄ ℓ f g).hom.app
          ((boundedConstructibleIntegersToPadicAlgCl ℓ E Z).obj K) ≫ q =
      (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map
          ((boundedConstructibleUpperStarComp 𝒪 ℓ f g).hom.app K) ≫
        (upperStarIntegersToPadicAlgClObjIso E f
          ((boundedConstructibleUpperStar 𝒪 ℓ g).obj K)).hom ≫
        (boundedConstructibleUpperStar ℚ̄ ℓ f).map
          (upperStarIntegersToPadicAlgClObjIso E g K).hom ≫ q := by
  simp only [← Category.assoc, upperStarIntegersToPadicAlgClObjIso_hom_comp]

/-- The pullback comparisons along equal morphisms agree up to the casts. -/
lemma upperStarIntegersToPadicAlgClObjIso_hom_eqToHom_assoc {f g : X ⟶ Y}
    (e : f = g) (K : Dᵇc(Y.left)⟦𝒪⟧)
    {W : Dᵇc(X.left)⟦ℚ̄⟧}
    (q : (boundedConstructibleUpperStar ℚ̄ ℓ g).obj
        ((boundedConstructibleIntegersToPadicAlgCl ℓ E Y).obj K) ⟶ W) :
    (upperStarIntegersToPadicAlgClObjIso E f K).hom ≫ eqToHom (by rw [e]) ≫ q =
      (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map (eqToHom (by rw [e])) ≫
        (upperStarIntegersToPadicAlgClObjIso E g K).hom ≫ q := by
  subst e
  simp

/-- `map_compactPullback_app_integersToPadicAlgCl`, composed with a morphism `q`. -/
lemma map_compactPullback_app_integersToPadicAlgCl_assoc (h : Y ⟶ X) [IsProper h.left]
    (K : Dᵇc(X.left)⟦𝒪⟧)
    {W : Dᵇc((point k).left)⟦ℚ̄⟧}
    (q : (boundedConstructibleLowerShriek ℓ (toPoint Y)).obj
      ((boundedConstructibleUpperStar ℚ̄ ℓ h).obj
        ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K)) ⟶ W) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)).map
          ((PadicIntegersRingObj.compactPullback ℓ E.1 h).app K) ≫
        (lowerShriekIntegersToPadicAlgClObjIso E (toPoint Y)
          ((boundedConstructibleUpperStar 𝒪 ℓ h).obj K)).hom ≫
        (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
          (upperStarIntegersToPadicAlgClObjIso E h K).hom ≫ q =
      (lowerShriekIntegersToPadicAlgClObjIso E (toPoint X) K).hom ≫
        (compactPullback ℓ h).app ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K) ≫ q := by
  simp only [← Category.assoc]
  rw [← map_compactPullback_app_integersToPadicAlgCl]
  simp only [Category.assoc]

end Comparison

section Frobenius

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {Φ : X ⟶ X}

/-- The extension of scalars `ψ = σ⁻¹ ∘ T_X θ : LΦ^* T_X K ⟶ T_X K` of a Frobenius correspondence
`θ : LΦ^* K ⟶ K` with `𝒪_E`-coefficients. -/
noncomputable def frobeniusCoefficientIntegersToPadicAlgCl
    {K : Dᵇc(X.left)⟦𝒪⟧}
    (θ : (boundedConstructibleUpperStar 𝒪 ℓ Φ).obj K ⟶ K) :
    (boundedConstructibleUpperStar ℚ̄ ℓ Φ).obj
        ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K) ⟶
      (boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K :=
  (upperStarIntegersToPadicAlgClObjIso E Φ K).inv ≫
    (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map θ

/-- The first iterate step of `map_frobeniusCoefficientIterate_integersToPadicAlgCl`, for a
morphism `u` equal to `Φ`. -/
lemma map_eqToHom_comp_integersToPadicAlgCl {u : X ⟶ X} (e : u = Φ)
    {K : Dᵇc(X.left)⟦𝒪⟧} (θ : (boundedConstructibleUpperStar 𝒪 ℓ Φ).obj K ⟶ K) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map (eqToHom (by rw [e]) ≫ θ) =
      (upperStarIntegersToPadicAlgClObjIso E u K).hom ≫ eqToHom (by rw [e]) ≫
        frobeniusCoefficientIntegersToPadicAlgCl E θ := by
  subst e
  simp [frobeniusCoefficientIntegersToPadicAlgCl]

/-- The inductive step of `map_frobeniusCoefficientIterate_integersToPadicAlgCl`, for a morphism
`u` equal to `Φ ≫ v`. -/
lemma map_frobeniusCoefficientIterate_integersToPadicAlgCl_step {u v : X ⟶ X} (e : u = Φ ≫ v)
    {K : Dᵇc(X.left)⟦𝒪⟧}
    (θ : (boundedConstructibleUpperStar 𝒪 ℓ Φ).obj K ⟶ K)
    (θv : (boundedConstructibleUpperStar 𝒪 ℓ v).obj K ⟶ K)
    (ψv : (boundedConstructibleUpperStar ℚ̄ ℓ v).obj
        ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K) ⟶
      (boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K)
    (h : (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map θv =
      (upperStarIntegersToPadicAlgClObjIso E v K).hom ≫ ψv) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map
        (eqToHom (by rw [e]) ≫
          (boundedConstructibleUpperStarComp 𝒪 ℓ Φ v).hom.app K ≫
          (boundedConstructibleUpperStar 𝒪 ℓ Φ).map θv ≫ θ) =
      (upperStarIntegersToPadicAlgClObjIso E u K).hom ≫ eqToHom (by rw [e]) ≫
        (boundedConstructibleUpperStarComp ℚ̄ ℓ Φ v).hom.app
          ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K) ≫
        (boundedConstructibleUpperStar ℚ̄ ℓ Φ).map ψv ≫
        frobeniusCoefficientIntegersToPadicAlgCl E θ := by
  subst e
  simp only [eqToHom_refl, Category.id_comp]
  unfold frobeniusCoefficientIntegersToPadicAlgCl
  have hn := upperStarIntegersToPadicAlgClObjIso_hom_naturality E Φ θv
  rw [h, Functor.map_comp] at hn
  conv_rhs => rw [← Category.assoc]
  rw [upperStarIntegersToPadicAlgClObjIso_hom_comp]
  simp only [Category.assoc, Functor.map_comp, ← reassoc_of% hn, Iso.hom_inv_id_assoc]
  rfl

/-- The iterates of the extension of scalars `ψ` of a Frobenius correspondence `θ` are the
extensions of scalars of its iterates: `T_X θ_m = σ_m ∘ ψ_m` for `m ≥ 1`. -/
theorem map_frobeniusCoefficientIterate_integersToPadicAlgCl
    {K : Dᵇc(X.left)⟦𝒪⟧}
    (θ : (boundedConstructibleUpperStar 𝒪 ℓ Φ).obj K ⟶ K)
    {m : ℕ} (hm : 1 ≤ m) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map (frobeniusCoefficientIterate θ m) =
      (upperStarIntegersToPadicAlgClObjIso E (frobeniusIterate Φ m) K).hom ≫
        frobeniusCoefficientIterate (frobeniusCoefficientIntegersToPadicAlgCl E θ) m := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [frobeniusCoefficientIterate_one, frobeniusCoefficientIterate_one]
    exact map_eqToHom_comp_integersToPadicAlgCl E (frobeniusIterate_one Φ) θ
  | succ m _ ih =>
    rw [frobeniusCoefficientIterate_succ_eq, frobeniusCoefficientIterate_succ_eq]
    simp only [upperStarIterateSuccIso, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
      eqToHom_app, Category.assoc]
    exact map_frobeniusCoefficientIterate_integersToPadicAlgCl_step E (frobeniusIterate_succ Φ m)
      θ _ _ ih

/-- **The operators `T_{c_m}` commute with `𝒪_E ⟶ ℚ̄_ℓ`**: through (Shriek), the extension of
scalars of `T_{c_m}(θ_m)` on `RΓ_c(X, K)` is the operator `T_{c_m}(ψ_m)` of the extension of
scalars `ψ` of `θ` on `RΓ_c(X, T_X K)`, for `m ≥ 1`. -/
theorem map_frobeniusCompactOperator_integersToPadicAlgCl [IsProper Φ.left]
    {K : Dᵇc(X.left)⟦𝒪⟧}
    (θ : (boundedConstructibleUpperStar 𝒪 ℓ Φ).obj K ⟶ K)
    {m : ℕ} (hm : 1 ≤ m) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)).map
          (PadicIntegersRingObj.frobeniusCompactOperator θ m) ≫
        (lowerShriekIntegersToPadicAlgClObjIso E (toPoint X) K).hom =
      (lowerShriekIntegersToPadicAlgClObjIso E (toPoint X) K).hom ≫
        frobeniusCompactOperator ℓ (frobeniusCoefficientIntegersToPadicAlgCl E θ) m := by
  unfold PadicIntegersRingObj.frobeniusCompactOperator frobeniusCompactOperator
  simp only [Functor.map_comp, Category.assoc, lowerShriekIntegersToPadicAlgClObjIso_hom_naturality,
    map_frobeniusCoefficientIterate_integersToPadicAlgCl E θ hm,
    map_compactPullback_app_integersToPadicAlgCl_assoc]

/-- **The stalk maps commute with `𝒪_E ⟶ ℚ̄_ℓ`**: through (Pull), the extension of scalars of the
stalk map `v_x` is the stalk map at `x` of the extension of scalars `σ⁻¹ ∘ T_X v` of `v`. -/
theorem map_graphStalkMap_integersToPadicAlgCl
    (K : Dᵇc(X.left)⟦𝒪⟧) (h : X ⟶ X)
    (v : (boundedConstructibleUpperStar 𝒪 ℓ h).obj K ⟶ K)
    (x : RationalPoint X) (hx : x ≫ h = x) :
    (boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)).map
          (PadicIntegersRingObj.graphStalkMap K h v x hx) ≫
        (upperStarIntegersToPadicAlgClObjIso E x K).hom =
      (upperStarIntegersToPadicAlgClObjIso E x K).hom ≫
        Correspondence.graphStalkMap ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K) h
          ((upperStarIntegersToPadicAlgClObjIso E h K).inv ≫
            (boundedConstructibleIntegersToPadicAlgCl ℓ E X).map v) x hx := by
  unfold PadicIntegersRingObj.graphStalkMap Correspondence.graphStalkMap
  simp only [upperStarIntegersToPadicAlgClObjIso_hom_eqToHom_assoc E hx.symm K,
    upperStarIntegersToPadicAlgClObjIso_hom_comp_assoc, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_map_assoc, upperStarIntegersToPadicAlgClObjIso_hom_naturality]

end Frobenius

end AlgebraicGeometry.ProEtale.CondensedRing
