/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothPadicIntegers
public import WeilConjectures.Tactic.ExactModProofs
public import WeilConjectures.Tactic.TransportModProofs

/-!

# Coefficient change for restricted base change maps

For a commutative square `sq : g' ≫ p' = p ≫ g` and a morphism `i : Z ⟶ Y'`, consider the
*restricted base change map* `Li^* (Lg^* Rp_* K ⟶ Rp'_* Lg'^* K)`, the base change map followed by
the pullback along `i` (for nearby cycles: the base change of `Rj_*` restricted to the special
fibre). This file shows that it is compatible with the change of coefficients
`𝔽_E ⟵ 𝒪_E ⟶ E ⟶ ℚ̄_ℓ`:

* `ProEtale.CondensedRing.nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app`:
  extension of scalars along any `a : Λ ⟶ Λ'` carries the restricted base change map at `K` to
  the one at `T K`, if the pushforwards commute with `T` at `K` and `Lg'^* K`;
* `ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicIntegers_of_residueField`
  (derived Nakayama): with `𝒪_E`-coefficients, the restricted base change map at a derived
  complete bounded below `K` is invertible if it is invertible with `𝔽_E`-coefficients at
  `𝔽_E ⊗ᴸ K`;
* `ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicSubfield_of_padicIntegers` and
  `ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicAlgCl_of_padicSubfield`: the
  invertibility passes from `𝒪_E` to `E` to `ℚ̄_ℓ` by flat extension of scalars.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

/-- A functor maps an isomorphism to an isomorphism (with the isomorphism as an explicit
hypothesis). -/
lemma isIso_map_of_isIso {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {A B : C}
    {f : A ⟶ B} (h : IsIso f) : IsIso (F.map f) :=
  inferInstance

/-- If `H (α_A)` is an isomorphism and `A ≅ B`, then so is `H (α_B)`. -/
lemma isIso_map_app_of_iso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D} (α : F ⟶ G) (H : D ⥤ E) {A B : C} (e : A ≅ B) (h : IsIso (H.map (α.app A))) :
    IsIso (H.map (α.app B)) :=
  (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight α H) e).1 h

/-- A morphism isomorphic, as an arrow, to an isomorphism is an isomorphism. -/
lemma isIso_of_nonempty_arrowIso_of_isIso {C : Type*} [Category* C] {A B A' B' : C}
    {f : A ⟶ B} {g : A' ⟶ B'} (e : Nonempty (Arrow.mk f ≅ Arrow.mk g)) (hg : IsIso g) :
    IsIso f :=
  ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff e.some).2 hg

/-- Transport of an arrow isomorphism `F' f ≅ g` along a natural isomorphism
`F ⋙ G ≅ F' ⋙ G'`: `G (F f) ≅ G' g`. -/
lemma nonempty_arrowIso_map_map_of_iso {C D D' E : Type*} [Category* C] [Category* D]
    [Category* D'] [Category* E] {F : C ⥤ D} {G : D ⥤ E} {F' : C ⥤ D'} {G' : D' ⥤ E}
    (e : F ⋙ G ≅ F' ⋙ G') {A B : C} (f : A ⟶ B) {A' B' : D'} {g : A' ⟶ B'}
    (k : Nonempty (Arrow.mk (F'.map f) ≅ Arrow.mk g)) :
    Nonempty (Arrow.mk (G.map (F.map f)) ≅ Arrow.mk (G'.map g)) :=
  ⟨Arrow.isoMk' (G.map (F.map f)) (G'.map (F'.map f)) (e.app A) (e.app B)
    (e.hom.naturality f).symm ≪≫ G'.mapArrow.mapIso k.some⟩

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section General

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Extension of scalars and the restricted base change map**: for `a : Λ ⟶ Λ'` with extension
of scalars `T`, if the comparisons `T ∘ Rh_* ⟶ Rh_* ∘ T` are invertible at `K` for `h = p` and at
`Lg'^* K` for `h = p'`, then `T` of `Li^* BC_sq^Λ(K)` and `Li^* BC_sq^Λ'(T K)` are isomorphic
arrows. -/
theorem nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app (sq : CommSq g' p' p g)
    (i : Z ⟶ Y')
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h₁ : IsIso ((derivedUpperStarExtendScalarsPushHom a p).app K))
    (h₂ : IsIso ((derivedUpperStarExtendScalarsPushHom a p').app
      ((g')^*⟦Λ⟧.leftDerivedFunctor.obj K))) :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctor.map
        ((L((i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ p)
          (derivedUpperStarLowerStarAdjunction Λ p') (pullbackSquareComparison Λ sq)).app K))) ≅
      Arrow.mk ((L((i)^*⟦Λ'⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ' p)
          (derivedUpperStarLowerStarAdjunction Λ' p') (pullbackSquareComparison Λ' sq)).app
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K)))) := by
  have k := nonempty_arrowIso_map_exchangeRight_derivedExtendScalars_of_nonFlat' a
    (derivedUpperStarExtendScalarsIsoCompCoherence a) sq K h₁ h₂
  exact nonempty_arrowIso_map_map_of_iso (F := L((i)^*⟦Λ⟧))
    (G := L(Mod.extendScalars (coefficientMap a Z)))
    (F' := L(Mod.extendScalars (coefficientMap a Y'))) (G' := L((i)^*⟦Λ'⟧))
    (derivedUpperStarExtendScalarsIso a i) _ (by exact_mod_proofs k)

/-- The restricted base change map with coefficients `Λ'` is invertible at `T K` if the one with
coefficients `Λ` is invertible at `K`, under the hypotheses of
`ProEtale.CondensedRing.nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app`. -/
theorem isIso_map_baseChangeMap_app_extendScalars (sq : CommSq g' p' p g) (i : Z ⟶ Y')
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h₁ : IsIso ((derivedUpperStarExtendScalarsPushHom a p).app K))
    (h₂ : IsIso ((derivedUpperStarExtendScalarsPushHom a p').app
      ((g')^*⟦Λ⟧.leftDerivedFunctor.obj K)))
    (hK : IsIso ((L((i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ p)
          (derivedUpperStarLowerStarAdjunction Λ p') (pullbackSquareComparison Λ sq)).app K))) :
    IsIso ((L((i)^*⟦Λ'⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ' p)
          (derivedUpperStarLowerStarAdjunction Λ' p') (pullbackSquareComparison Λ' sq)).app
      ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K))) :=
  isIso_of_nonempty_arrowIso_map _ hK
    (nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app a sq i K h₁ h₂)

end General

section Flat

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Flat extension of scalars and the restricted base change map**: the analogue of
`ProEtale.CondensedRing.nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app` for a
flat `a`, with the comparisons `derivedPushHom a`. -/
theorem nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app_of_flat
    (H : DerivedPullIsoCompCoherence a) (sq : CommSq g' p' p g) (i : Z ⟶ Y')
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h₁ : IsIso ((derivedPushHom a p).app K))
    (h₂ : IsIso ((derivedPushHom a p').app ((g')^*⟦Λ⟧.leftDerivedFunctor.obj K))) :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctor.map
        ((L((i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ p)
          (derivedUpperStarLowerStarAdjunction Λ p') (pullbackSquareComparison Λ sq)).app K))) ≅
      Arrow.mk ((L((i)^*⟦Λ'⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ' p)
          (derivedUpperStarLowerStarAdjunction Λ' p') (pullbackSquareComparison Λ' sq)).app
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K)))) := by
  have k := nonempty_arrowIso_map_exchangeRight_derivedExtendScalars a H sq K h₁ h₂
  exact nonempty_arrowIso_map_map_of_iso (F := L((i)^*⟦Λ⟧))
    (G := L(Mod.extendScalars (coefficientMap a Z)))
    (F' := L(Mod.extendScalars (coefficientMap a Y'))) (G' := L((i)^*⟦Λ'⟧))
    (derivedPullIso a i) _ (by exact_mod_proofs k)

/-- **Flat extension of scalars and the restricted base change map**: the analogue of
`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_extendScalars` for a flat `a`, with the
comparisons `derivedPushHom a`. -/
theorem isIso_map_baseChangeMap_app_derivedExtendScalars (H : DerivedPullIsoCompCoherence a)
    (sq : CommSq g' p' p g) (i : Z ⟶ Y')
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h₁ : IsIso ((derivedPushHom a p).app K))
    (h₂ : IsIso ((derivedPushHom a p').app ((g')^*⟦Λ⟧.leftDerivedFunctor.obj K)))
    (hK : IsIso ((L((i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ p)
          (derivedUpperStarLowerStarAdjunction Λ p') (pullbackSquareComparison Λ sq)).app K))) :
    IsIso ((L((i)^*⟦Λ'⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ' p)
          (derivedUpperStarLowerStarAdjunction Λ' p') (pullbackSquareComparison Λ' sq)).app
      ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K))) :=
  isIso_of_nonempty_arrowIso_map _ hK
    (nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app_of_flat a H sq i K h₁ h₂)

end Flat

section Transport

variable {Λ₁ Λ₂ Λ₃ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ₁]
  [IsCommMonObj Λ₁] [MonObj Λ₂] [IsCommMonObj Λ₂] [MonObj Λ₃] [IsCommMonObj Λ₃]
  (a : Λ₁ ⟶ Λ₂) [IsMonHom a] (b : Λ₂ ⟶ Λ₃) [IsMonHom b]
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The restricted base change map with coefficients `Λ₃` is invertible at `K` as soon as it is
invertible at `T_b (T_a K₀)` for some `K₀` with `T_b (T_a K₀) ≅ K`. -/
lemma isIso_map_baseChangeMap_app_of_iso_extendScalars (sq : CommSq g' p' p g) (i : Z ⟶ Y')
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₁ X)))
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₃ X))}
    (e : Nonempty ((Mod.extendScalars (coefficientMap b X)).leftDerivedFunctor.obj
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K₀) ≅ K))
    (h : IsIso ((L((i)^*⟦Λ₃⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ₃ p) (derivedUpperStarLowerStarAdjunction Λ₃ p')
      (pullbackSquareComparison Λ₃ sq)).app
        ((Mod.extendScalars (coefficientMap b X)).leftDerivedFunctor.obj
          ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K₀))))) :
    IsIso ((L((i)^*⟦Λ₃⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ₃ p) (derivedUpperStarLowerStarAdjunction Λ₃ p')
      (pullbackSquareComparison Λ₃ sq)).app K)) :=
  isIso_map_app_of_iso _ _ e.some h

end Transport

section Coefficients

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Derived Nakayama for morphisms, via extension of scalars**: a morphism of derived complete
`𝒪_E`-complexes whose extension of scalars to `𝔽_E` is an isomorphism is an isomorphism. -/
theorem isIso_of_derivedCompleteIntegers_of_isIso_extendScalars_map {X : Scheme.{u}}
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))} (φ : K ⟶ L)
    (hK : derivedCompleteIntegers ℓ E X K) (hL : derivedCompleteIntegers ℓ E X L)
    (h : IsIso ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map φ)) :
    IsIso φ := by
  obtain ⟨C, g, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle φ
  have hF := (Mod.extendScalars
    (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.map_distinguished _ hT
  have hC : derivedCompleteIntegers ℓ E X C :=
    derivedCompleteIntegers_ext₂ _ (Pretriangulated.rot_of_distTriang _ hT) hL
      (derivedCompleteIntegers_shift hK 1)
  refine (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_derivedCompleteIntegers_of_isZero_derivedReduction hC ?_)
  rw [isZero_derivedReduction_iff]
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hF).2 h

/-- **Derived Nakayama for the restricted base change map**: with `𝒪_E`-coefficients, the
restricted base change map `Li^* BC_sq(K₀)` at a derived complete bounded below `K₀` is invertible
if the restricted base change map with `𝔽_E`-coefficients is invertible at `𝔽_E ⊗ᴸ K₀`. -/
theorem isIso_map_baseChangeMap_app_padicIntegers_of_residueField [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace Y]
    [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Z]
    [QuasiSeparatedSpace Z] (sq : CommSq g' p' p g) (i : Z ⟶ Y')
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) [K₀.IsGE n]
    (hK₀ : derivedCompleteIntegers ℓ E X K₀)
    (h : IsIso ((L((i)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)⟧)).map
      ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) p)
        (derivedUpperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) p')
        (pullbackSquareComparison
          (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) sq)).app
        ((Mod.extendScalars (coefficientMap
          (Profinite.padicIntegersRingObjToResidueField ℓ E.1) X)).leftDerivedFunctor.obj K₀)))) :
    IsIso ((L((i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p')
      (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1) sq)).app K₀)) := by
  have : ((g')^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.leftDerivedFunctor.obj K₀).IsGE n :=
    isGE_leftDerivedUpperStar_obj _ g' K₀ n
  have h₁ := isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E p K₀ n
  have h₂ := isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E p'
    ((g')^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.leftDerivedFunctor.obj K₀) n
  have k := nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app
    (Profinite.padicIntegersRingObjToResidueField ℓ E.1) sq i K₀ h₁ h₂
  have hext := isIso_of_nonempty_arrowIso_of_isIso k (by exact_mod_proofs h)
  have hsrc := derivedCompleteIntegers_leftDerivedUpperStar_obj i
    (derivedCompleteIntegers_leftDerivedUpperStar_obj g
      (derivedCompleteIntegers_rightDerivedLowerStar_obj p hK₀))
  have htgt := derivedCompleteIntegers_leftDerivedUpperStar_obj i
    (derivedCompleteIntegers_rightDerivedLowerStar_obj p'
      (derivedCompleteIntegers_leftDerivedUpperStar_obj g' hK₀))
  exact isIso_of_derivedCompleteIntegers_of_isIso_extendScalars_map ℓ E _ hsrc htgt
    (by exact_mod_proofs hext)

/-- **From `𝒪_E` to `E` for the restricted base change map**: for quasi-compact quasi-separated
vertical maps, if the restricted base change map with `𝒪_E`-coefficients is invertible at a
bounded below `K₀`, then the one with `E`-coefficients is invertible at `E ⊗ᴸ_{𝒪_E} K₀`. -/
theorem isIso_map_baseChangeMap_app_padicSubfield_of_padicIntegers [QuasiCompact p]
    [QuasiSeparated p] [QuasiCompact p'] [QuasiSeparated p'] (sq : CommSq g' p' p g)
    (i : Z ⟶ Y')
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) (hn : K₀.IsGE n)
    (h : IsIso ((L((i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p')
      (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1) sq)).app K₀))) :
    IsIso ((L((i)^*⟦Profinite.continuousMapRingObj E.1⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E.1) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E.1) p')
      (pullbackSquareComparison (Profinite.continuousMapRingObj E.1) sq)).app
        ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
          X)).leftDerivedFunctor.obj K₀))) := by
  have := isGE_leftDerivedUpperStar_obj (Profinite.padicIntegersRingObj ℓ E.1) g' K₀ n
  have hE := isIso_map_baseChangeMap_app_derivedExtendScalars
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) (derivedPullIsoCompCoherence _) sq i K₀
    (isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E p K₀ n)
    (isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E p'
      ((g')^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.leftDerivedFunctor.obj K₀) n)
    (by exact_mod_proofs h)
  exact_mod_proofs hE

/-- **From `E` to `ℚ̄_ℓ` for the restricted base change map**: for quasi-compact quasi-separated
vertical maps, if the restricted base change map with `E`-coefficients is invertible at a
bounded below `K`, then the one with `ℚ̄_ℓ`-coefficients is invertible at `ℚ̄_ℓ ⊗ᴸ_E K`. -/
theorem isIso_map_baseChangeMap_app_padicAlgCl_of_padicSubfield [QuasiCompact p]
    [QuasiSeparated p] [QuasiCompact p'] [QuasiSeparated p'] (sq : CommSq g' p' p g)
    (i : Z ⟶ Y')
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X))) (n : ℤ) (hn : K.IsGE n)
    (h : IsIso ((L((i)^*⟦Profinite.continuousMapRingObj E.1⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E.1) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E.1) p')
      (pullbackSquareComparison (Profinite.continuousMapRingObj E.1) sq)).app K))) :
    IsIso ((L((i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p')
      (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) sq)).app
      ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        X)).leftDerivedFunctor.obj K))) := by
  have := isGE_leftDerivedUpperStar_obj (Profinite.continuousMapRingObj E.1) g' K n
  have hA := isIso_map_baseChangeMap_app_derivedExtendScalars
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) (derivedPullIsoCompCoherence _) sq i K
    (isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E p K n)
    (isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E p'
      ((g')^*⟦Profinite.continuousMapRingObj E.1⟧.leftDerivedFunctor.obj K) n)
    (by exact_mod_proofs h)
  exact_mod_proofs hA

/-- **The `ℚ̄_ℓ`-restricted base change map from integral models**: for quasi-compact
quasi-separated vertical maps and a topologically noetherian `X`, the restricted base change map
with `ℚ̄_ℓ`-coefficients is invertible at a bounded constructible `K` as soon as, for every finite
subextension `E ⊆ ℚ̄_ℓ`, the one with `𝒪_E`-coefficients is invertible at every bounded
constructible `𝒪_E`-complex: `K ≅ ℚ̄_ℓ ⊗ᴸ_E (E ⊗ᴸ_{𝒪_E} K₀)` for an integral model `K₀`
(`ProEtale.exists_padicAlgCl_iso_integralModel`). -/
theorem isIso_map_baseChangeMap_app_padicAlgCl_of_integral [TopologicalSpace.NoetherianSpace X]
    [QuasiCompact p] [QuasiSeparated p] [QuasiCompact p'] [QuasiSeparated p']
    (sq : CommSq g' p' p g) (i : Z ⟶ Y')
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hK : boundedConstructible _ K)
    (h : ∀ (E : FiniteIntermediateField ℓ) (K₀ : DerivedCategory (Mod
      (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))),
      boundedConstructible _ K₀ →
        IsIso ((L((i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p)
          (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p')
          (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1) sq)).app K₀))) :
    IsIso ((L((i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p')
      (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) sq)).app K)) := by
  obtain ⟨E, K₀, ⟨e⟩⟩ := exists_padicAlgCl_iso_integralModel X ℓ ⟨K, hK⟩
  -- the integral model as an object of the ambient derived category, `ℚ̄_ℓ ⊗ (E ⊗ K₀) ≅ K`
  have hobj : (ObjectProperty.ι _).obj (⟨K, hK⟩ : PadicAlgClConstructible X ℓ) = K := rfl
  have i₁ := (ObjectProperty.liftCompιIso (boundedConstructible (padicAlgClRingObj X ℓ))
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙ derivedExtendScalarsToPadicAlgCl X ℓ E)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj X ℓ E K)).app
      ((boundedConstructibleExtendScalars X ℓ E).obj K₀)
  have i₂ := (derivedExtendScalarsToPadicAlgCl X ℓ E).mapIso
    ((boundedConstructibleExtendScalarsCompatibility X ℓ E).app K₀)
  have e' := Nonempty.intro ((i₁ ≪≫ i₂).symm ≪≫ (ObjectProperty.ι _).mapIso e ≪≫ eqToIso hobj)
  have hK₀ : boundedConstructible _ K₀.obj := by exact_mod_proofs K₀.property
  obtain ⟨n, hn⟩ := hK₀.1.1
  have hE := isIso_map_baseChangeMap_app_padicSubfield_of_padicIntegers ℓ E sq i K₀.obj n hn
    (h E K₀.obj hK₀)
  have hnE := isGE_leftDerivedFunctor_extendScalars_obj
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) K₀.obj n
  have hA := isIso_map_baseChangeMap_app_padicAlgCl_of_padicSubfield ℓ E sq i
    ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
      X)).leftDerivedFunctor.obj K₀.obj) n hnE (by exact_mod_proofs hE)
  have hgen := isIso_map_baseChangeMap_app_of_iso_extendScalars
    (padicIntegersRingObjToContinuousMapRingObj ℓ E)
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) sq i K₀.obj (K := K)
  -- the hypotheses carry different proofs of `Precoherent Profinite`, which are identified
  clear i₁ i₂ hobj e hK₀ hE hnE
  revert E K₀ n hn hA e' hgen
  normalize_precoherent
  intro E K₀ e' n hn hA hgen
  exact hgen e' hA

end Coefficients

end AlgebraicGeometry.ProEtale.CondensedRing
