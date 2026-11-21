/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.HomComp

/-!

# The specialization map of a model with a projection

Let `M` be a model of `X` with special fibre `X'` (total space `𝒳`, inclusions `j : 𝒳_η̄ ⟶ 𝒳`,
`i : X' ⟶ 𝒳` and identification `ε : 𝒳_η̄ ⟶ X`), and let `p : 𝒳 ⟶ X` be a projection with
`j ≫ p = ε`, as for a constant family `X × S`. For `π = i ≫ p : X' ⟶ X`, the *specialization
map*
```
σ(K) : Lπ^* K ⟶ Ψ_M(K) = Li^* Rj_* Lε^* K
```
(`NearbyCyclesModel.specialization`) is the restriction to the special fibre of the unit of
`Lj^* ⊣ Rj_*` at `Lp^* K`, through the composition isomorphisms `Lπ^* ≅ Lp^* ⋙ Li^*` and
`Lε^* ≅ Lp^* ⋙ Lj^*`.

## Main results

- `NearbyCyclesModel.Hom.map_specialization_app_comp_pullbackExchange_app`: for a morphism of
  models `φ : M ⟶ N` over `f` and `f'` compatible with projections, the pullback exchange
  `α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` carries `Lf'^* σ_N` to `σ_M(Lf^*)`.
- `NearbyCyclesModel.Hom.specialization_app_comp_pushforwardExchange_app`: the pushforward
  exchange `χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M` carries `σ_N(Rf_*)` to `Rf'_* σ_M` composed with the base
  change map `Lπ_N^* Rf_* ⟶ Rf'_* Lπ_M^*`.

## Implementation details

The morphism `π` is a parameter, together with a proof of `i ≫ p = π`, rather than the composite
`i ≫ p` itself: for concrete models, `π` can then be a named morphism of special fibres, and the
kernel is never asked to compare composites whose middle objects are spelled differently (such as
the total space of a model and its definition), which it does by unfolding the definitions.

As in `WeilConjectures.SixFunctors.NearbyCycles.Exchange`, the diagram chases are carried out in
abstract categories and then instantiated, the pullback comparisons being identified by the
pasting law `ProEtale.CondensedRing.pullbackSquareComparison_hom_app_paste_of_eq`.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Abstract computations -/

section Abstract

private lemma map_specialization_comp_pullbackExchange_aux
    {DY' DX' DTN DTM DGN DGM DY DX : Type*} [Category DY'] [Category DX'] [Category DTN]
    [Category DTM] [Category DGN] [Category DGM] [Category DY] [Category DX]
    {Fp' : DY' ⥤ DX'} {IN : DTN ⥤ DY'} {IM : DTM ⥤ DX'} {T : DTN ⥤ DTM}
    {JN : DTN ⥤ DGN} {JNs : DGN ⥤ DTN} {JM : DTM ⥤ DGM} {JMs : DGM ⥤ DTM}
    (adjN : JN ⊣ JNs) (adjM : JM ⊣ JMs)
    {G : DGN ⥤ DGM} {EN : DY ⥤ DGN} {EM : DX ⥤ DGM} {F : DY ⥤ DX}
    (θi : IN ⋙ Fp' ≅ T ⋙ IM) (θi' : T ⋙ IM ≅ IN ⋙ Fp') (hθi : θi' = θi.symm)
    (θj : T ⋙ JM ≅ JN ⋙ G) (θε : EN ⋙ G ≅ F ⋙ EM) (θε' : F ⋙ EM ≅ EN ⋙ G)
    (hθε : θε' = θε.symm)
    {oY' : DY'} {oX' : DX'} {oTN : DTN} {oTM : DTM} {oY : DY}
    (uf' : Fp'.obj oY' ≅ oX') (uf'' : oX' ≅ Fp'.obj oY') (huf : uf'' = uf'.symm)
    (uiN : IN.obj oTN ≅ oY') (uiM : IM.obj oTM ≅ oX')
    (ut : T.obj oTN ≅ oTM) (ujN : JN.obj oTN ≅ EN.obj oY) (ujM : JM.obj oTM ≅ EM.obj (F.obj oY))
    (hi : uiM.inv ≫ IM.map ut.inv ≫ θi'.hom.app oTN = uf''.hom ≫ Fp'.map uiN.inv)
    (hj : ujM.inv ≫ JM.map ut.inv ≫ θj.hom.app oTN = θε'.hom.app oY ≫ G.map ujN.inv)
    (α : (EN ⋙ JNs ⋙ IN) ⋙ Fp' ⟶ F ⋙ EM ⋙ JMs ⋙ IM)
    (hα : α = Functor.whiskerLeft (EN ⋙ JNs) θi.hom ≫
          Functor.whiskerRight (Functor.whiskerLeft EN (mateEquiv adjN adjM θj.hom) ≫
            Functor.whiskerRight θε.hom JMs) IM)
    (σN : oY' ⟶ (EN ⋙ JNs ⋙ IN).obj oY)
    (hσN : σN = uiN.inv ≫ IN.map (adjN.unit.app oTN ≫ JNs.map ujN.hom))
    (σM : oX' ⟶ (EM ⋙ JMs ⋙ IM).obj (F.obj oY))
    (hσM : σM = uiM.inv ≫ IM.map (adjM.unit.app oTM ≫ JMs.map ujM.hom)) :
    Fp'.map σN ≫ α.app oY = uf'.hom ≫ σM := by
  subst hθi hθε huf hα hσN hσM
  have hi' : θi.hom.app oTN = Fp'.map uiN.hom ≫ uf'.hom ≫ uiM.inv ≫ IM.map ut.inv := by
    rw [← cancel_mono (θi.inv.app oTN), Iso.hom_inv_id_app]
    simp only [Iso.symm_hom] at hi
    simp only [Category.assoc, hi, Iso.hom_inv_id_assoc, ← Functor.map_comp, Iso.hom_inv_id]
    simp
  have hj' : θj.hom.app oTN = JM.map ut.hom ≫ ujM.hom ≫ θε.inv.app oY ≫ G.map ujN.inv := by
    simp only [Iso.symm_hom] at hj
    rw [← hj]
    simp [← Functor.map_comp_assoc]
  have nat := θi.hom.naturality (adjN.unit.app oTN ≫ JNs.map ujN.hom)
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at nat
  have hβ := (mateEquiv adjN adjM θj.hom).naturality ujN.hom
  simp only [Functor.comp_map] at hβ
  have hu := unit_mateEquiv adjN adjM θj.hom oTN
  have hn := adjM.unit.naturality ut.inv
  simp only [Functor.id_map, Functor.comp_map] at hn
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.map_comp, Category.assoc]
  rw [reassoc_of% nat, hi']
  simp only [Category.assoc, ← Fp'.map_comp_assoc, Iso.inv_hom_id, Fp'.map_id, Category.id_comp]
  congr 2
  simp only [← IM.map_comp]
  congr 1
  rw [reassoc_of% hβ, reassoc_of% hu, reassoc_of% hn, hj']
  simp [← Functor.map_comp]

private lemma whiskerLeft_comp_mateEquiv_aux {DY DX DY' DX' : Type*} [Category DY] [Category DX]
    [Category DY'] [Category DX'] {Ff : DY ⥤ DX} {Rf : DX ⥤ DY} {Ff' : DY' ⥤ DX'}
    {Rf' : DX' ⥤ DY'} (adjf : Ff ⊣ Rf) (adjf' : Ff' ⊣ Rf') {PN ΨN : DY ⥤ DY'} {PM ΨM : DX ⥤ DX'}
    (σN : PN ⟶ ΨN) (σM : PM ⟶ ΨM) (c : PN ⋙ Ff' ⟶ Ff ⋙ PM) (α : ΨN ⋙ Ff' ⟶ Ff ⋙ ΨM)
    (h : ∀ K, Ff'.map (σN.app K) ≫ α.app K = c.app K ≫ σM.app (Ff.obj K))
    (χ : Rf ⋙ ΨN ⟶ ΨM ⋙ Rf') (hχ : χ = mateEquiv adjf adjf' α)
    (β : Rf ⋙ PN ⟶ PM ⋙ Rf') (hβ : β = mateEquiv adjf adjf' c) (E : DX) :
    σN.app (Rf.obj E) ≫ χ.app E = β.app E ≫ Rf'.map (σM.app E) := by
  subst hχ hβ
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_obj, Functor.id_obj, Functor.comp_map,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_inv_app, Category.id_comp, Category.comp_id,
    Category.assoc]
  rw [← adjf'.unit_naturality_assoc]
  simp only [← Functor.map_comp]
  rw [reassoc_of% (h _), σM.naturality]

end Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

namespace NearbyCyclesModel

variable {X X' Y Y' : Scheme.{u}}

/-- The *specialization map* `σ : Lπ^* ⟶ Ψ_M` of a model `M` with a projection `p : 𝒳 ⟶ X` of its
total space such that `j ≫ p = ε`, where `π = i ≫ p : X' ⟶ X`: the restriction `Li^*` of the unit
`Lp^* ⟶ Rj_* Lj^* Lp^*` of `Lj^* ⊣ Rj_*`, through the composition isomorphisms
`Lπ^* ≅ Lp^* ⋙ Li^*` and `Lε^* ≅ Lp^* ⋙ Lj^*`. -/
noncomputable def specialization (M : NearbyCyclesModel X X') (p : M.total ⟶ X)
    (hp : M.j ≫ p = M.ε) {π : X' ⟶ X} (hπ : M.i ≫ p = π) :
    L((π)^*⟦Λ⟧) ⟶ M.nearbyCycles Λ :=
  (leftDerivedUpperStarCompOfEq Λ hπ).hom ≫
    Functor.whiskerLeft L((p)^*⟦Λ⟧)
      (Functor.whiskerRight (derivedUpperStarLowerStarAdjunction Λ M.j).unit L((M.i)^*⟦Λ⟧)) ≫
    Functor.whiskerRight
      (Functor.whiskerRight (leftDerivedUpperStarCompOfEq Λ hp).inv R((M.j)_*⟦Λ⟧))
      L((M.i)^*⟦Λ⟧)

lemma specialization_app (M : NearbyCyclesModel X X') (p : M.total ⟶ X) (hp : M.j ≫ p = M.ε)
    {π : X' ⟶ X} (hπ : M.i ≫ p = π)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (M.specialization Λ p hp hπ).app K =
      (leftDerivedUpperStarCompOfEq Λ hπ).hom.app K ≫
        L((M.i)^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ M.j).unit.app
          (L((p)^*⟦Λ⟧).obj K) ≫
          R((M.j)_*⟦Λ⟧).map ((leftDerivedUpperStarCompOfEq Λ hp).inv.app K)) := by
  simp [specialization]

variable {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}

namespace Hom

variable (φ : M.Hom N f f') {pM : M.total ⟶ X} {pN : N.total ⟶ Y} {πM : X' ⟶ X} {πN : Y' ⟶ Y}

/-- **Pullback compatibility of the specialization maps**: for a morphism of models `φ : M ⟶ N`
over `f` and `f'` compatible with projections `p_M`, `p_N`, the pullback exchange
`α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` carries `Lf'^* σ_N(K)` to `σ_M(Lf^* K)`, up to the pullback
comparison `Lf'^* Lπ_N^* ≅ Lπ_M^* Lf^*`. -/
lemma map_specialization_app_comp_pullbackExchange_app (hpM : M.j ≫ pM = M.ε)
    (hpN : N.j ≫ pN = N.ε) (hπM : M.i ≫ pM = πM) (hπN : N.i ≫ pN = πN)
    (hp : φ.total ≫ pN = pM ≫ f) (sq : CommSq πM f' f πN)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    L((f')^*⟦Λ⟧).map ((N.specialization Λ pN hpN hπN).app K) ≫ (φ.pullbackExchange Λ).app K =
      (pullbackSquareComparison Λ sq).hom.app K ≫
        (M.specialization Λ pM hpM hπM).app (L((f)^*⟦Λ⟧).obj K) := by
  have sqt : CommSq φ.total pM pN f := ⟨hp⟩
  exact map_specialization_comp_pullbackExchange_aux (derivedUpperStarLowerStarAdjunction Λ N.j)
    (derivedUpperStarLowerStarAdjunction Λ M.j) (pullbackSquareComparison Λ φ.commSq_i)
    (pullbackSquareComparison Λ φ.commSq_i.flip) (pullbackSquareComparison_flip Λ _)
    (pullbackSquareComparison Λ φ.commSq_j) (pullbackSquareComparison Λ φ.commSq_ε)
    (pullbackSquareComparison Λ φ.commSq_ε.flip) (pullbackSquareComparison_flip Λ _)
    ((pullbackSquareComparison Λ sq).app K) ((pullbackSquareComparison Λ sq.flip).app K)
    (by rw [pullbackSquareComparison_flip Λ sq]; rfl)
    ((leftDerivedUpperStarCompOfEq Λ hπN).app K).symm
    ((leftDerivedUpperStarCompOfEq Λ hπM).app (L((f)^*⟦Λ⟧).obj K)).symm
    ((pullbackSquareComparison Λ sqt).app K).symm
    ((leftDerivedUpperStarCompOfEq Λ hpN).app K).symm
    ((leftDerivedUpperStarCompOfEq Λ hpM).app (L((f)^*⟦Λ⟧).obj K)).symm
    (pullbackSquareComparison_hom_app_paste_of_eq Λ φ.commSq_i.flip sqt hπM hπN sq.flip K)
    (pullbackSquareComparison_hom_app_paste_of_eq Λ φ.commSq_j sqt hpM hpN φ.commSq_ε.flip K)
    (φ.pullbackExchange Λ) rfl _ (N.specialization_app Λ pN hpN hπN K) _
    (M.specialization_app Λ pM hpM hπM _)

/-- **Pushforward compatibility of the specialization maps**: for a morphism of models
`φ : M ⟶ N` over `f` and `f'` compatible with projections `p_M`, `p_N`, the pushforward exchange
`χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M` carries `σ_N(Rf_* E)` to `Rf'_* σ_M(E)`, up to the base change map
`Lπ_N^* Rf_* ⟶ Rf'_* Lπ_M^*`. -/
lemma specialization_app_comp_pushforwardExchange_app (hpM : M.j ≫ pM = M.ε)
    (hpN : N.j ≫ pN = N.ε) (hπM : M.i ≫ pM = πM) (hπN : N.i ≫ pN = πN)
    (hp : φ.total ≫ pN = pM ≫ f) (sq : CommSq πM f' f πN)
    (E : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (N.specialization Λ pN hpN hπN).app (R((f)_*⟦Λ⟧).obj E) ≫
        (φ.pushforwardExchange Λ).app E =
      (baseChangeMap Λ sq).app E ≫ R((f')_*⟦Λ⟧).map ((M.specialization Λ pM hpM hπM).app E) :=
  whiskerLeft_comp_mateEquiv_aux (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f') (N.specialization Λ pN hpN hπN)
    (M.specialization Λ pM hpM hπM) (pullbackSquareComparison Λ sq).hom
    (φ.pullbackExchange Λ)
    (φ.map_specialization_app_comp_pullbackExchange_app Λ hpM hpN hπM hπN hp sq)
    (φ.pushforwardExchange Λ) rfl (baseChangeMap Λ sq)
    (Adjunction.exchangeRight_eq_mateEquiv _ _ _) E

end Hom

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
