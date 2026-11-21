/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeIntegralRational
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeComponents
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeIntegral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangePadicAlgCl.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClLowerStarHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralToPadicAlgClUpperShriekCompatibility
public import WeilConjectures.TraceFormula.ExternalProductExtendScalars
public import WeilConjectures.TraceFormula.IntegersToPadicAlgClLowerStar
public import WeilConjectures.TraceFormula.IntegralCompactPullback

/-!

# The operators of Frobenius correspondences under `𝒪_E ⟶ ℚ̄_ℓ`

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`, and write
`T = ℚ̄_ℓ ⊗ᴸ_{𝒪_E} -` for the extension of scalars on bounded constructible complexes
(`ProEtale.CondensedRing.boundedConstructibleIntegersToPadicAlgCl`). This file shows that `T`
carries the operators of Frobenius correspondences with
`𝒪_E`-coefficients (`WeilConjectures.TraceFormula.IntegralCompactPullback`) to the same operators
with `ℚ̄_ℓ`-coefficients (`WeilConjectures.TraceFormula.CompactPullback`):

* `ProEtale.CondensedRing.integersToPadicAlgCl_map_compactPullback_app`: under the comparisons
  `T RΓ_c ≅ RΓ_c T` and `T Lh^* ≅ Lh^* T`, the extension of scalars of the pullback
  `h^♯ : RΓ_c(X, K) ⟶ RΓ_c(Y, Lh^* K)` on compactly supported cohomology along a proper `h` is
  `h^♯` at `T K`.

It is assembled from the compatibilities of the coefficient comparisons with the structure
maps entering `h^♯`:

* with the composition of pullbacks (`integersToPadicAlgCl_map_upperStarComp_hom_app`);
* with the unit of `Lh^* ⊣ Rh_*` (`integersToPadicAlgCl_map_unit_app`);
* with the identification `Rh_! ≅ Rh_*` for a proper `h`
  (`integersToPadicAlgCl_map_lowerShriekIsoLowerStar_inv_app`);
* with the composition of lower shrieks (`integersToPadicAlgCl_map_lowerShriekComp_hom_app`).

## Implementation details

The assembly is done once for abstract functors (`map_compactPullback_aux`,
`map_graphStalkMap_aux`, ...): rewriting directly with these identities in the categories
`Dᵇc(X)⟦Λ⟧` is slow, since unification unfolds the definitions of the functors involved.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

-- The coefficient ring `𝒪_E`.
set_option quotPrecheck false in
local notation "𝒪" => Profinite.padicIntegersRingObj ℓ E.1

-- The coefficient ring `ℚ̄_ℓ`.
set_option quotPrecheck false in
local notation "ℚ̄" => Profinite.padicAlgClRingObj ℓ

-- The extension of scalars `T_X = ℚ̄_ℓ ⊗ᴸ_{𝒪_E} -`.
set_option quotPrecheck false in
local notation "𝐓" => boundedConstructibleIntegersToPadicAlgCl ℓ E

/-! ### Abstract identities -/

section Abstract

variable {DX DY DP DX' DY' DP' : Type*} [Category* DX] [Category* DY] [Category* DP]
  [Category* DX'] [Category* DY'] [Category* DP']
  {TX : DX ⥤ DX'} {TY : DY ⥤ DY'} {TP : DP ⥤ DP'}
  {u : DX ⥤ DY} {u' : DX' ⥤ DY'} {s : DY ⥤ DX} {s' : DY' ⥤ DX'} {t : DY ⥤ DX}
  {t' : DY' ⥤ DX'} {cX : DX ⥤ DP} {cX' : DX' ⥤ DP'} {cY : DY ⥤ DP} {cY' : DY' ⥤ DP'}

/-- The extension of scalars of a pullback on compactly supported cohomology, for abstract
functors: if comparisons `T u ≅ u' T`, `T s ≅ s' T`, `T t ≅ t' T`, `T cX ≅ cX' T` and
`T cY ≅ cY' T` are compatible with the units of `u ⊣ s` and `u' ⊣ s'`, with identifications
`t ≅ s`, `t' ≅ s'` and with `t ⋙ cX ≅ cY`, `t' ⋙ cX' ≅ cY'`, then they are compatible with the
composites `cX ⟶ cX s u ≅ cX t u ≅ cY u`. -/
lemma map_compactPullback_aux (adj : u ⊣ s) (adj' : u' ⊣ s') (i : t ≅ s) (i' : t' ≅ s')
    (c : t ⋙ cX ≅ cY) (c' : t' ⋙ cX' ≅ cY')
    (σ : u ⋙ TY ≅ TX ⋙ u') (ls : s ⋙ TX ≅ TY ⋙ s') (lt : t ⋙ TX ≅ TY ⋙ t')
    (lX : cX ⋙ TP ≅ TX ⋙ cX') (lY : cY ⋙ TP ≅ TY ⋙ cY')
    (hU : ∀ K, TX.map (adj.unit.app K) ≫ ls.hom.app (u.obj K) ≫ s'.map (σ.hom.app K) =
      adj'.unit.app (TX.obj K))
    (hP : ∀ M, TX.map (i.inv.app M) ≫ lt.hom.app M = ls.hom.app M ≫ i'.inv.app (TY.obj M))
    (hC : ∀ M, TP.map (c.hom.app M) ≫ lY.hom.app M =
      lX.hom.app (t.obj M) ≫ cX'.map (lt.hom.app M) ≫ c'.hom.app (TY.obj M))
    (K : DX) :
    TP.map (cX.map (adj.unit.app K) ≫ cX.map (i.inv.app (u.obj K)) ≫ c.hom.app (u.obj K)) ≫
        lY.hom.app (u.obj K) ≫ cY'.map (σ.hom.app K) =
      lX.hom.app K ≫ cX'.map (adj'.unit.app (TX.obj K)) ≫
        cX'.map (i'.inv.app (u'.obj (TX.obj K))) ≫ c'.hom.app (u'.obj (TX.obj K)) := by
  have h₁ := lX.hom.naturality (adj.unit.app K)
  have h₂ := lX.hom.naturality (i.inv.app (u.obj K))
  have h₃ := c'.hom.naturality (σ.hom.app K)
  have h₄ := i'.inv.naturality (σ.hom.app K)
  have h₅ := hP (u.obj K)
  have h₆ := hU K
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at h₁ h₂ h₃ h₄ h₅ h₆
  have key : TX.map (adj.unit.app K) ≫ TX.map (i.inv.app (u.obj K)) ≫
      lt.hom.app (u.obj K) ≫ t'.map (σ.hom.app K) =
      adj'.unit.app (TX.obj K) ≫ i'.inv.app (u'.obj (TX.obj K)) := by
    rw [reassoc_of% h₅, ← h₄, reassoc_of% h₆]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (hC (u.obj K)), ← h₃, reassoc_of% h₂, reassoc_of% h₁]
  simp only [← Functor.map_comp_assoc, key]

/-- The extension of scalars of an operator `RΓ_c(v) ∘ h^♯`, for abstract functors. -/
lemma map_compactPullback_comp_aux {cX' : DX' ⥤ DP'} {h : DX ⥤ DX} {h' : DX' ⥤ DX'}
    (cp : cX ⟶ h ⋙ cX) (cp' : cX' ⟶ h' ⋙ cX') (σ : h ⋙ TX ≅ TX ⋙ h')
    (lX : cX ⋙ TP ≅ TX ⋙ cX') (K : DX)
    (hcp : TP.map (cp.app K) ≫ lX.hom.app (h.obj K) ≫ cX'.map (σ.hom.app K) =
      lX.hom.app K ≫ cp'.app (TX.obj K)) (v : h.obj K ⟶ K) :
    TP.map (cp.app K ≫ cX.map v) ≫ lX.hom.app K =
      lX.hom.app K ≫ cp'.app (TX.obj K) ≫ cX'.map (σ.inv.app K ≫ TX.map v) := by
  have h₁ := lX.hom.naturality v
  simp only [Functor.comp_map, Functor.comp_obj] at h₁
  rw [Functor.map_comp, Category.assoc, h₁, ← reassoc_of% hcp, ← Functor.map_comp,
    Iso.hom_inv_id_app_assoc]

/-- The extension of scalars of a stalk map `v_x`, for abstract functors. -/
lemma map_graphStalkMap_aux {xs xhs : DX ⥤ DP} {xs' xhs' : DX' ⥤ DP'} {h : DX ⥤ DX}
    {h' : DX' ⥤ DX'} (comp : xhs ≅ h ⋙ xs) (comp' : xhs' ≅ h' ⋙ xs')
    (σx : xs ⋙ TP ≅ TX ⋙ xs') (σh : h ⋙ TX ≅ TX ⋙ h') (σxh : xhs ⋙ TP ≅ TX ⋙ xhs') (K : DX)
    (e : xs.obj K ⟶ xhs.obj K) (e' : xs'.obj (TX.obj K) ⟶ xhs'.obj (TX.obj K))
    (hUS : TP.map (comp.hom.app K) ≫ σx.hom.app (h.obj K) ≫ xs'.map (σh.hom.app K) =
      σxh.hom.app K ≫ comp'.hom.app (TX.obj K))
    (hc : TP.map e ≫ σxh.hom.app K = σx.hom.app K ≫ e') (v : h.obj K ⟶ K) :
    TP.map (e ≫ comp.hom.app K ≫ xs.map v) ≫ σx.hom.app K =
      σx.hom.app K ≫ e' ≫ comp'.hom.app (TX.obj K) ≫ xs'.map (σh.inv.app K ≫ TX.map v) := by
  have h₁ := σx.hom.naturality v
  simp only [Functor.comp_map, Functor.comp_obj] at h₁
  have h₂ : TP.map (comp.hom.app K) ≫ σx.hom.app (h.obj K) =
      σxh.hom.app K ≫ comp'.hom.app (TX.obj K) ≫ xs'.map (σh.inv.app K) := by
    rw [← reassoc_of% hUS, ← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  simp only [Functor.map_comp, Category.assoc]
  rw [h₁, reassoc_of% h₂, reassoc_of% hc]

/-- The extension of scalars of a composite `Rh_! ⋙ Rc_! ≅ R(h ≫ c)_! = Rd_!`, for abstract
functors. -/
lemma map_lowerShriekCompToPoint_aux {DZ DZ' : Type*} [Category* DZ] [Category* DZ']
    {TZ : DZ ⥤ DZ'} {A : DY ⥤ DX} {A' : DY' ⥤ DX'} {B : DX ⥤ DZ} {B' : DX' ⥤ DZ'}
    {C D : DY ⥤ DZ} {C' D' : DY' ⥤ DZ'} (c : C ≅ A ⋙ B) (c' : C' ≅ A' ⋙ B') (p : C = D)
    (p' : C' = D') (lA : A ⋙ TX ≅ TY ⋙ A') (lB : B ⋙ TZ ≅ TX ⋙ B') (lC : C ⋙ TZ ≅ TY ⋙ C')
    (lD : D ⋙ TZ ≅ TY ⋙ D') (M : DY)
    (hcomp : TZ.map (c.hom.app M) ≫ lB.hom.app (A.obj M) ≫ B'.map (lA.hom.app M) =
      lC.hom.app M ≫ c'.hom.app (TY.obj M))
    (hcongr : TZ.map (eqToHom (by rw [p])) ≫ lD.hom.app M =
      lC.hom.app M ≫ eqToHom (by rw [p'])) :
    TZ.map ((c.symm ≪≫ eqToIso p).hom.app M) ≫ lD.hom.app M =
      lB.hom.app (A.obj M) ≫ B'.map (lA.hom.app M) ≫
        (c'.symm ≪≫ eqToIso p').hom.app (TY.obj M) := by
  subst p p'
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id] at hcongr
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id, hcongr]
  rw [← cancel_epi (TZ.map (c.hom.app M)), ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hcomp, Iso.hom_inv_id_app,
    Category.comp_id]

end Abstract


/-! ### The comparisons of the six operations along `𝒪_E ⟶ ℚ̄_ℓ` -/

section Comparisons

variable {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- The comparison `Lf^*_{𝒪_E} ⋙ T ≅ T ⋙ Lf^*_E` for the extension of scalars `𝒪_E ⟶ E`
commutes with the composition isomorphisms `L(x ≫ h)^* ≅ Lh^* ⋙ Lx^*`. -/
lemma extendScalars_map_upperStarComp_hom_app (x : Z ⟶ Y) (h : Y ⟶ X)
    (K : Dᵇc(X.left)⟦𝒪⟧) :
    (boundedConstructibleExtendScalars Z.left ℓ E).map
        ((boundedConstructibleUpperStarComp 𝒪 ℓ x h).hom.app K) ≫
        (boundedConstructibleUpperStarExtendScalarsIso ℓ E x).hom.app
          ((boundedConstructibleUpperStar 𝒪 ℓ h).obj K) ≫
        (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E.1) ℓ x).map
          ((boundedConstructibleUpperStarExtendScalarsIso ℓ E h).hom.app K) =
      (boundedConstructibleUpperStarExtendScalarsIso ℓ E (x ≫ h)).hom.app K ≫
        (boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj E.1) ℓ x h).hom.app
          ((boundedConstructibleExtendScalars X.left ℓ E).obj K) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleExtendScalars_map_hom,
    boundedConstructibleUpperStar_map_hom,
    boundedConstructibleUpperStarExtendScalarsIso_hom_app_hom,
    boundedConstructibleUpperStarComp_hom_app_hom]
  exact (derivedPullIsoCompCoherence _ x.left h.left K.obj).symm

/-- The comparison `Lf^*_E ⋙ T ≅ T ⋙ Lf^*_{ℚ̄_ℓ}` for the extension of scalars `E ⟶ ℚ̄_ℓ`
commutes with the composition isomorphisms `L(x ≫ h)^* ≅ Lh^* ⋙ Lx^*`. -/
lemma toPadicAlgCl_map_upperStarComp_hom_app (x : Z ⟶ Y) (h : Y ⟶ X)
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleToPadicAlgCl Z.left ℓ E).map
        ((boundedConstructibleUpperStarComp _ ℓ x h).hom.app K) ≫
        (boundedConstructibleUpperStarToPadicAlgClIso ℓ E x).hom.app
          ((boundedConstructibleUpperStar _ ℓ h).obj K) ≫
        (boundedConstructibleUpperStar ℚ̄ ℓ x).map
          ((boundedConstructibleUpperStarToPadicAlgClIso ℓ E h).hom.app K) =
      (boundedConstructibleUpperStarToPadicAlgClIso ℓ E (x ≫ h)).hom.app K ≫
        (boundedConstructibleUpperStarComp ℚ̄ ℓ x h).hom.app
          ((boundedConstructibleToPadicAlgCl X.left ℓ E).obj K) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleToPadicAlgCl_map_hom,
    boundedConstructibleUpperStar_map_hom, boundedConstructibleUpperStarToPadicAlgClIso_hom_app_hom,
    boundedConstructibleUpperStarComp_hom_app_hom]
  exact (derivedPullIsoCompCoherence _ x.left h.left K.obj).symm

/-- The components of the comparison `Lf^*_{𝒪_E} ⋙ T ≅ T ⋙ Lf^*_{ℚ̄_ℓ}`: the comparison for
`𝒪_E ⟶ E` followed by the one for `E ⟶ ℚ̄_ℓ`. -/
lemma boundedConstructibleUpperStarIntegersToPadicAlgClIso_hom_app (f : Y ⟶ X)
    (K : Dᵇc(X.left)⟦𝒪⟧) :
    (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E f).hom.app K =
      (boundedConstructibleToPadicAlgCl Y.left ℓ E).map
          ((boundedConstructibleUpperStarExtendScalarsIso ℓ E f).hom.app K) ≫
        (boundedConstructibleUpperStarToPadicAlgClIso ℓ E f).hom.app
          ((boundedConstructibleExtendScalars X.left ℓ E).obj K) := by
  simp [boundedConstructibleUpperStarIntegersToPadicAlgClIso, boundedConstructibleToPadicAlgCl]

/-- `integersToPadicAlgCl_map_upperStarComp_hom_app` with `T` written as the composite of the
extensions of scalars `𝒪_E ⟶ E` and `E ⟶ ℚ̄_ℓ`. -/
lemma toPadicAlgCl_extendScalars_map_upperStarComp_hom_app (x : Z ⟶ Y) (h : Y ⟶ X)
    (K : Dᵇc(X.left)⟦𝒪⟧) :
    (boundedConstructibleToPadicAlgCl Z.left ℓ E).map
        ((boundedConstructibleExtendScalars Z.left ℓ E).map
          ((boundedConstructibleUpperStarComp 𝒪 ℓ x h).hom.app K)) ≫
        (boundedConstructibleToPadicAlgCl Z.left ℓ E).map
          ((boundedConstructibleUpperStarExtendScalarsIso ℓ E x).hom.app
            ((boundedConstructibleUpperStar 𝒪 ℓ h).obj K)) ≫
        (boundedConstructibleUpperStarToPadicAlgClIso ℓ E x).hom.app
          ((boundedConstructibleExtendScalars Y.left ℓ E).obj
            ((boundedConstructibleUpperStar 𝒪 ℓ h).obj K)) ≫
        (boundedConstructibleUpperStar ℚ̄ ℓ x).map
          ((boundedConstructibleToPadicAlgCl Y.left ℓ E).map
              ((boundedConstructibleUpperStarExtendScalarsIso ℓ E h).hom.app K) ≫
            (boundedConstructibleUpperStarToPadicAlgClIso ℓ E h).hom.app
              ((boundedConstructibleExtendScalars X.left ℓ E).obj K)) =
      (boundedConstructibleToPadicAlgCl Z.left ℓ E).map
          ((boundedConstructibleUpperStarExtendScalarsIso ℓ E (x ≫ h)).hom.app K) ≫
        (boundedConstructibleUpperStarToPadicAlgClIso ℓ E (x ≫ h)).hom.app
          ((boundedConstructibleExtendScalars X.left ℓ E).obj K) ≫
        (boundedConstructibleUpperStarComp ℚ̄ ℓ x h).hom.app
          ((boundedConstructibleToPadicAlgCl X.left ℓ E).obj
            ((boundedConstructibleExtendScalars X.left ℓ E).obj K)) := by
  have e₃ := (boundedConstructibleUpperStarToPadicAlgClIso ℓ E x).hom.naturality
    ((boundedConstructibleUpperStarExtendScalarsIso ℓ E h).hom.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at e₃
  refine Eq.trans ?_ ((boundedConstructibleToPadicAlgCl Z.left ℓ E).map
    ((boundedConstructibleUpperStarExtendScalarsIso ℓ E (x ≫ h)).hom.app K) ≫=
      toPadicAlgCl_map_upperStarComp_hom_app ℓ E x h
        ((boundedConstructibleExtendScalars X.left ℓ E).obj K))
  refine Eq.trans ?_ ((boundedConstructibleToPadicAlgCl Z.left ℓ E).map_comp_assoc _ _ _)
  refine Eq.trans ?_ (congrArg (fun t ↦ (boundedConstructibleToPadicAlgCl Z.left ℓ E).map t ≫ _)
    (extendScalars_map_upperStarComp_hom_app ℓ E x h K))
  simp only [Functor.map_comp, Category.assoc]
  exact _ ≫= _ ≫= ((Category.assoc _ _ _).symm.trans
    ((e₃ =≫ _).trans (Category.assoc _ _ _))).symm

/-- **The pullback comparison commutes with composition** (on bounded constructible
complexes, for `𝒪_E ⟶ ℚ̄_ℓ`): for `x : Z ⟶ Y` and `h : Y ⟶ X`, the comparison `T L(x ≫ h)^* ≅ L(x ≫ h)^* T`
followed by `L(x ≫ h)^* ≅ Lx^* Lh^*` is `T` of the composition isomorphism followed by the
comparisons for `x` and `h`. -/
theorem integersToPadicAlgCl_map_upperStarComp_hom_app (x : Z ⟶ Y) (h : Y ⟶ X)
    (K : Dᵇc(X.left)⟦𝒪⟧) :
    (𝐓 Z).map ((boundedConstructibleUpperStarComp 𝒪 ℓ x h).hom.app K) ≫
        (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E x).hom.app
          ((boundedConstructibleUpperStar 𝒪 ℓ h).obj K) ≫
        (boundedConstructibleUpperStar ℚ̄ ℓ x).map
          ((boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E h).hom.app K) =
      (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E (x ≫ h)).hom.app K ≫
        (boundedConstructibleUpperStarComp ℚ̄ ℓ x h).hom.app ((𝐓 X).obj K) := by
  simp only [boundedConstructibleUpperStarIntegersToPadicAlgClIso_hom_app, Category.assoc]
  exact toPadicAlgCl_extendScalars_map_upperStarComp_hom_app ℓ E x h K

/-- In the square of adjunctions of `Adjunction.pullIsoOfComapIso`, the unit of `U₂ ⊣ L₂` at
`E₂ K` is the unit of `U₁ ⊣ L₁` followed by `pushHomOfComapIso` and the pullback comparison. -/
lemma _root_.CategoryTheory.Adjunction.map_unit_comp_pushHomOfComapIso_app
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    {E₁ : A ⥤ B} {Res₁ : B ⥤ A} (adj₁ : E₁ ⊣ Res₁) {E₂ : A' ⥤ B'} {Res₂ : B' ⥤ A'}
    (adj₂ : E₂ ⊣ Res₂) {U₁ : A' ⥤ A} {L₁ : A ⥤ A'} (adjR : U₁ ⊣ L₁) {U₂ : B' ⥤ B}
    {L₂ : B ⥤ B'} (adjS : U₂ ⊣ L₂) (e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁) (K : A') :
    E₂.map (adjR.unit.app K) ≫ (Adjunction.pushHomOfComapIso adj₁ adj₂ e).app (U₁.obj K) ≫
        L₂.map ((Adjunction.pullIsoOfComapIso adj₁ adj₂ adjR adjS e).hom.app K) =
      adjS.unit.app (E₂.obj K) := by
  rw [Adjunction.pushHomOfComapIso_eq_mateEquiv adj₁ adj₂ adjR adjS, ← Category.assoc,
    unit_mateEquiv]
  simp

/-- The unit compatibility for the coefficient change `𝒪_E ⟶ E`. -/
lemma extendScalars_map_unit_app (h : Y ⟶ X) (K : Dᵇc(X.left)⟦𝒪⟧) :
    (boundedConstructibleExtendScalars X.left ℓ E).map
        ((PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E.1
          h).unit.app K) ≫
        (boundedConstructibleLowerStarExtendScalarsIso ℓ E h).hom.app
          ((boundedConstructibleUpperStar 𝒪 ℓ h).obj K) ≫
        (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E h).map
          ((boundedConstructibleUpperStarExtendScalarsIso ℓ E h).hom.app K) =
      (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E h).unit.app
        ((boundedConstructibleExtendScalars X.left ℓ E).obj K) := by
  have h₂ : (boundedConstructibleLowerStarExtendScalarsIso ℓ E h).hom =
      mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E.1 h)
        (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E h)
        (boundedConstructibleUpperStarExtendScalarsIso ℓ E h).inv := rfl
  simp only [h₂, ← Category.assoc, unit_mateEquiv]
  simp

/-- On the ambient derived categories, the comparison
`boundedConstructibleLowerStarToPadicAlgClIsoOfQcqs`
is the derived (Push) morphism. -/
lemma boundedConstructibleLowerStarToPadicAlgClIsoOfQcqs_hom_app_hom (h : Y ⟶ X)
    (K : Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧) :
    ((boundedConstructibleLowerStarToPadicAlgClIsoOfQcqs ℓ E h).hom.app K).hom =
      (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) h.left).app K.obj := by
  simp only [Functor.comp_obj, boundedConstructibleToPadicAlgCl_obj_obj,
    ContinuousMapRingObj.boundedConstructibleLowerStar_obj_obj,
    boundedConstructibleLowerStar_obj_obj, boundedConstructibleLowerStarToPadicAlgClIsoOfQcqs,
    Functor.FullyFaithful.preimageIso_hom, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskeringRight_obj_obj, boundedConstructibleToPadicAlgClCompatibility,
    ObjectProperty.liftCompιIso, ContinuousMapRingObj.boundedConstructibleLowerStarCompatibility,
    boundedConstructibleLowerStarCompatibility, Iso.refl_hom, Iso.refl_inv,
    Functor.FullyFaithful.whiskeringRight_preimage_app, NatTrans.comp_app, ObjectProperty.ι_obj,
    Functor.associator_hom_app, Functor.whiskerLeft_app, NatTrans.id_app,
    ObjectProperty.lift_obj_obj, Functor.associator_inv_app, Functor.whiskerRight_app,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp, ObjectProperty.homMk_hom]

/-- The unit compatibility for the coefficient change `E ⟶ ℚ̄_ℓ`. -/
lemma toPadicAlgCl_map_unit_app (h : Y ⟶ X)
    (L : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E.1⟧) :
    (boundedConstructibleToPadicAlgCl X.left ℓ E).map
        ((ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
          h).unit.app L) ≫
        (boundedConstructibleLowerStarToPadicAlgClIsoOfQcqs ℓ E h).hom.app
          ((boundedConstructibleUpperStar _ ℓ h).obj L) ≫
        (boundedConstructibleLowerStar ℓ h).map
          ((boundedConstructibleUpperStarToPadicAlgClIso ℓ E h).hom.app L) =
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ h).unit.app
        ((boundedConstructibleToPadicAlgCl X.left ℓ E).obj L) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleToPadicAlgCl_map_hom,
    ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction_unit_app_hom',
    boundedConstructibleLowerStarToPadicAlgClIsoOfQcqs_hom_app_hom,
    boundedConstructibleLowerStar_map_hom, boundedConstructibleUpperStarToPadicAlgClIso_hom_app_hom,
    boundedConstructibleUpperStarLowerStarAdjunction_unit_app_hom',
    boundedConstructibleToPadicAlgCl_obj_obj, boundedConstructibleUpperStar_obj_obj]
  exact Adjunction.map_unit_comp_pushHomOfComapIso_app _ _ _ _ _ L.obj

/-- **Transport of the unit of `Lh^* ⊣ Rh_*`** (for `𝒪_E ⟶ ℚ̄_ℓ`): under the comparisons
`T Rh_* ≅ Rh_* T` and `T Lh^* ≅ Lh^* T`, the extension of scalars of the unit
`K ⟶ Rh_* Lh^* K` is the unit at `T K`. -/
theorem integersToPadicAlgCl_map_unit_app (h : Y ⟶ X) (K : Dᵇc(X.left)⟦𝒪⟧) :
    (𝐓 X).map ((PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E.1
          h).unit.app K) ≫
        (boundedConstructibleLowerStarIntegersToPadicAlgClIso ℓ E h).hom.app
          ((boundedConstructibleUpperStar 𝒪 ℓ h).obj K) ≫
        (boundedConstructibleLowerStar ℓ h).map
          ((boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E h).hom.app K) =
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ h).unit.app ((𝐓 X).obj K) := by
  have h₁ := congrArg (constructibleToPadicAlgCl X.left ℓ E).map
    (extendScalars_map_unit_app ℓ E h K)
  have h₂ :=
    toPadicAlgCl_map_unit_app ℓ E h ((boundedConstructibleExtendScalars X.left ℓ E).obj K)
  simp only [Functor.map_comp] at h₁
  simp only [boundedConstructibleLowerStarIntegersToPadicAlgClIso,
    boundedConstructibleUpperStarIntegersToPadicAlgClIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj, Functor.comp_map, Category.id_comp,
    Category.comp_id, Functor.map_comp, Category.assoc]
  have hn (Z : Dᵇc(X.left)⟦ℚ̄⟧) (g : _ ⟶ Z) :=
    (boundedConstructibleLowerStarToPadicAlgClIsoOfQcqs ℓ E h).hom.naturality_assoc
      ((boundedConstructibleUpperStarExtendScalarsIso ℓ E h).hom.app K) g
  simp only [Functor.comp_obj, Functor.comp_map, boundedConstructibleToPadicAlgCl_eq] at hn
  simp only [← hn, reassoc_of% h₁]
  exact h₂

/-- **`Rh_! ≅ Rh_*` commutes with the coefficient comparisons** for a proper `h`: the comparison `T Rh_! ≅ Rh_! T` corresponds to the comparison
`T Rh_* ≅ Rh_* T` under the identifications `Rh_! ≅ Rh_*` over `𝒪_E` and over `ℚ̄_ℓ`. -/
theorem integersToPadicAlgCl_map_lowerShriekIsoLowerStar_inv_app (h : Y ⟶ X) [IsProper h.left]
    (M : Dᵇc(Y.left)⟦𝒪⟧) :
    (𝐓 X).map ((boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E.1 h).inv.app M) ≫
        (boundedConstructibleLowerShriekIntegersToPadicAlgClIso ℓ E h).inv.app M =
      (boundedConstructibleLowerStarIntegersToPadicAlgClIso ℓ E h).hom.app M ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ h).inv.app ((𝐓 Y).obj M) := by
  sorry

/-- **The compactly supported comparison commutes with composition** (for `𝒪_E ⟶ ℚ̄_ℓ`): for `f : Y ⟶ X` and
`g : X ⟶ Z`, the comparison `T R(f ≫ g)_! ≅ R(f ≫ g)_! T` followed by the composition isomorphism
`R(f ≫ g)_! ≅ Rg_! Rf_!` is `T` of the composition isomorphism followed by the comparisons for `g`
and `f`. -/
theorem integersToPadicAlgCl_map_lowerShriekComp_hom_app (f : Y ⟶ X) (g : X ⟶ Z)
    (M : Dᵇc(Y.left)⟦𝒪⟧) :
    (𝐓 Z).map ((boundedConstructibleLowerShriekComp_padicIntegers ℓ E.1 f g).hom.app M) ≫
        (boundedConstructibleLowerShriekIntegersToPadicAlgClIso ℓ E g).inv.app
          ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 f).obj M) ≫
        (boundedConstructibleLowerShriek ℓ g).map
          ((boundedConstructibleLowerShriekIntegersToPadicAlgClIso ℓ E f).inv.app M) =
      (boundedConstructibleLowerShriekIntegersToPadicAlgClIso ℓ E (f ≫ g)).inv.app M ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app ((𝐓 Y).obj M) := by
  sorry

/-- The comparison `Rf_! ⋙ T_X ≅ T_Y ⋙ Rf_!` of the compactly supported direct images along
`𝒪_E ⟶ ℚ̄_ℓ` (`boundedConstructibleLowerShriekIntegersToPadicAlgClIso`), with the extension of scalars written as
`T = boundedConstructibleIntegersToPadicAlgCl`. -/
noncomputable def lowerShriekIntegersToPadicAlgClIso (f : Y ⟶ X) :
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 f ⋙ 𝐓 X ≅
      𝐓 Y ⋙ boundedConstructibleLowerShriek ℓ f :=
  (boundedConstructibleLowerShriekIntegersToPadicAlgClIso ℓ E f).symm

/-- The compactly supported comparisons along equal morphisms agree up to the casts. -/
lemma lowerShriekIntegersToPadicAlgClIso_hom_app_congr {a b : Y ⟶ X} (e : a = b)
    (M : Dᵇc(Y.left)⟦𝒪⟧) :
    (𝐓 X).map (eqToHom (by rw [e])) ≫ (lowerShriekIntegersToPadicAlgClIso ℓ E b).hom.app M =
      (lowerShriekIntegersToPadicAlgClIso ℓ E a).hom.app M ≫ eqToHom (by rw [e]) := by
  subst e
  simp

/-- `integersToPadicAlgCl_map_lowerShriekIsoLowerStar_inv_app`, for
`lowerShriekIntegersToPadicAlgClIso`. -/
lemma map_lowerShriekIsoLowerStar_inv_app_comp_lowerShriekIntegersToPadicAlgClIso_hom_app
    (h : Y ⟶ X) [IsProper h.left] (M : Dᵇc(Y.left)⟦𝒪⟧) :
    (𝐓 X).map ((boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E.1 h).inv.app M) ≫
        (lowerShriekIntegersToPadicAlgClIso ℓ E h).hom.app M =
      (boundedConstructibleLowerStarIntegersToPadicAlgClIso ℓ E h).hom.app M ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ h).inv.app ((𝐓 Y).obj M) :=
  integersToPadicAlgCl_map_lowerShriekIsoLowerStar_inv_app ℓ E h M

/-- `integersToPadicAlgCl_map_lowerShriekComp_hom_app`, for
`lowerShriekIntegersToPadicAlgClIso`. -/
lemma map_lowerShriekComp_hom_app_comp_lowerShriekIntegersToPadicAlgClIso_hom_app (f : Y ⟶ X)
    (g : X ⟶ Z) (M : Dᵇc(Y.left)⟦𝒪⟧) :
    (𝐓 Z).map ((boundedConstructibleLowerShriekComp_padicIntegers ℓ E.1 f g).hom.app M) ≫
        (lowerShriekIntegersToPadicAlgClIso ℓ E g).hom.app
          ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 f).obj M) ≫
        (boundedConstructibleLowerShriek ℓ g).map
          ((lowerShriekIntegersToPadicAlgClIso ℓ E f).hom.app M) =
      (lowerShriekIntegersToPadicAlgClIso ℓ E (f ≫ g)).hom.app M ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app ((𝐓 Y).obj M) :=
  integersToPadicAlgCl_map_lowerShriekComp_hom_app ℓ E f g M

/-- **The compactly supported comparison commutes with the composition isomorphisms
`Rh_! ⋙ Ra_{X!} ≅ Ra_{Y!}` to the point**, by
`integersToPadicAlgCl_map_lowerShriekComp_hom_app`. -/
theorem integersToPadicAlgCl_map_lowerShriekCompToPoint_hom_app (h : Y ⟶ X)
    (M : Dᵇc(Y.left)⟦𝒪⟧) :
    (𝐓 (point k)).map
          ((PadicIntegersRingObj.boundedConstructibleLowerShriekCompToPoint ℓ E.1 h).hom.app M) ≫
        (lowerShriekIntegersToPadicAlgClIso ℓ E (toPoint Y)).hom.app M =
      (lowerShriekIntegersToPadicAlgClIso ℓ E (toPoint X)).hom.app
          ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 h).obj M) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((lowerShriekIntegersToPadicAlgClIso ℓ E h).hom.app M) ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ h).hom.app ((𝐓 Y).obj M) := by
  unfold PadicIntegersRingObj.boundedConstructibleLowerShriekCompToPoint
    boundedConstructibleLowerShriekCompToPoint
  exact map_lowerShriekCompToPoint_aux _ _ _ _ (lowerShriekIntegersToPadicAlgClIso ℓ E h)
    (lowerShriekIntegersToPadicAlgClIso ℓ E (toPoint X))
    (lowerShriekIntegersToPadicAlgClIso ℓ E (h ≫ toPoint X))
    (lowerShriekIntegersToPadicAlgClIso ℓ E (toPoint Y)) M
    (map_lowerShriekComp_hom_app_comp_lowerShriekIntegersToPadicAlgClIso_hom_app ℓ E h
      (toPoint X) M)
    (lowerShriekIntegersToPadicAlgClIso_hom_app_congr ℓ E (comp_toPoint h) M)

/-- **The pullback on compactly supported cohomology commutes with the extension of scalars**:
for a proper `h : Y ⟶ X`, under the comparisons `T RΓ_c ≅ RΓ_c T` and `T Lh^* ≅ Lh^* T`, the
extension of scalars of `h^♯ : RΓ_c(X, K) ⟶ RΓ_c(Y, Lh^* K)` is `h^♯` at `T K`. It is assembled
from the compatibilities of the comparisons with the unit of `Lh^* ⊣ Rh_*`, with `Rh_! ≅ Rh_*` and
with the composition of lower shrieks. -/
theorem integersToPadicAlgCl_map_compactPullback_app (h : Y ⟶ X) [IsProper h.left]
    (K : Dᵇc(X.left)⟦𝒪⟧) :
    (𝐓 (point k)).map ((PadicIntegersRingObj.compactPullback ℓ E.1 h).app K) ≫
        (lowerShriekIntegersToPadicAlgClIso ℓ E (toPoint Y)).hom.app
          ((boundedConstructibleUpperStar 𝒪 ℓ h).obj K) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
          ((boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E h).hom.app K) =
      (lowerShriekIntegersToPadicAlgClIso ℓ E (toPoint X)).hom.app K ≫
        (compactPullback ℓ h).app ((𝐓 X).obj K) := by
  simp only [PadicIntegersRingObj.compactPullback_app ℓ E.1 h K,
    compactPullback_app ℓ h ((𝐓 X).obj K)]
  refine map_compactPullback_aux
    (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E.1 h)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ h)
    (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E.1 h)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ h)
    (PadicIntegersRingObj.boundedConstructibleLowerShriekCompToPoint ℓ E.1 h)
    (boundedConstructibleLowerShriekCompToPoint ℓ h)
    (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E h)
    (boundedConstructibleLowerStarIntegersToPadicAlgClIso ℓ E h)
    (lowerShriekIntegersToPadicAlgClIso ℓ E h) (lowerShriekIntegersToPadicAlgClIso ℓ E (toPoint X))
    (lowerShriekIntegersToPadicAlgClIso ℓ E (toPoint Y))
    ?_ ?_ ?_ K
  · intro K
    exact integersToPadicAlgCl_map_unit_app ℓ E h K
  · intro M
    exact
      map_lowerShriekIsoLowerStar_inv_app_comp_lowerShriekIntegersToPadicAlgClIso_hom_app ℓ E h M
  · intro M
    set_option maxRecDepth 20000 in
    exact integersToPadicAlgCl_map_lowerShriekCompToPoint_hom_app ℓ E h M

/-- The comparisons `T Lx^* ≅ Lx^* T` along equal morphisms agree up to the casts. -/
lemma boundedConstructibleUpperStarIntegersToPadicAlgClIso_hom_app_congr {a b : Y ⟶ X}
    (e : a = b) (K : Dᵇc(X.left)⟦𝒪⟧) :
    (𝐓 Y).map (eqToHom (by rw [e])) ≫
        (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E a).hom.app K =
      (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E b).hom.app K ≫
        eqToHom (by rw [e]) := by
  subst e
  simp

end Comparisons

end AlgebraicGeometry.ProEtale.CondensedRing
