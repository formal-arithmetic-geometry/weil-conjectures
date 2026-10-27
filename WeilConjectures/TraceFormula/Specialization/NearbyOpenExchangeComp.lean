/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyOpenExchange

/-!

# The compact-support exchange along an open sub-model

For open immersions of models `φ : N ⟶ M` over `j` and `ψ : M ⟶ P` over `ι` and a proper `P`,
the compact-support exchange `ν_{jι}` of the compactification `N ⊆ P` is the composite of the
exchange `ν_j` and of the compact-support exchange `ν_ι` of `M ⊆ P`
(`ProEtale.CondensedRing.compactSupportExchangeOfCompactification_comp_app`). In particular,
along an open sub-model `N ⊆ M` the compact-support exchange of the restricted compactification
is the composite of `ν_j` and of that of `M`
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.compactSupportExchange_ofOpen_app`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Shape

variable {DC DC' DX DX' DP DP' Ds Ds' : Type*} [Category DC] [Category DC'] [Category DX]
  [Category DX'] [Category DP] [Category DP'] [Category Ds] [Category Ds']

/-- `compactSupportExchangeAux_lift_comp_app` on the ambient categories, with the two sides `z`
and `x` given separately. -/
lemma compactSupportExchangeAux_lift_comp_app_hom_eq {PC : ObjectProperty DC}
    {PC' : ObjectProperty DC'} {PX : ObjectProperty DX} {PX' : ObjectProperty DX'}
    {PP : ObjectProperty DP} {PP' : ObjectProperty DP'} {Ps : ObjectProperty Ds}
    {Ps' : ObjectProperty Ds'} {ΨC : DC ⥤ DC'} {ΨX : DX ⥤ DX'} {ΨP : DP ⥤ DP'}
    {Ψs : Ds ⥤ Ds'} {hSpC : ∀ X, PC' ((PC.ι ⋙ ΨC).obj X)} {hSpX : ∀ X, PX' ((PX.ι ⋙ ΨX).obj X)}
    {hT : ∀ X, Ps' ((Ps.ι ⋙ Ψs).obj X)} {DhN : DC ⥤ DP} {DhN' : DC' ⥤ DP'}
    {DhM : DX ⥤ DP} {DhM' : DX' ⥤ DP'} {Rp : DP ⥤ Ds} {Rp' : DP' ⥤ Ds'}
    {hON : ∀ X, PP ((PC.ι ⋙ DhN).obj X)} {hON' : ∀ X, PP' ((PC'.ι ⋙ DhN').obj X)}
    {hOM : ∀ X, PP ((PX.ι ⋙ DhM).obj X)} {hOM' : ∀ X, PP' ((PX'.ι ⋙ DhM').obj X)}
    {hR : ∀ X, Ps ((PP.ι ⋙ Rp).obj X)} {hR' : ∀ X, Ps' ((PP'.ι ⋙ Rp').obj X)}
    {LSfN : PC.FullSubcategory ⥤ Ps.FullSubcategory}
    {LSfN' : PC'.FullSubcategory ⥤ Ps'.FullSubcategory}
    {LSfM : PX.FullSubcategory ⥤ Ps.FullSubcategory}
    {LSfM' : PX'.FullSubcategory ⥤ Ps'.FullSubcategory}
    {i₁N : LSfN' ≅ PP'.lift (PC'.ι ⋙ DhN') hON' ⋙ Ps'.lift (PP'.ι ⋙ Rp') hR'}
    {i₂N : LSfN ≅ PP.lift (PC.ι ⋙ DhN) hON ⋙ Ps.lift (PP.ι ⋙ Rp) hR}
    {i₁M : LSfM' ≅ PP'.lift (PX'.ι ⋙ DhM') hOM' ⋙ Ps'.lift (PP'.ι ⋙ Rp') hR'}
    {i₂M : LSfM ≅ PP.lift (PX.ι ⋙ DhM) hOM ⋙ Ps.lift (PP.ι ⋙ Rp) hR}
    {νhN : ΨC ⋙ DhN' ⟶ DhN ⋙ ΨP} {νhM : ΨX ⋙ DhM' ⟶ DhM ⋙ ΨP}
    {χ : Rp ⋙ Ψs ⟶ ΨP ⋙ Rp'} {hχ : IsIsoOn PP.ι χ}
    {Dj : PC.FullSubcategory ⥤ PX.FullSubcategory}
    {Dj' : PC'.FullSubcategory ⥤ PX'.FullSubcategory}
    (νj : PC'.lift (PC.ι ⋙ ΨC) hSpC ⋙ Dj' ⟶ Dj ⋙ PX'.lift (PX.ι ⋙ ΨX) hSpX)
    (lsc : LSfN ≅ Dj ⋙ LSfM) (lsc' : LSfN' ≅ Dj' ⋙ LSfM') (M : PC.FullSubcategory)
    (e : DhN.obj M.obj ⟶ DhM.obj (Dj.obj M).obj)
    (e' : DhN'.obj (ΨC.obj M.obj) ⟶ DhM'.obj (Dj'.obj ((PC'.lift (PC.ι ⋙ ΨC) hSpC).obj M)).obj)
    (h₁ : νhN.app M.obj ≫ ΨP.map e = e' ≫ DhM'.map (νj.app M).hom ≫ νhM.app (Dj.obj M).obj)
    (h₂ : (i₁N.hom.app ((PC'.lift (PC.ι ⋙ ΨC) hSpC).obj M)).hom ≫ Rp'.map e' =
        (lsc'.hom.app ((PC'.lift (PC.ι ⋙ ΨC) hSpC).obj M)).hom ≫
          (i₁M.hom.app (Dj'.obj ((PC'.lift (PC.ι ⋙ ΨC) hSpC).obj M))).hom)
    (h₃ : (i₂N.inv.app M ≫ lsc.hom.app M).hom = Rp.map e ≫ (i₂M.inv.app (Dj.obj M)).hom)
    {z : Ψs.obj (LSfN.obj M).obj ⟶ Ψs.obj (LSfM.obj (Dj.obj M)).obj}
    (hz : Ψs.map (lsc.hom.app M).hom = z)
    {x : (LSfN'.obj ((PC'.lift (PC.ι ⋙ ΨC) hSpC).obj M)).obj ⟶
      Ψs.obj (LSfM.obj (Dj.obj M)).obj}
    (hx : (lsc'.hom.app ((PC'.lift (PC.ι ⋙ ΨC) hSpC).obj M)).hom ≫
        (LSfM'.map (νj.app M)).hom ≫
        ((compactSupportExchangeAux Ps'.fullyFaithfulι i₁M i₂M (PX'.liftCompιIso _ hSpX)
          (PP'.liftCompιIso _ hOM') (Ps'.liftCompιIso _ hR') (PP.liftCompιIso _ hOM)
          (Ps.liftCompιIso _ hR) (Ps'.liftCompιIso _ hT) νhM
          (invOnSubcategory PP.ι χ hχ)).app (Dj.obj M)).hom = x) :
    ((compactSupportExchangeAux Ps'.fullyFaithfulι i₁N i₂N (PC'.liftCompιIso _ hSpC)
        (PP'.liftCompιIso _ hON') (Ps'.liftCompιIso _ hR') (PP.liftCompιIso _ hON)
        (Ps.liftCompιIso _ hR) (Ps'.liftCompιIso _ hT) νhN
        (invOnSubcategory PP.ι χ hχ)).app M).hom ≫ z = x := by
  subst hz hx
  have key : (compactSupportExchangeAux Ps'.fullyFaithfulι i₁N i₂N (PC'.liftCompιIso _ hSpC)
      (PP'.liftCompιIso _ hON') (Ps'.liftCompιIso _ hR') (PP.liftCompιIso _ hON)
      (Ps.liftCompιIso _ hR) (Ps'.liftCompιIso _ hT) νhN (invOnSubcategory PP.ι χ hχ)).app M ≫
        (Ps'.lift (Ps.ι ⋙ Ψs) hT).map (lsc.hom.app M) =
      lsc'.hom.app ((PC'.lift (PC.ι ⋙ ΨC) hSpC).obj M) ≫ LSfM'.map (νj.app M) ≫
        (compactSupportExchangeAux Ps'.fullyFaithfulι i₁M i₂M (PX'.liftCompιIso _ hSpX)
          (PP'.liftCompιIso _ hOM') (Ps'.liftCompιIso _ hR') (PP.liftCompιIso _ hOM)
          (Ps.liftCompιIso _ hR) (Ps'.liftCompιIso _ hT) νhM
          (invOnSubcategory PP.ι χ hχ)).app (Dj.obj M) := by
    have : IsIso (χ.app (DhN.obj M.obj)) := hχ ((PP.lift (PC.ι ⋙ DhN) hON).obj M)
    have : IsIso (χ.app (DhM.obj (Dj.obj M).obj)) :=
      hχ ((PP.lift (PX.ι ⋙ DhM) hOM).obj (Dj.obj M))
    have hχe : (invOnSubcategory PP.ι χ hχ).app ((PP.lift (PC.ι ⋙ DhN) hON).obj M) ≫
        Ψs.map (Rp.map e) = Rp'.map (ΨP.map e) ≫
          (invOnSubcategory PP.ι χ hχ).app ((PP.lift (PX.ι ⋙ DhM) hOM).obj (Dj.obj M)) := by
      rw [← cancel_mono (χ.app (DhM.obj (Dj.obj M).obj)), Category.assoc, Category.assoc]
      erw [χ.naturality e, invOnSubcategory_app_comp_assoc, invOnSubcategory_app_comp]
      simp
    have hi : (LSfM'.map (νj.app M)).hom ≫ (i₁M.hom.app _).hom =
        (i₁M.hom.app _).hom ≫ Rp'.map (DhM'.map (νj.app M).hom) :=
      congr_arg InducedCategory.Hom.hom (i₁M.hom.naturality (νj.app M))
    apply Ps'.fullyFaithfulι.map_injective
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, compactSupportExchangeAux_app,
      compactSupportExchangeAux_app]
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj,
      ObjectProperty.ι_map, ObjectProperty.liftCompιIso_hom_app, CategoryTheory.Functor.map_id,
      ObjectProperty.liftCompιIso_inv_app, ObjectProperty.lift_map, Functor.comp_map,
      ObjectProperty.homMk_hom, Category.id_comp, Category.assoc]
    rw [← Ψs.map_comp, ← ObjectProperty.FullSubcategory.comp_hom, h₃, Ψs.map_comp,
      reassoc_of% hχe, ← Rp'.map_comp_assoc, h₁]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% h₂, ← reassoc_of% hi]
  have h := congrArg (fun f ↦ f.hom) key
  simpa only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.lift_map,
    ObjectProperty.homMk_hom, Functor.comp_map, ObjectProperty.ι_map] using h

/-- The composition law `lowerShriekExchangeOfInv_comp_app` followed by the image of a morphism
`u : Dj K ⟶ B` (and read through a right inverse `v` of the primed `u'`). -/
lemma lowerShriekExchangeOfInv_comp_app_comp_map {DC DC' DX DX' DP DP' : Type*} [Category DC]
    [Category DC'] [Category DX] [Category DX'] [Category DP] [Category DP']
    {ΨC : DC ⥤ DC'} {ΨX : DX ⥤ DX'} {ΨP : DP ⥤ DP'}
    {Dj : DC ⥤ DX} {Lj : DX ⥤ DC} {Dj' : DC' ⥤ DX'} {Lj' : DX' ⥤ DC'}
    {Dι : DX ⥤ DP} {Lι : DP ⥤ DX} {Dι' : DX' ⥤ DP'} {Lι' : DP' ⥤ DX'}
    {Djι : DC ⥤ DP} {Ljι : DP ⥤ DC} {Djι' : DC' ⥤ DP'} {Ljι' : DP' ⥤ DC'}
    (adjj : Dj ⊣ Lj) (adjj' : Dj' ⊣ Lj') (adjι : Dι ⊣ Lι) (adjι' : Dι' ⊣ Lι')
    (adjjι : Djι ⊣ Ljι) (adjjι' : Djι' ⊣ Ljι') (c : Ljι ≅ Lι ⋙ Lj) (c' : Ljι' ≅ Lι' ⋙ Lj')
    (αj : ΨX ⋙ Lj' ⟶ Lj ⋙ ΨC) [IsIso αj] (αι : ΨP ⋙ Lι' ⟶ Lι ⋙ ΨX) [IsIso αι]
    (αjι : ΨP ⋙ Ljι' ⟶ Ljι ⋙ ΨC) [IsIso αjι]
    (hα : ∀ A, αjι.app A ≫ ΨC.map (c.hom.app A) =
      c'.hom.app (ΨP.obj A) ≫ Lj'.map (αι.app A) ≫ αj.app (Lι.obj A))
    (K : DC) {B : DX} (u : Dj.obj K ⟶ B) {B' : DX'} (u' : Dj'.obj (ΨC.obj K) ⟶ B')
    (v : B' ⟶ Dj'.obj (ΨC.obj K)) (huv : u' ≫ v = 𝟙 _) :
    (lowerShriekExchangeOfInv adjjι adjjι' αjι).app K ≫
        ΨP.map ((((conjugateIsoEquiv adjjι (adjj.comp adjι)).symm c).symm).hom.app K ≫
          Dι.map u) =
      ((((conjugateIsoEquiv adjjι' (adjj'.comp adjι')).symm c').symm).hom.app (ΨC.obj K) ≫
          Dι'.map u') ≫
        Dι'.map (v ≫ (lowerShriekExchangeOfInv adjj adjj' αj).app K ≫ ΨX.map u) ≫
          (lowerShriekExchangeOfInv adjι adjι' αι).app B := by
  have n := (lowerShriekExchangeOfInv adjι adjι' αι).naturality u
  simp only [Functor.comp_obj, Functor.comp_map] at n
  rw [Functor.map_comp, reassoc_of% (lowerShriekExchangeOfInv_comp_app adjj adjj' adjι adjι' adjjι
    adjjι' c c' αj αι αjι hα K), ← n]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc Dι' u' v, huv, CategoryTheory.Functor.map_id, Category.id_comp]

end Shape

section General

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Algebra k k']
  {Y X Z : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {Y' X' Z' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  [IsProper (toPoint Z).left] [IsProper (toPoint Z').left]
  {j : Y ⟶ X} {ι : X ⟶ Z} [IsOpenImmersion j.left] [IsOpenImmersion ι.left]
  [IsOpenImmersion (j ≫ ι).left] {j' : Y' ⟶ X'} {ι' : X' ⟶ Z'} [IsOpenImmersion j'.left]
  [IsOpenImmersion ι'.left] [IsOpenImmersion (j' ≫ ι').left]
  {N : NearbyCyclesModel Y.left Y'.left} {M : NearbyCyclesModel X.left X'.left}
  {P : NearbyCyclesModel Z.left Z'.left}
  (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hS : (traitModel k k').PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))

set_option maxHeartbeats 6000000 in
-- the identities are matched against the unfolded exchanges by `cast_proofs`
/-- **The compact-support exchange of a composite of open immersions of models**: for
`φ : N ⟶ M` over open immersions `j`, `j'` and `ψ : M ⟶ P` over open immersions `ι`, `ι'` with
`P` proper, the compact-support exchange of `N ⊆ P` (along `φ ≫ ψ`) followed by
`Ra_! ≅ Rj_! ⋙ Ra_{X!}` is `Ra'_! ≅ Rj'_! ⋙ Ra'_{X!}` followed by `Ra'_{X!}(ν_j)` and the
compact-support exchange of `M ⊆ P` at `Rj_!`. -/
theorem compactSupportExchangeOfCompactification_comp_app (φ : N.Hom M j.left j'.left)
    (ψ : M.Hom P ι.left ι'.left) [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    [IsIso (ψ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    [IsIso ((φ.comp ψ).pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    (a₁ : P.Hom (traitModel k k') (toPoint Z).left (toPoint Z').left)
    (ha₁ : IsIsoOn (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      Z.left)).ι (a₁.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)))
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactSupportExchangeOfCompactification ℓ hN hS (comp_toPoint (j ≫ ι))
        (comp_toPoint (j' ≫ ι')) (φ.comp ψ) a₁ ha₁).app K ≫
        (NearbyCyclesModel.boundedConstructibleNearbyCycles hS).map
          ((lowerShriekCompOfEq ℓ j (toPoint X) (comp_toPoint j)).hom.app K) =
      (lowerShriekCompOfEq ℓ j' (toPoint X') (comp_toPoint j')).hom.app
          ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj K) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X')).map
          ((φ.boundedConstructibleLowerShriekExchange ℓ hN hM).app K) ≫
        (compactSupportExchangeOfCompactification ℓ hM hS (comp_toPoint ι) (comp_toPoint ι') ψ a₁
          ha₁).app ((boundedConstructibleLowerShriek ℓ j).obj K) := by
  ext1
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, compactSupportExchangeOfCompactification_eq_lift,
    compactSupportExchangeOfCompactification_eq_lift]
  apply compactSupportExchangeAux_lift_comp_app_hom_eq
    (φ.boundedConstructibleLowerShriekExchange ℓ hN hM)
    (lowerShriekCompOfEq ℓ j (toPoint X) (comp_toPoint j))
    (lowerShriekCompOfEq ℓ j' (toPoint X') (comp_toPoint j')) K
    (((boundedConstructibleOpenImmersionLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ j
      ι).hom.app K).hom ≫
      ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ ι).map
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app
          K)).hom)
    (((boundedConstructibleOpenImmersionLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ j'
      ι').hom.app (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙
          N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)) fun K ↦ hN K.obj K.property).obj K)).hom ≫
      ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ ι').map
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j').inv.app
          (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙
            N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)) fun K ↦ hN K.obj K.property).obj
              K))).hom)
    (i₁M := compactificationLowerShriekIso ℓ ι' (toPoint Z') (comp_toPoint ι'))
    (i₂M := compactificationLowerShriekIso ℓ ι (toPoint Z) (comp_toPoint ι))
    (νhM := lowerShriekExchangeOfInv (openImmersionAdjunction ℓ ι.left)
      (openImmersionAdjunction ℓ ι'.left) (ψ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)))
  case h₁ =>
    have hνj : ((φ.boundedConstructibleLowerShriekExchange ℓ hN hM).app K).hom =
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j').hom.app
          ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj K)).hom ≫
        (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ j.left)
          (openImmersionAdjunction ℓ j'.left)
          (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))).app K.obj ≫
        (M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map
          ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app
            K).hom := by
      rw [NearbyCyclesModel.Hom.boundedConstructibleLowerShriekExchange, NatTrans.comp_app,
        NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
        ObjectProperty.FullSubcategory.comp_hom, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, NearbyCyclesModel.Hom.boundedConstructibleOpenExchange_app_hom]
      rfl
    rw [hνj, boundedConstructibleOpenImmersionLowerShriekComp_hom_app_hom,
      boundedConstructibleOpenImmersionLowerShriekComp_hom_app_hom,
      boundedConstructibleOpenImmersionLowerShriek_map_hom,
      boundedConstructibleOpenImmersionLowerShriek_map_hom]
    cast_proofs lowerShriekExchangeOfInv_comp_app_comp_map (openImmersionAdjunction ℓ j.left)
      (openImmersionAdjunction ℓ j'.left) (openImmersionAdjunction ℓ ι.left)
      (openImmersionAdjunction ℓ ι'.left) (openImmersionAdjunction ℓ (j ≫ ι).left)
      (openImmersionAdjunction ℓ (j' ≫ ι').left)
      (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) j.left ι.left)
      (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) j'.left ι'.left)
      (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))
      (ψ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))
      ((φ.comp ψ).pullbackExchange (Profinite.padicAlgClRingObj ℓ))
      (fun A ↦ φ.pullbackExchange_comp_app (Profinite.padicAlgClRingObj ℓ) ψ A) K.obj
      ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app K).hom
      ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j').inv.app
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj K)).hom
      ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j').hom.app
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj K)).hom
      (by rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id_app]; rfl)
  case h₂ =>
    have h := congrArg (fun f ↦ f.hom)
      (compactificationLowerShriekIso_hom_app_comp_map_openImmersionLowerShriekComp ℓ j' ι'
        (toPoint Z') (comp_toPoint ι') (comp_toPoint j') (comp_toPoint (j' ≫ ι'))
        (((boundedConstructible _).lift ((boundedConstructible _).ι ⋙
          N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)) fun K ↦ hN K.obj K.property).obj K))
    simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleLowerStar_map_hom] at h
    cast_proofs h
  case h₃ =>
    have h := compactificationLowerShriekIso_hom_app_comp_map_openImmersionLowerShriekComp ℓ j ι
      (toPoint Z) (comp_toPoint ι) (comp_toPoint j) (comp_toPoint (j ≫ ι)) K
    have h' : (compactificationLowerShriekIso ℓ (j ≫ ι) (toPoint Z) (comp_toPoint (j ≫ ι))).inv.app
          K ≫ (lowerShriekCompOfEq ℓ j (toPoint X) (comp_toPoint j)).hom.app K =
        (boundedConstructibleLowerStar ℓ (toPoint Z)).map
          ((boundedConstructibleOpenImmersionLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ j
            ι).hom.app K ≫
          (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ ι).map
            ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app
              K)) ≫
          (compactificationLowerShriekIso ℓ ι (toPoint Z) (comp_toPoint ι)).inv.app
            ((boundedConstructibleLowerShriek ℓ j).obj K) := by
      rw [← cancel_epi ((compactificationLowerShriekIso ℓ (j ≫ ι) (toPoint Z)
        (comp_toPoint (j ≫ ι))).hom.app K), Iso.hom_inv_id_app_assoc, reassoc_of% h,
        Iso.hom_inv_id_app, Category.comp_id]
    have h'' := congrArg (fun f ↦ f.hom) h'
    simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleLowerStar_map_hom]
      at h''
    cast_proofs h''
  case hz => rfl
  case hx =>
    cast_proofs Eq.refl
      (((lowerShriekCompOfEq ℓ j' (toPoint X') (comp_toPoint j')).hom.app
          ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj K)).hom ≫
        ((boundedConstructibleLowerShriek ℓ (toPoint X')).map
          ((φ.boundedConstructibleLowerShriekExchange ℓ hN hM).app K)).hom ≫
        ((compactSupportExchangeOfCompactification ℓ hM hS (comp_toPoint ι) (comp_toPoint ι') ψ
          a₁ ha₁).app ((boundedConstructibleLowerShriek ℓ j).obj K)).hom)

end General

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfBase

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Algebra k k']
  {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom]
  [QuasiCompact Y'.hom] [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left}
  {q : N.total ⟶ trait k'} {g : N.generic ⟶ Spec (.of (traitGenericField k'))}
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {hM : M.IsTraitModelOfBase k qM gM}


/-- **The compact-support exchanges along an open sub-model** (blueprint
`det-nearby-exchange-maps`, `det-nearby-exceptional-tensor` (3)): for an open sub-model `N ⊆ M`
over open immersions `j`, `j'` and a compactification `M ⊆ P`, the compact-support exchange of
the restricted compactification `N ⊆ P` is the composite of the exchange `ν_j` (adjoint to
`α_j⁻¹`) and of the compact-support exchange of `M ⊆ P`, through the composition isomorphisms
`Ra_N! ≅ Rj_! ⋙ Ra_M!` and `Ra'_N! ≅ Rj'_! ⋙ Ra'_M!`.

Mathematically: `ν_{jι} = ι'_!(ν_j) ∘ ν_ι(j_!)` through the conjugates `(j ≫ ι)_! ≅ j_! ⋙ ι_!` of
the composition isomorphisms of the pullbacks
(`ProEtale.CondensedRing.lowerShriekExchangeOfInv_comp_app`
with `NearbyCyclesModel.Hom.pullbackExchange_comp_app_of_eq`); these conjugates are the composition
isomorphisms of the lower shrieks under `Rf_! ≅ f_!`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl_hom_app_of_isOpenImmersion`,
`compactificationLowerShriekIso_hom_app_comp_map_openImmersionLowerShriekComp`
);
the shapes `χ_P⁻¹ ∘ Rp'_*(ν)` then compose
(`ProEtale.CondensedRing.compactSupportExchangeAux_lift_comp_app_hom_eq`), see
`ProEtale.CondensedRing.compactSupportExchangeOfCompactification_comp_app`. -/
theorem Compactification.compactSupportExchange_ofOpen_app (C : hM.Compactification)
    (hN : N.IsTraitModelOfBase k q g) (j : Y ⟶ X) [IsOpenImmersion j.left] (j' : Y' ⟶ X')
    [IsOpenImmersion j'.left] (φ : N.Hom M j.left j'.left) [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic N.j M.j φ.total) (hq : q = φ.total ≫ qM)
    (hg : g = φ.generic ≫ gM)
    [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((C.ofOpen hN j j' φ hφ hq hg).compactSupportExchange ℓ).app K ≫
        (traitSpecialization k k' (ℓ := ℓ)).map
          ((lowerShriekCompOfEq ℓ j (toPoint X) (comp_toPoint j)).hom.app K) =
      (lowerShriekCompOfEq ℓ j' (toPoint X') (comp_toPoint j')).hom.app
          ((boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible ℓ)).obj K) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X')).map
          ((φ.boundedConstructibleLowerShriekExchange ℓ (hN.preservesBoundedConstructible ℓ)
            (hM.preservesBoundedConstructible ℓ)).app K) ≫
        (C.compactSupportExchange ℓ).app ((boundedConstructibleLowerShriek ℓ j).obj K) := by
  have : IsOpenImmersion (j ≫ C.ι).left := (C.ofOpen hN j j' φ hφ hq hg).isOpenImmersion_ι
  have : IsOpenImmersion (j' ≫ C.ι').left := (C.ofOpen hN j j' φ hφ hq hg).isOpenImmersion_ι'
  have : IsIso ((φ.comp C.hom).pullbackExchange (Profinite.padicAlgClRingObj ℓ)) :=
    inferInstanceAs (IsIso ((C.ofOpen hN j j' φ hφ hq hg).hom.pullbackExchange _))
  rw [compactSupportExchange_ofOpen, Compactification.compactSupportExchange]
  delta traitSpecialization
  cast_proofs compactSupportExchangeOfCompactification_comp_app ℓ
    (hN.preservesBoundedConstructible ℓ) (hM.preservesBoundedConstructible ℓ)
    (preservesBoundedConstructible_traitModel ℓ) φ C.hom C.isTraitModelOfBase.toTrait
    (C.isIsoOn_pushforwardExchange ℓ) K

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfBase
