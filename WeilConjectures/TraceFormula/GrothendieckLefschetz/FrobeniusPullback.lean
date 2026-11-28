/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.AdicFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.FrobeniusCorrespondenceOperator
public import WeilConjectures.TraceFormula.CompactPullback
import WeilConjectures.AlgebraicGeometry.ForgetSupportsComposition
import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeIsoMate
import WeilConjectures.TraceFormula.GrothendieckLefschetz.FrobeniusPullbackTriv

/-!
# Pullbacks on compactly supported cohomology along proper morphisms over the base

Let `Λ` be a finite coefficient ring and `s` a scheme. For a proper morphism `u : X ⟶ Y` and
morphisms `a' : Y ⟶ s`, `a : X ⟶ s` with `u ≫ a' = a`, the *pullback along `u`*
```
u^♯ : Ra'_! ⟶ Ra'_! Ru_* Lu^* ≅ Ra'_! Ru_! Lu^* ≅ R(u ≫ a')_! Lu^* = Ra_! Lu^*
```
is built from the unit of `Lu^* ⊣ Ru_*`, the identification `Ru_! ≅ Ru_*` and the composition
isomorphism of the lower shriek (`AlgebraicGeometry.Etale.lowerShriekPullbackOfComp`). For
`X = Y` and `a = a'` it is the pullback `AlgebraicGeometry.Etale.lowerShriekPullback` defining the
operators of Frobenius correspondences. The pullbacks are transitive
(`AlgebraicGeometry.Etale.lowerShriekPullbackOfComp_comp_app`).

For an endomorphism `u` of `X` over an automorphism `w` of the base (`u ≫ a = a ≫ w`), `u` is a
morphism over `s` from `a ≫ w` to `a`, and the derived global sections of `R(a ≫ w)_!` are
mapped to those of `Ra_!` by the composition isomorphism, `Rw_! ≅ Rw_*`, the transport of
derived global sections along `w` and the counit of `Lw^* ⊣ Rw_*`
(`AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsTransport`). Two instances of this
construction are compared with other descriptions:

* for an automorphism `g` of `X` over an automorphism `h` of `s` (a cartesian square), the
  pullback along `g` is the compact-support base change
  `AlgebraicGeometry.Etale.compactPullback`
  (`AlgebraicGeometry.Etale.compactPullback_eq_whiskerRight_lowerShriekPullbackOfComp`);
* for an inverse `w` of the absolute Frobenius `F_s`, the map is the pullback along the absolute
  Frobenius `F_X`, followed by the trivialization `L(F_X)^* ≅ 𝟭`
  (`compactlySupportedGlobalSectionsTransport_eq_lowerShriekPullbackOfComp`).

## Main definitions

- `AlgebraicGeometry.Etale.lowerShriekPullbackOfComp`: the pullback `u^♯ : Ra'_! ⟶ Lu^* ⋙ Ra_!`.
- `AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsTransport`: the map
  `RΓ(s, R(a ≫ w)_! -) ⟶ RΓ(s, Ra_! -)` for an automorphism `w` of `s`.

## Main results

- `AlgebraicGeometry.Etale.lowerShriekPullbackOfComp_comp_app`: transitivity of the pullbacks.
- `AlgebraicGeometry.Etale.compactPullback_eq_whiskerRight_lowerShriekPullbackOfComp`: the
  pullback along an automorphism over an automorphism of the base is the compact-support base
  change.
- `AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsTransport_eq_lowerShriekPullbackOfComp`:
  the absolute Frobenius acts trivially on compactly supported cohomology.
- `AlgebraicGeometry.Etale.correspondenceOperator_comp_eq_globalOperator`: the operator of the
  Frobenius correspondence along `F_X ≫ g` is the global operator of `g`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {s : Scheme.{u}}

/-- The composition law of pullbacks of the shape of
`AlgebraicGeometry.Etale.lowerShriekPullbackOfComp`, for an abstract family of functors: if each
of `Ph`, `Pg`, `Pgh` is built from the unit of an adjunction `L ⊣ R`, an isomorphism `S ≅ R` and
isomorphisms `V ≅ S ⋙ A`, `V ≅ A'`, then the pullback `Pgh` along the composite is `Ph` followed
by `Pg` and the composition isomorphism `uc`. -/
lemma pullbackOfComp_comp_aux {DX DY DZ S : Type*} [Category DX] [Category DY] [Category DZ]
    [Category S] {Lh : DX ⥤ DY} {Lg : DY ⥤ DZ} {Lgh : DX ⥤ DZ} {Rh : DY ⥤ DX} {Rg : DZ ⥤ DY}
    {Rgh : DZ ⥤ DX} {Sh : DY ⥤ DX} {Sg : DZ ⥤ DY} {Sgh : DZ ⥤ DX} {AX : DX ⥤ S} {AY : DY ⥤ S}
    {AZ : DZ ⥤ S} {Vh : DY ⥤ S} {Vg : DZ ⥤ S} {Vgh : DZ ⥤ S} (adjh : Lh ⊣ Rh) (adjg : Lg ⊣ Rg)
    (adjgh : Lgh ⊣ Rgh) (ih : Sh ≅ Rh) (ig : Sg ≅ Rg) (igh : Sgh ≅ Rgh) (uc : Lgh ≅ Lh ⋙ Lg)
    (lc : Rg ⋙ Rh ≅ Rgh) (sc : Sgh ≅ Sg ⋙ Sh) (ch : Vh ≅ Sh ⋙ AX) (eh : Vh ≅ AY)
    (cg : Vg ≅ Sg ⋙ AY) (eg : Vg ≅ AZ) (cgh : Vgh ≅ Sgh ⋙ AX) (egh : Vgh ≅ AZ)
    (Ph : AX ⟶ Lh ⋙ AY) (Pg : AY ⟶ Lg ⋙ AZ) (Pgh : AX ⟶ Lgh ⋙ AZ)
    (hPh : Ph = (Functor.leftUnitor _).inv ≫ Functor.whiskerRight adjh.unit _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (Functor.whiskerRight ih.inv _ ≫ ch.inv ≫ eh.hom))
    (hPg : Pg = (Functor.leftUnitor _).inv ≫ Functor.whiskerRight adjg.unit _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (Functor.whiskerRight ig.inv _ ≫ cg.inv ≫ eg.hom))
    (hPgh : Pgh = (Functor.leftUnitor _).inv ≫ Functor.whiskerRight adjgh.unit _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (Functor.whiskerRight igh.inv _ ≫ cgh.inv ≫ egh.hom))
    (hU : ∀ K, adjgh.unit.app K ≫ lc.inv.app (Lgh.obj K) =
      adjh.unit.app K ≫ Rh.map (adjg.unit.app (Lh.obj K)) ≫ Rh.map (Rg.map (uc.inv.app K)))
    (hL : ∀ P, sc.hom.app P ≫ ih.hom.app (Sg.obj P) ≫ Rh.map (ig.hom.app P) =
      igh.hom.app P ≫ lc.inv.app P)
    (hA : ∀ P, egh.inv.app P ≫ cgh.hom.app P ≫ AX.map (sc.hom.app P) =
      eg.inv.app P ≫ cg.hom.app P ≫ eh.inv.app (Sg.obj P) ≫ ch.hom.app (Sg.obj P))
    (K : DX) :
    Pgh.app K = Ph.app K ≫ Pg.app (Lh.obj K) ≫ AZ.map (uc.inv.app K) := by
  subst hPh hPg hPgh
  have hA' (P : DZ) : (cgh.symm ≪≫ egh).inv.app P ≫ AX.map (sc.hom.app P) =
      (cg.symm ≪≫ eg).inv.app P ≫ (ch.symm ≪≫ eh).inv.app (Sg.obj P) := by
    simpa only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc] using hA P
  have h := ProEtale.CondensedRing.compactPullback_comp_aux adjh adjg adjgh ih ig igh uc lc sc
    (ch.symm ≪≫ eh) (cg.symm ≪≫ eg) (cgh.symm ≪≫ egh) hU hL hA' K
  simpa only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp, Iso.trans_hom,
    Iso.symm_hom, Category.assoc] using h

/-- The components of a pullback of the shape of
`AlgebraicGeometry.Etale.lowerShriekPullbackOfComp`, for an abstract family of functors. -/
lemma pullbackOfComp_app {DX DY S : Type*} [Category DX] [Category DY] [Category S]
    {Lu : DY ⥤ DX} {Ru Su : DX ⥤ DY} {A : DY ⥤ S} {A' V : DX ⥤ S} (P : A ⟶ Lu ⋙ A')
    (adj : Lu ⊣ Ru) (ι : Su ≅ Ru) (c : V ≅ Su ⋙ A) (e : V ≅ A')
    (hP : P = (Functor.leftUnitor _).inv ≫ Functor.whiskerRight adj.unit A ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft Lu (Functor.whiskerRight ι.inv A ≫ c.inv ≫ e.hom)) (K : DY) :
    P.app K = A.map (adj.unit.app K) ≫ A.map (ι.inv.app (Lu.obj K)) ≫ c.inv.app (Lu.obj K) ≫
      e.hom.app (Lu.obj K) := by
  subst hP
  simp

section Pullback

variable {X Y : Scheme.{u}} {a : X ⟶ s} {a' : Y ⟶ s} [QuasiCompact a] [HasCompactification a]
  [QuasiCompact a'] [HasCompactification a']

/-- The *pullback on compactly supported cohomology* `u^♯ : Ra'_! ⟶ Lu^* ⋙ Ra_!` along a proper
morphism `u : X ⟶ Y` with `u ≫ a' = a`: the composite
```
Ra'_! K ⟶ Ra'_! Ru_* Lu^* K ≅ Ra'_! Ru_! Lu^* K ≅ R(u ≫ a')_! Lu^* K = Ra_! Lu^* K
```
of the unit of `Lu^* ⊣ Ru_*`, the identification `Ru_! ≅ Ru_*` and the composition isomorphism
of the lower shriek. -/
noncomputable def lowerShriekPullbackOfComp (u : X ⟶ Y) [IsProper u] (h : u ≫ a' = a) :
    R(a')_![ModuleCat.{u + 1} Λ] ⟶
      L((u)^*[ModuleCat.{u + 1} Λ]) ⋙ R(a)_![ModuleCat.{u + 1} Λ] :=
  have : HasCompactification (u ≫ a') := by rw [h]; infer_instance
  have : QuasiCompact (u ≫ a') := by rw [h]; infer_instance
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) u).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (Functor.whiskerRight (rightDerivedLowerShriekIsoRightDerivedLowerStar _ u).inv _ ≫
        (rightDerivedLowerShriekCompIso Λ u a').inv ≫ (rightDerivedLowerShriekCongrIso Λ h).hom)

/-- For an endomorphism over `s`, the pullback `AlgebraicGeometry.Etale.lowerShriekPullbackOfComp`
is `AlgebraicGeometry.Etale.lowerShriekPullback`. -/
lemma lowerShriekPullbackOfComp_eq_lowerShriekPullback (u : X ⟶ X) [IsProper u] (h : u ≫ a = a) :
    lowerShriekPullbackOfComp Λ u h = lowerShriekPullback Λ u h :=
  rfl

/-- **Transitivity of the pullbacks**: for proper `u₁ : X ⟶ Y`, `u₂ : Y ⟶ Z` over `s`, the pullback
along `u₁₂ = u₁ ≫ u₂` is the pullback along `u₂` followed by the pullback along `u₁` and the
composition isomorphism `Lu₂^* ⋙ Lu₁^* ≅ Lu₁₂^*`. -/
theorem lowerShriekPullbackOfComp_comp_app {Z : Scheme.{u}} {a'' : Z ⟶ s} [QuasiCompact a'']
    [HasCompactification a''] (u₁ : X ⟶ Y) (u₂ : Y ⟶ Z) (u₁₂ : X ⟶ Z) [IsProper u₁]
    [IsProper u₂] [IsProper u₁₂] (hu : u₁₂ = u₁ ≫ u₂) (h₁ : u₁ ≫ a' = a) (h₂ : u₂ ≫ a'' = a')
    (h₁₂ : u₁₂ ≫ a'' = a)
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (lowerShriekPullbackOfComp Λ u₁₂ h₁₂).app K =
      (lowerShriekPullbackOfComp Λ u₂ h₂).app K ≫
        (lowerShriekPullbackOfComp Λ u₁ h₁).app (L((u₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
          (R(a)_![ModuleCat.{u + 1} Λ]).map
            ((leftDerivedUpperStarComp _ u₁ u₂ u₁₂ hu).inv.app K) := by
  subst hu
  have : HasCompactification (u₁ ≫ a') := h₁ ▸ inferInstance
  have : QuasiCompact (u₁ ≫ a') := h₁ ▸ inferInstance
  have : HasCompactification (u₂ ≫ a'') := h₂ ▸ inferInstance
  have : QuasiCompact (u₂ ≫ a'') := h₂ ▸ inferInstance
  have : HasCompactification ((u₁ ≫ u₂) ≫ a'') := h₁₂ ▸ inferInstance
  have : QuasiCompact ((u₁ ≫ u₂) ≫ a'') := h₁₂ ▸ inferInstance
  refine pullbackOfComp_comp_aux (Lh := L((u₂)^*[ModuleCat.{u + 1} Λ]))
    (Lg := L((u₁)^*[ModuleCat.{u + 1} Λ])) (Lgh := L((u₁ ≫ u₂)^*[ModuleCat.{u + 1} Λ]))
    (AX := R(a'')_![ModuleCat.{u + 1} Λ]) (AY := R(a')_![ModuleCat.{u + 1} Λ])
    (AZ := R(a)_![ModuleCat.{u + 1} Λ])
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) u₂)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) u₁)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (u₁ ≫ u₂))
    (rightDerivedLowerShriekIsoRightDerivedLowerStar _ u₂)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar _ u₁)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar _ (u₁ ≫ u₂))
    (leftDerivedUpperStarComp _ u₁ u₂ (u₁ ≫ u₂) rfl)
    (rightDerivedLowerStarCompIsoOfComp _ u₁ u₂ (u₁ ≫ u₂) rfl)
    (rightDerivedLowerShriekCompIso Λ u₁ u₂)
    (rightDerivedLowerShriekCompIso Λ u₂ a'') (rightDerivedLowerShriekCongrIso Λ h₂)
    (rightDerivedLowerShriekCompIso Λ u₁ a') (rightDerivedLowerShriekCongrIso Λ h₁)
    (rightDerivedLowerShriekCompIso Λ (u₁ ≫ u₂) a'') (rightDerivedLowerShriekCongrIso Λ h₁₂)
    (lowerShriekPullbackOfComp Λ u₂ h₂) (lowerShriekPullbackOfComp Λ u₁ h₁)
    (lowerShriekPullbackOfComp Λ (u₁ ≫ u₂) h₁₂) rfl rfl rfl ?hU ?hL ?hA K
  case hU =>
    intro K
    have hU := unit_conjugateEquiv
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (u₁ ≫ u₂))
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) u₂).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) u₁))
      (leftDerivedUpperStarComp _ u₁ u₂ (u₁ ≫ u₂) rfl).inv K
    rw [Adjunction.comp_unit_app, Category.assoc] at hU
    exact hU
  case hL => exact rightDerivedLowerShriekCompIso_hom_app_comp_isoRightDerivedLowerStar Λ u₁ u₂
  case hA => exact rightDerivedLowerShriekCompIso_congr_assoc_app Λ u₁ u₂ h₁ h₂ h₁₂

end Pullback

/-- For an adjunction `L ⊣ R` of endofunctors and a natural transformation `T : Γ ⟶ L ⋙ Γ`,
the composite `R ⋙ Γ ⟶ R ⋙ L ⋙ Γ ⟶ Γ` of `T` and the counit. -/
noncomputable def transportCounit {C E : Type*} [Category C] [Category E] {L R : C ⥤ C}
    (adj : L ⊣ R) (Γ : C ⥤ E) (T : Γ ⟶ L ⋙ Γ) : R ⋙ Γ ⟶ Γ :=
  Functor.whiskerLeft R T ≫ (Functor.associator R L Γ).inv ≫
    Functor.whiskerRight adj.counit Γ ≫ (Functor.leftUnitor Γ).hom

lemma transportCounit_app {C E : Type*} [Category C] [Category E] {L R : C ⥤ C}
    (adj : L ⊣ R) (Γ : C ⥤ E) (T : Γ ⟶ L ⋙ Γ) (B : C) :
    (transportCounit adj Γ T).app B = T.app (R.obj B) ≫ Γ.map (adj.counit.app B) := by
  simp [transportCounit]

/-- The transport along an endofunctor with a unit: for `L ⊣ R` and `T : Γ ⟶ L ⋙ Γ`,
`Γ(η_A ≫ R e) ≫ T_{RB} ≫ Γ(ε_B) = T_A ≫ Γ(e)`. -/
lemma map_unit_comp_transportCounit_app {C E : Type*} [Category C] [Category E] {L R : C ⥤ C}
    (adj : L ⊣ R) (Γ : C ⥤ E) (T : Γ ⟶ L ⋙ Γ) {A B : C} (e : L.obj A ⟶ B) :
    Γ.map (adj.unit.app A ≫ R.map e) ≫ (transportCounit adj Γ T).app B = T.app A ≫ Γ.map e := by
  rw [transportCounit_app, T.naturality_assoc]
  congr 1
  rw [Functor.comp_map, ← Γ.map_comp]
  congr 1
  simp

/-- The abstract form of
`AlgebraicGeometry.Etale.compactPullback_eq_whiskerRight_lowerShriekPullbackOfComp`: if the
adjunct of `Ex : Ra ⋙ Lh ⟶ Lg ⋙ Ra` under `Lh ⊣ Rp` is `pb` followed by `c : Rah ⟶ Ra ⋙ Rs`
and `ι : Rs ⟶ Rp`, then the transport `T` followed by `Γ(Ex)` is `Γ(pb)` followed by `Γ(c ≫ ι)`,
`T` and `Γ` of the counit. -/
lemma whiskerLeft_comp_whiskerRight_eq_whiskerRight_comp_whiskerLeft {DX Ds E : Type*}
    [Category DX]
    [Category Ds] [Category E] {Ra Rah : DX ⥤ Ds} {Lg : DX ⥤ DX} {Lh Rs Rp : Ds ⥤ Ds}
    (adj : Lh ⊣ Rp) (Γ : Ds ⥤ E) (T : Γ ⟶ Lh ⋙ Γ) (c : Rah ⟶ Ra ⋙ Rs) (ι : Rs ⟶ Rp)
    (Ex : Ra ⋙ Lh ⟶ Lg ⋙ Ra) (pb : Ra ⟶ Lg ⋙ Rah)
    (hF : ∀ K, adj.unit.app (Ra.obj K) ≫ Rp.map (Ex.app K) =
      pb.app K ≫ c.app (Lg.obj K) ≫ ι.app (Ra.obj (Lg.obj K))) :
    Functor.whiskerLeft Ra T ≫ (Functor.associator _ _ _).inv ≫ Functor.whiskerRight Ex Γ ≫
        (Functor.associator _ _ _).hom =
      Functor.whiskerRight pb Γ ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft Lg (Functor.whiskerRight (c ≫ Functor.whiskerLeft Ra ι) Γ ≫
          (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Ra (transportCounit adj Γ T)) := by
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.id_comp, Category.comp_id,
    ← Γ.map_comp_assoc]
  rw [← hF]
  exact (map_unit_comp_transportCounit_app _ _ _ _).symm

/-- The abstract form of
`AlgebraicGeometry.Etale.correspondenceOperator_comp_eq_globalOperator`. -/
lemma map_app_comp_map_eq_app_comp_map {DX Ds E : Type*} [Category DX] [Category Ds]
    [Category E] {Ra Rah : DX ⥤ Ds} {Lg LF LΦ : DX ⥤ DX} (Γ : Ds ⥤ E) (pbg : Ra ⟶ Lg ⋙ Rah)
    (pbF : Rah ⟶ LF ⋙ Ra) (pbΦ : Ra ⟶ LΦ ⋙ Ra) (τ : LF ⟶ 𝟭 DX) (e : LΦ ≅ Lg ⋙ LF)
    (Q : Rah ⋙ Γ ⟶ Ra ⋙ Γ) (CP : Ra ⋙ Γ ⟶ Lg ⋙ Ra ⋙ Γ)
    (hΦ : ∀ K, pbΦ.app K = pbg.app K ≫ pbF.app (Lg.obj K) ≫ Ra.map (e.inv.app K))
    (hQ : Q =
      Functor.whiskerRight (pbF ≫ Functor.whiskerRight τ Ra ≫ (Functor.leftUnitor Ra).hom) Γ)
    (hCP : CP = Functor.whiskerRight pbg Γ ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft Lg Q) {K : DX} (v : Lg.obj K ⟶ K) :
    Γ.map (pbΦ.app K ≫ Ra.map (e.hom.app K ≫ τ.app (Lg.obj K) ≫ v)) =
      CP.app K ≫ (Ra ⋙ Γ).map v := by
  subst hQ hCP
  simp [hΦ]

/-- The components of the pullback of the shape of
`AlgebraicGeometry.Etale.lowerShriekPullbackOfComp` along a morphism whose pullback is
trivialized by `τ : Lu ≅ 𝟭`: followed by `A(τ)`, it is `B` of the inverse of the induced
trivialization `Su ≅ Ru ≅ 𝟭`, followed by `c⁻¹` and `e`. -/
lemma pullbackOfComp_app_comp_map_eq {DX S : Type*} [Category DX] [Category S]
    {Lu Ru Su : DX ⥤ DX} {A B V : DX ⥤ S} (P : B ⟶ Lu ⋙ A) (adj : Lu ⊣ Ru) (ι : Su ≅ Ru)
    (c : V ≅ Su ⋙ B) (e : V ≅ A) (τ : Lu ≅ 𝟭 DX)
    (hP : P = (Functor.leftUnitor _).inv ≫ Functor.whiskerRight adj.unit B ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft Lu (Functor.whiskerRight ι.inv B ≫ c.inv ≫ e.hom)) (K : DX) :
    P.app K ≫ A.map (τ.hom.app K) =
      B.map ((ι ≪≫ adj.rightAdjointUniq (Adjunction.id.ofNatIsoLeft τ.symm)).inv.app K) ≫
        c.inv.app K ≫ e.hom.app K := by
  subst hP
  have hu := Adjunction.unit_rightAdjointUniq_hom_app adj (Adjunction.id.ofNatIsoLeft τ.symm) K
  have hn := (adj.rightAdjointUniq (Adjunction.id.ofNatIsoLeft τ.symm)).inv.naturality
    (τ.hom.app K)
  simp only [Functor.id_map] at hn
  have hu' : adj.unit.app K = τ.inv.app K ≫
      (adj.rightAdjointUniq (Adjunction.id.ofNatIsoLeft τ.symm)).inv.app (Lu.obj K) := by
    rw [← cancel_mono ((adj.rightAdjointUniq (Adjunction.id.ofNatIsoLeft τ.symm)).hom.app
      (Lu.obj K)), Category.assoc, Iso.inv_hom_id_app, hu]
    simp [Adjunction.ofNatIsoLeft]
  have key : adj.unit.app K ≫ Ru.map (τ.hom.app K) =
      (adj.rightAdjointUniq (Adjunction.id.ofNatIsoLeft τ.symm)).inv.app K := by
    rw [hu', Category.assoc, ← hn, Iso.inv_hom_id_app_assoc]
    rfl
  simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp, Iso.trans_inv,
    Category.assoc]
  rw [← e.hom.naturality, ← c.inv.naturality_assoc, Functor.comp_map, ← B.map_comp_assoc,
    ← B.map_comp_assoc, Category.assoc, ← ι.inv.naturality, reassoc_of% key, B.map_comp_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-- The abstract form of the computation of the map
`AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsTransport` for an inverse of the absolute
Frobenius of the base. -/
lemma eq_whiskerRight_of_transport {DX Ds E : Type*} [Category DX] [Category Ds] [Category E]
    {Ra Rah : DX ⥤ Ds} {LF : DX ⥤ DX} {Lw Rs Rp LF' L1 : Ds ⥤ Ds} (adj : Lw ⊣ Rp) (Γ : Ds ⥤ E)
    (T : Γ ⟶ Lw ⋙ Γ) (triv : LF' ≅ L1) (ε : L1 ≅ 𝟭 Ds) (κ : L1 ≅ LF' ⋙ Lw)
    (hT : ∀ N, T.app (LF'.obj N) ≫ Γ.map (κ.inv.app N) = Γ.map (triv.hom.app N))
    (c : Rah ⟶ Ra ⋙ Rs) (ι : Rs ⟶ Rp) (pb : Rah ⟶ LF ⋙ Ra) (τ : LF ⟶ 𝟭 DX)
    (hμ : ∀ M, c.app M ≫ ι.app (Ra.obj M) ≫ ε.inv.app (Rp.obj (Ra.obj M)) ≫
      κ.hom.app (Rp.obj (Ra.obj M)) ≫ Lw.map ((triv ≪≫ ε).hom.app (Rp.obj (Ra.obj M))) ≫
      adj.counit.app (Ra.obj M) = pb.app M ≫ Ra.map (τ.app M))
    (Q : Rah ⋙ Γ ⟶ Ra ⋙ Γ)
    (hQ : Q = Functor.whiskerRight (c ≫ Functor.whiskerLeft Ra ι) Γ ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Ra (transportCounit adj Γ T)) :
    Q = Functor.whiskerRight (pb ≫ Functor.whiskerRight τ Ra ≫ (Functor.leftUnitor Ra).hom) Γ := by
  have hT' (N : Ds) : T.app N = Γ.map (ε.inv.app N ≫ κ.hom.app N ≫
      Lw.map ((triv ≪≫ ε).hom.app N)) := by
    have hn := T.naturality ((triv ≪≫ ε).hom.app N)
    simp only [Functor.comp_map, Functor.id_obj] at hn
    have h₀ : T.app (LF'.obj N) = Γ.map (triv.hom.app N) ≫ Γ.map (κ.hom.app N) := by
      rw [← hT, Category.assoc, ← Γ.map_comp, Iso.inv_hom_id_app]
      exact (Category.comp_id _).symm.trans (congrArg _ (Γ.map_id _).symm)
    rw [← cancel_epi (Γ.map ((triv ≪≫ ε).hom.app N)), hn, h₀, Iso.trans_hom, NatTrans.comp_app]
    simp only [Category.assoc, ← Γ.map_comp, Iso.hom_inv_id_app_assoc]
  subst hQ
  ext M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id,
    transportCounit_app, hT', ← Γ.map_comp, Category.assoc]
  erw [Category.comp_id]
  exact congrArg Γ.map (hμ M)

/-- The final step of the computation of `AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsTransport`
for an inverse of the absolute Frobenius of the base, in a category. -/
lemma comp_eq_of_frobenius {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ : C}
    (cw : O₁ ⟶ O₂) (r : O₂ ⟶ O₃) (pbτ : O₁ ⟶ O₃) (ρX : O₄ ≅ O₁) (cFb : O₅ ≅ O₄) (ch : O₅ ≅ O₃)
    (ce : O₅ ≅ O₆) (cbs : O₆ ≅ O₇) (ρs : O₇ ≅ O₁) (Fcw : O₇ ⟶ O₈) (ρs' : O₈ ≅ O₂)
    (c₁₂ : O₆ ≅ O₃) (φ : O₉ ≅ O₃) (c₂ : O₁₀ ≅ O₉) (cws : O₁₀ ≅ O₈)
    (hA : pbτ = ρX.inv ≫ cFb.inv ≫ ch.hom)
    (hFr : cFb.hom ≫ ρX.hom = ce.hom ≫ cbs.hom ≫ ρs.hom)
    (hnat : ρs.hom ≫ cw = Fcw ≫ ρs'.hom)
    (hassoc : c₁₂.inv ≫ cbs.hom ≫ Fcw = φ.inv ≫ c₂.inv ≫ cws.hom)
    (hcore : c₂.inv ≫ cws.hom ≫ ρs'.hom ≫ r = φ.hom)
    (hcc : ce.hom ≫ c₁₂.hom = ch.hom) :
    cw ≫ r = pbτ := by
  have hFr' : ρX.inv ≫ cFb.inv = ρs.inv ≫ cbs.inv ≫ ce.inv := by
    have e : cFb ≪≫ ρX = ce ≪≫ cbs ≪≫ ρs := Iso.ext (by simpa using hFr)
    simpa using congrArg Iso.inv e
  rw [hA, reassoc_of% hFr', ← hcc, Iso.inv_hom_id_assoc, ← cancel_epi ρs.hom, Iso.hom_inv_id_assoc,
    ← cancel_epi cbs.hom, Iso.hom_inv_id_assoc, reassoc_of% hnat]
  have hassoc' : cbs.hom ≫ Fcw = c₁₂.hom ≫ φ.inv ≫ c₂.inv ≫ cws.hom := by
    rw [← hassoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hassoc', hcore, Iso.inv_hom_id, Category.comp_id]

section Base

variable {X : Scheme.{u}} (a : X ⟶ s) [QuasiCompact a] [HasCompactification a]

/-- For an automorphism `w` of `s`, the map `RΓ(s, R(a ≫ w)_! -) ⟶ RΓ(s, Ra_! -)`:
```
RΓ(s, R(a ≫ w)_! M) ≅ RΓ(s, Rw_! Ra_! M) ≅ RΓ(s, Rw_* Ra_! M) ≅ RΓ(s, Lw^* Rw_* Ra_! M)
  ⟶ RΓ(s, Ra_! M)
```
the composition isomorphism of the lower shriek, the identification `Rw_! ≅ Rw_*`, the transport
of derived global sections along `w` (`AlgebraicGeometry.Etale.globalSectionsTransport`) and the
counit of `Lw^* ⊣ Rw_*`. -/
noncomputable def compactlySupportedGlobalSectionsTransport (w : s ⟶ s) [IsIso w]
    [HasCompactification (a ≫ w)] [QuasiCompact (a ≫ w)] :
    compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) (a ≫ w) ⟶
      compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a :=
  Functor.whiskerRight ((rightDerivedLowerShriekCompIso Λ a w).hom ≫
      Functor.whiskerLeft R(a)_![ModuleCat.{u + 1} Λ]
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) w).hom)
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft R(a)_![ModuleCat.{u + 1} Λ]
      (transportCounit (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) w)
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s) (globalSectionsTransport Λ w).hom)

/-- **The pullback along an automorphism over an automorphism of the base is the compact-support
base change**: for a cartesian square `g ≫ a = a ≫ h` of automorphisms `g` of `X` and `h` of
`s`, the pullback along `g`, a morphism over `s` from `a ≫ h` to `a`, followed by the map
`RΓ(s, R(a ≫ h)_! -) ⟶ RΓ(s, Ra_! -)`
(`AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsTransport`), is the compact-support
base change `AlgebraicGeometry.Etale.compactPullback`. -/
theorem compactPullback_eq_whiskerRight_lowerShriekPullbackOfComp {g : X ⟶ X} {h : s ⟶ s}
    [IsIso g] [IsIso h] (sq : IsPullback g a a h) [HasCompactification (a ≫ h)]
    [QuasiCompact (a ≫ h)] :
    compactPullback Λ sq =
      Functor.whiskerRight (lowerShriekPullbackOfComp Λ g sq.w)
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L((g)^*[ModuleCat.{u + 1} Λ])
          (compactlySupportedGlobalSectionsTransport Λ a h) := by
  have : HasCompactification (g ≫ a) := HasCompactification.of_eq sq.w.symm
  have : QuasiCompact (g ≫ a) := by rw [sq.w]; infer_instance
  have hpb (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      (lowerShriekPullbackOfComp Λ g sq.w).app K =
      (R(a)_![ModuleCat.{u + 1} Λ]).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app K) ≫
        (R(a)_![ModuleCat.{u + 1} Λ]).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) g).inv.app
            ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
        (rightDerivedLowerShriekCompIso Λ g a).inv.app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
        (rightDerivedLowerShriekCongrIso Λ sq.w).hom.app
          ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) :=
    pullbackOfComp_app (lowerShriekPullbackOfComp Λ g sq.w)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) g)
      (rightDerivedLowerShriekCompIso Λ g a) (rightDerivedLowerShriekCongrIso Λ sq.w) rfl K
  have hF (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app
          ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) ≫
        (R((h)_*[ModuleCat.{u + 1} Λ])).map ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K) =
      (lowerShriekPullbackOfComp Λ g sq.w).app K ≫
        (rightDerivedLowerShriekCompIso Λ a h).hom.app ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) h).hom.app
          ((R(a)_![ModuleCat.{u + 1} Λ]).obj ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
    rw [hpb K, unit_app_comp_map_rightDerivedLowerShriekBaseChangeMap_app Λ sq K]
    simp only [Category.assoc]
  exact whiskerLeft_comp_whiskerRight_eq_whiskerRight_comp_whiskerLeft
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h)
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s) (globalSectionsTransport Λ h).hom
    (rightDerivedLowerShriekCompIso Λ a h).hom
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) h).hom
    (rightDerivedLowerShriekBaseChangeMap Λ sq) (lowerShriekPullbackOfComp Λ g sq.w) hF

/-- **The absolute Frobenius acts trivially on compactly supported cohomology**: let `X` and `s`
be schemes of characteristic `p` with absolute `p ^ n`-power Frobenius `F_X` and `F_s`, and let
`w` be an inverse of `F_s`, so that `F_X` is a morphism over `s` from `a` to `a ≫ w`. The
map `RΓ(s, R(a ≫ w)_! -) ⟶ RΓ(s, Ra_! -)`
(`AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsTransport`) is the pullback along
`F_X` followed by the trivialization `L(F_X)^* ≅ L(𝟙 X)^* ≅ 𝟭`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso`). -/
theorem compactlySupportedGlobalSectionsTransport_eq_lowerShriekPullbackOfComp
    {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (hs : (p : Γ(s, ⊤)) = 0) (n : ℕ)
    {w : s ⟶ s} [IsIso w] [IsProper (X.iterateFrobenius hp hX n)]
    [IsProper (s.iterateFrobenius hp hs n)] [HasCompactification (a ≫ w)]
    [QuasiCompact (a ≫ w)] (hw : s.iterateFrobenius hp hs n ≫ w = 𝟙 s)
    (h : X.iterateFrobenius hp hX n ≫ a ≫ w = a)
    (hT : ∀ N : DerivedCategory (Sheaf s.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (globalSectionsTransport Λ w).hom.app
          ((L((s.iterateFrobenius hp hs n)^*[ModuleCat.{u + 1} Λ])).obj N) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s).map
          ((leftDerivedUpperStarComp _ w (s.iterateFrobenius hp hs n) (𝟙 s)
            (by rw [IsIso.eq_inv_of_inv_hom_id hw, IsIso.hom_inv_id])).inv.app N) =
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s).map
        ((leftDerivedUpperStarIterateFrobeniusIso _ hp hs n).hom.app N)) :
    compactlySupportedGlobalSectionsTransport Λ a w =
      Functor.whiskerRight (lowerShriekPullbackOfComp Λ (X.iterateFrobenius hp hX n) h ≫
          Functor.whiskerRight (leftDerivedUpperStarIterateFrobeniusIso (ModuleCat.{u + 1} Λ) hp
            hX n ≪≫ leftDerivedUpperStarId _ X).hom R(a)_![ModuleCat.{u + 1} Λ] ≫
          (Functor.leftUnitor _).hom)
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s) := by
  have hw' : w ≫ s.iterateFrobenius hp hs n = 𝟙 s := by
    rw [IsIso.eq_inv_of_inv_hom_id hw, IsIso.hom_inv_id]
  have he : X.iterateFrobenius hp hX n ≫ a ≫ w = (a ≫ w) ≫ s.iterateFrobenius hp hs n :=
    (comp_iterateFrobenius hp (a ≫ w) hs hX n).symm
  have h₁₂ : (a ≫ w) ≫ s.iterateFrobenius hp hs n = a := by
    rw [Category.assoc, hw', Category.comp_id]
  have : HasCompactification (X.iterateFrobenius hp hX n ≫ a ≫ w) := HasCompactification.of_eq h.symm
  have : QuasiCompact (X.iterateFrobenius hp hX n ≫ a ≫ w) := by rw [h]; infer_instance
  have : HasCompactification ((a ≫ w) ≫ s.iterateFrobenius hp hs n) :=
    HasCompactification.of_eq h₁₂.symm
  have : QuasiCompact ((a ≫ w) ≫ s.iterateFrobenius hp hs n) := by rw [h₁₂]; infer_instance
  have : HasCompactification (a ≫ 𝟙 s) := HasCompactification.of_eq (Category.comp_id a).symm
  have : QuasiCompact (a ≫ 𝟙 s) := by rw [Category.comp_id]; infer_instance
  refine eq_whiskerRight_of_transport (derivedUpperStarLowerStarAdjunction _ w)
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s) (globalSectionsTransport Λ w).hom
    (leftDerivedUpperStarIterateFrobeniusIso _ hp hs n) (leftDerivedUpperStarId _ s)
    (leftDerivedUpperStarComp _ w (s.iterateFrobenius hp hs n) (𝟙 s) hw'.symm) hT
    (rightDerivedLowerShriekCompIso Λ a w).hom
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) w).hom
    (lowerShriekPullbackOfComp Λ (X.iterateFrobenius hp hX n) h)
    (leftDerivedUpperStarIterateFrobeniusIso (ModuleCat.{u + 1} Λ) hp hX n ≪≫
      leftDerivedUpperStarId _ X).hom (fun M ↦ ?_) _ rfl
  have : HasCompactification (w ≫ s.iterateFrobenius hp hs n) := HasCompactification.of_eq hw'.symm
  have : QuasiCompact (w ≫ s.iterateFrobenius hp hs n) := by rw [hw']; infer_instance
  have hA := pullbackOfComp_app_comp_map_eq (lowerShriekPullbackOfComp Λ (X.iterateFrobenius hp hX n) h)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (X.iterateFrobenius hp hX n))
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) _)
    (rightDerivedLowerShriekCompIso Λ (X.iterateFrobenius hp hX n) (a ≫ w))
    (rightDerivedLowerShriekCongrIso Λ h)
    (leftDerivedUpperStarIterateFrobeniusIso (ModuleCat.{u + 1} Λ) hp hX n ≪≫
      leftDerivedUpperStarId _ X) rfl M
  have hρ₀ : rightDerivedLowerShriekIterateFrobeniusIso Λ hp n hX =
      rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) _ ≪≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (X.iterateFrobenius hp hX n)).rightAdjointUniq
          (Adjunction.id.ofNatIsoLeft (leftDerivedUpperStarIterateFrobeniusIso
            (ModuleCat.{u + 1} Λ) hp hX n ≪≫ leftDerivedUpperStarId _ X).symm) := rfl
  rw [← hρ₀] at hA
  have hFr := rightDerivedLowerShriekCompIso_iterateFrobenius Λ hp n hX hs (a ≫ w) M
  have hnat := (rightDerivedLowerShriekIterateFrobeniusIso Λ hp n hs).hom.naturality
    (X := (R(a ≫ w)_![ModuleCat.{u + 1} Λ]).obj M)
    (Y := (R(w)_![ModuleCat.{u + 1} Λ]).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj M))
    ((rightDerivedLowerShriekCompIso Λ a w).hom.app M)
  have hass := rightDerivedLowerShriekCompIso_congr_assoc_app Λ a w (Category.comp_id a) hw' h₁₂ M
  have hunit := rightDerivedLowerShriekCompIso_id_right_hom_app Λ a M
  have hcore := rightDerivedLowerShriekCompIso_hom_app_comp_iterateFrobenius Λ hp n hs hw'
    ((R(a)_![ModuleCat.{u + 1} Λ]).obj M)
  have hcc := rightDerivedLowerShriekCongrIso_hom_app_trans Λ he h₁₂ M
  refine comp_eq_of_frobenius ((rightDerivedLowerShriekCompIso Λ a w).hom.app M) _ _
    ((R(a ≫ w)_![ModuleCat.{u + 1} Λ]).mapIso
      ((rightDerivedLowerShriekIterateFrobeniusIso Λ hp n hX).app M))
    ((rightDerivedLowerShriekCompIso Λ (X.iterateFrobenius hp hX n) (a ≫ w)).app M)
    ((rightDerivedLowerShriekCongrIso Λ h).app M) ((rightDerivedLowerShriekCongrIso Λ he).app M)
    ((rightDerivedLowerShriekCompIso Λ (a ≫ w) (s.iterateFrobenius hp hs n)).app M)
    ((rightDerivedLowerShriekIterateFrobeniusIso Λ hp n hs).app
      ((R(a ≫ w)_![ModuleCat.{u + 1} Λ]).obj M))
    ((R(s.iterateFrobenius hp hs n)_![ModuleCat.{u + 1} Λ]).map
      ((rightDerivedLowerShriekCompIso Λ a w).hom.app M))
    ((rightDerivedLowerShriekIterateFrobeniusIso Λ hp n hs).app
      ((R(w)_![ModuleCat.{u + 1} Λ]).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj M)))
    ((rightDerivedLowerShriekCongrIso Λ h₁₂).app M)
    ((rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) s).app
      ((R(a)_![ModuleCat.{u + 1} Λ]).obj M))
    ((rightDerivedLowerShriekCongrIso Λ hw').app ((R(a)_![ModuleCat.{u + 1} Λ]).obj M))
    ((rightDerivedLowerShriekCompIso Λ w (s.iterateFrobenius hp hs n)).app
      ((R(a)_![ModuleCat.{u + 1} Λ]).obj M)) hA hFr hnat.symm ?_ hcore hcc
  have hu' : (rightDerivedLowerShriekCongrIso Λ (Category.comp_id a)).inv.app M ≫
      (rightDerivedLowerShriekCompIso Λ a (𝟙 s)).hom.app M =
      (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) s).inv.app
        ((R(a)_![ModuleCat.{u + 1} Λ]).obj M) := by
    rw [← cancel_mono ((rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) s).hom.app _),
      Category.assoc, hunit, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    rfl
  exact hass.trans (by rw [reassoc_of% hu']; rfl)

/-- **The operator of a Frobenius correspondence is the global operator**: let `Φ = F_X ≫ g` be
the composite of the absolute Frobenius `F_X` of `X` and an automorphism `g` of `X` over an
automorphism `σ` of `s` inverse to the absolute Frobenius `F_s` (a cartesian square), so that `Φ`
is an endomorphism over `s`. For `v : Lg^* K ⟶ K` and the identification
`κ : LΦ^* ≅ Lg^* ⋙ LF_X^* ≅ Lg^*` given by the trivialization of `L(F_X)^*`, the operator
`T(v ∘ κ) = RΓ_c(X, v ∘ κ) ∘ Φ^♯` is the global operator `RΓ_c(X, v) ∘ g_c^*`. -/
theorem correspondenceOperator_comp_eq_globalOperator {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (hs : (p : Γ(s, ⊤)) = 0) (n : ℕ) {Φ g : X ⟶ X} {σ : s ⟶ s}
    [IsProper Φ] [IsProper (X.iterateFrobenius hp hX n)] [IsProper (s.iterateFrobenius hp hs n)]
    [IsIso g] [IsIso σ]
    [HasCompactification (a ≫ σ)] [QuasiCompact (a ≫ σ)] (sq : IsPullback g a a σ)
    (hΦ : Φ ≫ a = a) (hFg : Φ = X.iterateFrobenius hp hX n ≫ g)
    (hσ : s.iterateFrobenius hp hs n ≫ σ = 𝟙 s)
    (hT : ∀ N : DerivedCategory (Sheaf s.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (globalSectionsTransport Λ σ).hom.app
          ((L((s.iterateFrobenius hp hs n)^*[ModuleCat.{u + 1} Λ])).obj N) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s).map
          ((leftDerivedUpperStarComp _ σ (s.iterateFrobenius hp hs n) (𝟙 s)
            (by rw [IsIso.eq_inv_of_inv_hom_id hσ, IsIso.hom_inv_id])).inv.app N) =
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s).map
        ((leftDerivedUpperStarIterateFrobeniusIso _ hp hs n).hom.app N))
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (v : L((g)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K) :
    correspondenceOperator Λ Φ hΦ ((leftDerivedUpperStarComp _ _ _ _ hFg).hom.app K ≫
        (leftDerivedUpperStarIterateFrobeniusIso _ hp hX n ≪≫ leftDerivedUpperStarId _ X).hom.app
          (L((g)^*[ModuleCat.{u + 1} Λ]).obj K) ≫ v) =
      globalOperator Λ sq v := by
  have h₁ : X.iterateFrobenius hp hX n ≫ a ≫ σ = a := by
    rw [← Category.assoc, ← comp_iterateFrobenius hp a hs hX, Category.assoc, hσ,
      Category.comp_id]
  have hΦ' (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      (lowerShriekPullback Λ Φ hΦ).app K =
        (lowerShriekPullbackOfComp Λ g sq.w).app K ≫
          (lowerShriekPullbackOfComp Λ (X.iterateFrobenius hp hX n) h₁).app
            (L((g)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
          (R(a)_![ModuleCat.{u + 1} Λ]).map
            ((leftDerivedUpperStarComp _ _ _ _ hFg).inv.app K) := by
    rw [← lowerShriekPullbackOfComp_eq_lowerShriekPullback]
    exact lowerShriekPullbackOfComp_comp_app Λ _ _ _ hFg h₁ sq.w hΦ K
  exact map_app_comp_map_eq_app_comp_map (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s)
    (lowerShriekPullbackOfComp Λ g sq.w)
    (lowerShriekPullbackOfComp Λ (X.iterateFrobenius hp hX n) h₁) (lowerShriekPullback Λ Φ hΦ)
    (leftDerivedUpperStarIterateFrobeniusIso _ hp hX n ≪≫ leftDerivedUpperStarId _ X).hom
    (leftDerivedUpperStarComp _ _ _ _ hFg)
    (compactlySupportedGlobalSectionsTransport Λ a σ) (compactPullback Λ sq) hΦ'
    (compactlySupportedGlobalSectionsTransport_eq_lowerShriekPullbackOfComp Λ a hp
      hX hs n hσ h₁ hT)
    (compactPullback_eq_whiskerRight_lowerShriekPullbackOfComp Λ a sq) v

end Base

end AlgebraicGeometry.Etale
