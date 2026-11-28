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
import WeilConjectures.TraceFormula.GrothendieckLefschetz.FrobeniusPullbackComp

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
morphism over `s` from `a ≫ w` to `a`, and the derived global sections of `R(a ≫ w)_!` and of
`Ra_!` are identified by the composition isomorphism and the Leray isomorphism of the proper
`w` (`AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsCompIso`). Two instances of this
construction are compared with other descriptions:

* for an automorphism `g` of `X` over an automorphism `h` of `s` (a cartesian square), the
  pullback along `g` is the compact-support base change
  `AlgebraicGeometry.Etale.compactPullback`
  (`AlgebraicGeometry.Etale.compactPullback_app_eq_map_lowerShriekPullbackOfComp`);
* the pullback along the absolute Frobenius `F_X` of a scheme of characteristic `p`, followed by
  the trivialization `L(F_X)^* ≅ 𝟭`, is the identity
  (`AlgebraicGeometry.Etale.map_lowerShriekPullbackOfComp_comp_iterateFrobenius`).

## Main definitions

- `AlgebraicGeometry.Etale.lowerShriekPullbackOfComp`: the pullback `u^♯ : Ra'_! ⟶ Lu^* ⋙ Ra_!`.
- `AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsCompIso`: the identification
  `RΓ(s, R(a ≫ w)_! -) ≅ RΓ(s, Ra_! -)` for a proper `w : s ⟶ s`.

## Main results

- `AlgebraicGeometry.Etale.lowerShriekPullbackOfComp_comp_app`: transitivity of the pullbacks.
- `AlgebraicGeometry.Etale.compactPullback_app_eq_map_lowerShriekPullbackOfComp`: the pullback
  along an automorphism over an automorphism of the base is the compact-support base change.
- `AlgebraicGeometry.Etale.map_lowerShriekPullbackOfComp_comp_iterateFrobenius`: the absolute
  Frobenius acts trivially on compactly supported cohomology.
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

omit [Finite Λ] in
/-- For a proper `u`, the identification `Ru_! ≅ Ru_*` is the forget-supports map of the chosen
compactification of `u`. -/
lemma rightDerivedLowerShriekIsoRightDerivedLowerStar_hom_eq_compactificationForgetSupports
    (u : X ⟶ Y) [IsProper u] :
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) u).hom =
      compactificationForgetSupports (ModuleCat.{u + 1} Λ)
        (HasCompactification.compactification u) := by
  rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom,
    rightDerivedLowerShriekToLowerStarComp_comp_eq]
  rfl

/-- The identifications `Rf_! ≅ Rf_*` of proper morphisms are compatible with the composition
isomorphisms of the lower shriek and of the lower star. -/
lemma rightDerivedLowerShriekCompIso_hom_app_comp_isoRightDerivedLowerStar {Z : Scheme.{u}}
    (u₁ : X ⟶ Y) (u₂ : Y ⟶ Z) [IsProper u₁] [IsProper u₂] [IsProper (u₁ ≫ u₂)]
    (P : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekCompIso Λ u₁ u₂).hom.app P ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar _ u₂).hom.app
          ((R(u₁)_![ModuleCat.{u + 1} Λ]).obj P) ≫
        (R((u₂)_*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ u₁).hom.app P) =
      (rightDerivedLowerShriekIsoRightDerivedLowerStar _ (u₁ ≫ u₂)).hom.app P ≫
        (rightDerivedLowerStarCompIsoOfComp _ u₁ u₂ (u₁ ≫ u₂) rfl).inv.app P := by
  rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom_eq_compactificationForgetSupports,
    rightDerivedLowerShriekIsoRightDerivedLowerStar_hom_eq_compactificationForgetSupports,
    rightDerivedLowerShriekIsoRightDerivedLowerStar_hom_eq_compactificationForgetSupports,
    ← cancel_mono ((rightDerivedLowerStarCompIsoOfComp _ u₁ u₂ (u₁ ≫ u₂) rfl).hom.app P)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← rightDerivedLowerShriekCompIso_inv_app_comp_forgetSupports, Iso.hom_inv_id_app_assoc]

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

section Base

variable {X : Scheme.{u}} (a : X ⟶ s) [QuasiCompact a] [HasCompactification a]

/-- For a proper `w : s ⟶ s`, the identification `RΓ(s, R(a ≫ w)_! -) ≅ RΓ(s, Ra_! -)` given by
the composition isomorphism `R(a ≫ w)_! ≅ Ra_! ⋙ Rw_!` and the isomorphism
`RΓ(s, Rw_! -) ≅ RΓ(s, -)` of the proper `w`
(`AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsIsoOfIsProper`). -/
noncomputable def compactlySupportedGlobalSectionsCompIso (w : s ⟶ s) [IsProper w]
    [HasCompactification (a ≫ w)] [QuasiCompact (a ≫ w)] :
    compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) (a ≫ w) ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a :=
  Functor.isoWhiskerRight (rightDerivedLowerShriekCompIso Λ a w) _ ≪≫
    Functor.isoWhiskerLeft R(a)_![ModuleCat.{u + 1} Λ]
      (compactlySupportedGlobalSectionsIsoOfIsProper (ModuleCat.{u + 1} Λ) w)

/-- **The pullback along an automorphism over an automorphism of the base is the compact-support
base change**: for a cartesian square `g ≫ a = a ≫ h` of automorphisms `g` of `X` and `h` of
`s`, the pullback along `g`, a morphism over `s` from `a ≫ h` to `a`, followed by the
identification `RΓ(s, R(a ≫ h)_! -) ≅ RΓ(s, Ra_! -)`, is the compact-support base change
`AlgebraicGeometry.Etale.compactPullback`. -/
theorem compactPullback_app_eq_map_lowerShriekPullbackOfComp {g : X ⟶ X} {h : s ⟶ s} [IsIso g]
    [IsIso h] (sq : IsPullback g a a h) [HasCompactification (a ≫ h)] [QuasiCompact (a ≫ h)]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactPullback Λ sq).app K =
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s).map
          ((lowerShriekPullbackOfComp Λ g sq.w).app K) ≫
        (compactlySupportedGlobalSectionsCompIso Λ a h).hom.app
          (L((g)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  sorry

/-- **The absolute Frobenius acts trivially on compactly supported cohomology**: let `X` and `s`
be schemes of characteristic `p` with absolute `p ^ n`-power Frobenius `F_X` and `F_s`, and let
`w` be an inverse of `F_s`, so that `F_X` is a morphism over `s` from `a` to `a ≫ w`. The
pullback along `F_X`, preceded by the identification `RΓ(s, Ra_! -) ≅ RΓ(s, R(a ≫ w)_! -)` and
followed by the trivialization `L(F_X)^* ≅ L(𝟙 X)^* ≅ 𝟭`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso`), is the identity of
`RΓ(s, Ra_! M)`. -/
theorem map_lowerShriekPullbackOfComp_comp_iterateFrobenius {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (hs : (p : Γ(s, ⊤)) = 0) (n : ℕ) {w : s ⟶ s} [IsProper w]
    [IsProper (X.iterateFrobenius hp hX n)] [HasCompactification (a ≫ w)]
    [QuasiCompact (a ≫ w)] (hw : s.iterateFrobenius hp hs n ≫ w = 𝟙 s)
    (hw' : w ≫ s.iterateFrobenius hp hs n = 𝟙 s)
    (h : X.iterateFrobenius hp hX n ≫ a ≫ w = a)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactlySupportedGlobalSectionsCompIso Λ a w).inv.app M ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s).map
          ((lowerShriekPullbackOfComp Λ (X.iterateFrobenius hp hX n) h).app M ≫
            (R(a)_![ModuleCat.{u + 1} Λ]).map
              ((leftDerivedUpperStarIterateFrobeniusIso (ModuleCat.{u + 1} Λ) hp hX n ≪≫
                leftDerivedUpperStarId _ X).hom.app M)) = 𝟙 _ := by
  sorry

/-- **The operator of a Frobenius correspondence is the global operator**: let `Φ = F_X ≫ g` be
the composite of the absolute Frobenius `F_X` of `X` and an automorphism `g` of `X` over an
automorphism `σ` of `s` inverse to the absolute Frobenius `F_s` (a cartesian square), so that `Φ`
is an endomorphism over `s`. For `v : Lg^* K ⟶ K` and the identification
`κ : LΦ^* ≅ Lg^* ⋙ LF_X^* ≅ Lg^*` given by the trivialization of `L(F_X)^*`, the operator
`T(v ∘ κ) = RΓ_c(X, v ∘ κ) ∘ Φ^♯` is the global operator `RΓ_c(X, v) ∘ g_c^*`. -/
theorem correspondenceOperator_comp_eq_globalOperator {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (hs : (p : Γ(s, ⊤)) = 0) (n : ℕ) {Φ g : X ⟶ X} {σ : s ⟶ s}
    [IsProper Φ] [IsProper (X.iterateFrobenius hp hX n)] [IsIso g] [IsIso σ]
    [HasCompactification (a ≫ σ)] [QuasiCompact (a ≫ σ)] (sq : IsPullback g a a σ)
    (hΦ : Φ ≫ a = a) (hFg : Φ = X.iterateFrobenius hp hX n ≫ g)
    (hσ : s.iterateFrobenius hp hs n ≫ σ = 𝟙 s) (hσ' : σ ≫ s.iterateFrobenius hp hs n = 𝟙 s)
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (v : L((g)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K) :
    correspondenceOperator Λ Φ hΦ ((leftDerivedUpperStarComp _ _ _ _ hFg).hom.app K ≫
        (leftDerivedUpperStarIterateFrobeniusIso _ hp hX n ≪≫ leftDerivedUpperStarId _ X).hom.app
          (L((g)^*[ModuleCat.{u + 1} Λ]).obj K) ≫ v) =
      globalOperator Λ sq v := by
  have h₁ : X.iterateFrobenius hp hX n ≫ a ≫ σ = a := by
    rw [← Category.assoc, ← comp_iterateFrobenius hp a hs hX, Category.assoc, hσ,
      Category.comp_id]
  have hF := map_lowerShriekPullbackOfComp_comp_iterateFrobenius Λ a hp hX hs n hσ hσ' h₁
    (L((g)^*[ModuleCat.{u + 1} Λ]).obj K)
  have hF' := (Iso.inv_comp_eq ((compactlySupportedGlobalSectionsCompIso Λ a σ).app
      (L((g)^*[ModuleCat.{u + 1} Λ]).obj K))).1 hF
  rw [Category.comp_id, Functor.map_comp] at hF'
  rw [correspondenceOperator, globalOperator, ← lowerShriekPullbackOfComp_eq_lowerShriekPullback,
    lowerShriekPullbackOfComp_comp_app Λ _ _ _ hFg h₁ sq.w,
    compactPullback_app_eq_map_lowerShriekPullbackOfComp Λ a sq K]
  simp only [Category.assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp]
  rw [reassoc_of% hF']
  rfl

end Base

end AlgebraicGeometry.Etale
