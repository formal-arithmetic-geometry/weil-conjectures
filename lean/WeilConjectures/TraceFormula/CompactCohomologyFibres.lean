/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CompactCohomology

/-!

# Compactly supported cohomology of Weil objects: fibres and compatibilities

The Frobenius comparison `θ_f` of `WeilConjectures.TraceFormula.CompactCohomology` at a fibre
(proper base change for Weil objects) and its compatibility with the composition isomorphisms of
the lower shriek (the Leray isomorphism for Weil objects), blueprint
`lem-trf-weil-shriek-operator-fibres`. Split off `WeilConjectures.TraceFormula.CompactCohomology`,
which alone took longer than the 60 s a file may take.

## Main statements

- `ProEtale.CondensedRing.nonempty_weilCompactCohomology_weilLowerShriekOfFrobenius_iso`
- `ProEtale.CondensedRing.nonempty_weilStalk_weilLowerShriekOfFrobenius_iso`

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The Frobenius comparison at a fibre -/

section Fibre

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

set_option maxHeartbeats 1000000 in
-- the instances of the categories of sheaves make the rewriting slow
/-- **The Frobenius comparison at a fibre** (blueprint `lem-trf-weil-shriek-operator-fibres`,
proof of (2)): for the fibre `Z` of `f = r ≫ f'` over a point `y` fixed by `Φ_Y`, the base change
`β : Ly^* Rf_! ≅ RΓ_c(Z, -)` intertwines `Ly^*(θ_f)` with the pullback `Φ_Z^♯`. -/
lemma baseChange_comp_weilLowerShriekFrobeniusComparison_stalk {ΦY : Y ⟶ Y} {p : X' ⟶ X}
    {f' : X' ⟶ Y} {r : X ⟶ X'} {ΦZ : Z ⟶ Z} {j : Z ⟶ X'} {y : RationalPoint Y}
    [IsFinite r.left] [IsUniversalHomeomorphism r.left] [IsProper ΦZ.left]
    (sq : IsPullback p f' (r ≫ f') ΦY) (hy : y ≫ ΦY = y)
    (hZ : IsPullback (j ≫ p) (toPoint Z) (r ≫ f') y) (hL : IsPullback j (toPoint Z) f' y)
    (hT : IsPullback (j ≫ p) ΦZ r j) (hi : ΦZ ≫ j ≫ p = (j ≫ p) ≫ r ≫ p)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    eqToHom (congrArg (fun g ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
        ℓ g).obj ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (r ≫ f')).obj K)) hy.symm) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ y ΦY).hom.app
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (r ≫ f')).obj K) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).map
        ((weilLowerShriekFrobeniusComparison ℓ (r ≫ p) ΦY (r ≫ f') sq r rfl rfl).hom.app K) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (r ≫ p)).obj K) =
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).app K ≫
      (compactPullback ℓ ΦZ).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (j ≫ p)).obj K) ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Z)).map
        ((weilUpperStarComparison ℓ ΦZ (r ≫ p) (j ≫ p) hi).hom.app K) := by
  have hH := boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz ℓ hL sq K
  have cH := boundedConstructibleLowerShriekBaseChange_padicAlgCl_congr_app_bottom ℓ hZ
    (hL.paste_horiz sq) hy.symm K
  have hk := baseChange_comp_relativeFrobenius_stalk ℓ hZ hL hT hi K
  simp only [weilLowerShriekFrobeniusComparison, Iso.trans_hom, NatTrans.comp_app, asIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app, eqToIso.hom, eqToHom_app,
    Category.id_comp, Functor.comp_obj, Functor.id_obj]
  simp only [Functor.map_comp, Category.assoc]
  rw [cH, hH]
  rw [eqToHom_refl ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
      (r ≫ f')).obj ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (r ≫ p)).obj K))]
  rw [CategoryTheory.Functor.map_id, Category.id_comp
      (X := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).obj
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (r ≫ f')).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (r ≫ p)).obj K)))
      ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).app _)]
  simp only [Category.assoc]
  rw [hk]

set_option maxHeartbeats 1000000 in
-- the instances of the categories of sheaves make the rewriting slow
/-- `baseChange_comp_weilLowerShriekFrobeniusComparison_stalk`
followed by a morphism `h`; stated by hand, `@[reassoc]` took 7-20 s here. -/
lemma baseChange_comp_weilLowerShriekFrobeniusComparison_stalk_assoc {ΦY : Y ⟶ Y} {p : X' ⟶ X}
    {f' : X' ⟶ Y} {r : X ⟶ X'} {ΦZ : Z ⟶ Z} {j : Z ⟶ X'} {y : RationalPoint Y}
    [IsFinite r.left] [IsUniversalHomeomorphism r.left] [IsProper ΦZ.left]
    (sq : IsPullback p f' (r ≫ f') ΦY) (hy : y ≫ ΦY = y)
    (hZ : IsPullback (j ≫ p) (toPoint Z) (r ≫ f') y) (hL : IsPullback j (toPoint Z) f' y)
    (hT : IsPullback (j ≫ p) ΦZ r j) (hi : ΦZ ≫ j ≫ p = (j ≫ p) ≫ r ≫ p)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {W : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧} (h : _ ⟶ W) :
    eqToHom (congrArg (fun g ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
        ℓ g).obj ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (r ≫ f')).obj K)) hy.symm) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ y ΦY).hom.app
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (r ≫ f')).obj K) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).map
        ((weilLowerShriekFrobeniusComparison ℓ (r ≫ p) ΦY (r ≫ f') sq r rfl rfl).hom.app K) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (r ≫ p)).obj K) ≫ h =
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).app K ≫
      (compactPullback ℓ ΦZ).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (j ≫ p)).obj K) ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Z)).map
        ((weilUpperStarComparison ℓ ΦZ (r ≫ p) (j ≫ p) hi).hom.app K) ≫ h := by
  have e := baseChange_comp_weilLowerShriekFrobeniusComparison_stalk ℓ sq hy hZ hL hT hi K =≫ h
  simp only [Category.assoc] at e
  exact e

end Fibre

/-! ### Compatibilities with the lower shriek -/

section Compatibilities

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {ΦX : X ⟶ X} {ΦY : Y ⟶ Y} {f : X ⟶ Y} {p : X' ⟶ X} {f' : X' ⟶ Y}
  (sq : IsPullback p f' f ΦY) {r : X ⟶ X'} (hrp : r ≫ p = ΦX) (hrf : r ≫ f' = f)
  [IsFinite r.left] [IsUniversalHomeomorphism r.left]
  [IsFinite ΦX.left] [IsUniversalHomeomorphism ΦX.left]
  [IsFinite ΦY.left] [IsUniversalHomeomorphism ΦY.left]

omit [IsFinite ΦX.left]
  [IsUniversalHomeomorphism ΦX.left] [IsFinite ΦY.left] [IsUniversalHomeomorphism ΦY.left]
  [IsFinite r.left] [IsUniversalHomeomorphism r.left] in
/-- The relative Frobenius part of `θ_f` is the pullback along `r` on compactly supported
cohomology: `Rf'_!(η_r)` followed by `Rf'_! Rr_* ≅ Rf'_! Rr_! ≅ R(r ≫ f')_!` is `r^♯` under the
composition isomorphisms. -/
lemma compToPoint_inv_app_comp_relativeFrobenius (r : X ⟶ X') (f' : X' ⟶ Y) [IsProper r.left]
    (M : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekCompToPoint ℓ f').inv.app M ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f').map
          ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
            r).unit.app M)) ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f').map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv.app
            ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M))) ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ r f').inv.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M)) =
    (compactPullback ℓ r).app M ≫
      (boundedConstructibleLowerShriekCompToPoint ℓ (r ≫ f')).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M) := by
  have h₁ := (boundedConstructibleLowerShriekCompToPoint ℓ f').inv.naturality
    ((boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
      r).unit.app M)
  have h₂ := (boundedConstructibleLowerShriekCompToPoint ℓ f').inv.naturality
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ r).inv.app
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M))
  have h₃ := boundedConstructibleLowerShriekCompToPoint_assoc ℓ r f'
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M)
  simp only [Functor.comp_map] at h₁ h₂
  have h₃' : (boundedConstructibleLowerShriekCompToPoint ℓ f').inv.app
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ r).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M)) ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ r f').inv.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r).obj M)) =
      (boundedConstructibleLowerShriekCompToPoint ℓ r).hom.app _ ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ (r ≫ f')).inv.app _ := by
    rw [← cancel_epi ((boundedConstructibleLowerShriekCompToPoint ℓ r).inv.app _),
      ← reassoc_of% h₃, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← reassoc_of% h₁, ← reassoc_of% h₂, h₃', compactPullback_app]
  simp only [Category.assoc]

omit [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] [IsFinite ΦX.left]
  [IsUniversalHomeomorphism ΦX.left] [IsFinite ΦY.left] [IsUniversalHomeomorphism ΦY.left] in
/-- The casts at the end of `θ_f`. -/
lemma compToPoint_inv_app_comp_eqToHom {a : X ⟶ X} {b : X ⟶ Y} (ha : a = ΦX) (hb : b = f)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (e : (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ b).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a).obj K) =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX).obj K)) :
    (boundedConstructibleLowerShriekCompToPoint ℓ b).inv.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a).obj K) ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Y)).map
        (eqToHom e) ≫
      (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX).obj K) =
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
      (eqToHom (by rw [ha])) := by
  subst ha hb
  simp

omit [IsUniversalHomeomorphism ΦX.left] [IsUniversalHomeomorphism ΦY.left] in
include sq hrp hrf in
/-- **The Frobenius comparison of `Rf_!` on compactly supported cohomology** (blueprint
`lem-trf-weil-shriek-operator-fibres`, proof of (1)): under the composition isomorphism
`c_f : RΓ_c(Y, Rf_! K) ≅ RΓ_c(X, K)`, `RΓ_c(Y, θ_f) ∘ Φ_Y^♯` is `Φ_X^♯`. -/
lemma compactPullback_comp_weilLowerShriekFrobeniusComparison
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactPullback ℓ ΦY).app
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj K) ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Y)).map
        ((weilLowerShriekFrobeniusComparison ℓ ΦX ΦY f sq r hrp hrf).hom.app K) ≫
      (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX).obj K) =
    (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.app K ≫ (compactPullback ℓ ΦX).app K := by
  have : IsFinite p.left := MorphismProperty.of_isPullback sq.overLeft.flip inferInstance
  have : IsProper (r ≫ p).left := by
    rw [Over.comp_left]
    infer_instance
  have hB : (compactPullback ℓ ΦY).app
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj K) ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Y)).map
        ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K) =
      (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.app K ≫ (compactPullback ℓ p).app K ≫
        (boundedConstructibleLowerShriekCompToPoint ℓ f').inv.app _ := by
    rw [← reassoc_of% (compactPullback_app_comp_baseChange ℓ sq K), Iso.hom_inv_id_app]
    simp only [Functor.comp_obj, Category.comp_id]
  have hn := (boundedConstructibleLowerShriekCompToPoint ℓ (r ≫ f')).inv.naturality
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ r p).inv.app K)
  simp only [Functor.comp_map] at hn
  simp only [weilLowerShriekFrobeniusComparison, Iso.trans_hom, NatTrans.comp_app, asIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app, eqToIso.hom, eqToHom_app,
    Category.id_comp, Functor.comp_obj, Functor.id_obj, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hB, reassoc_of% (compToPoint_inv_app_comp_relativeFrobenius ℓ r f' _),
    ← reassoc_of% hn, compToPoint_inv_app_comp_eqToHom ℓ hrp hrf,
    ← compactPullback_app_congr ℓ hrp, compactPullback_comp_app]
  simp only [Category.assoc]

omit [IsUniversalHomeomorphism ΦX.left] [IsUniversalHomeomorphism ΦY.left] in
include sq hrp hrf in
/-- `compactPullback_comp_weilLowerShriekFrobeniusComparison`
followed by a morphism `h`; stated by hand, `@[reassoc]` took 7-20 s here. -/
lemma compactPullback_comp_weilLowerShriekFrobeniusComparison_assoc
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {W : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧} (h : _ ⟶ W) :
    (compactPullback ℓ ΦY).app
        ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj K) ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Y)).map
        ((weilLowerShriekFrobeniusComparison ℓ ΦX ΦY f sq r hrp hrf).hom.app K) ≫
      (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX).obj K) ≫ h =
    (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.app K ≫ (compactPullback ℓ ΦX).app K ≫
      h := by
  have e := compactPullback_comp_weilLowerShriekFrobeniusComparison ℓ sq hrp hrf K =≫ h
  simp only [Category.assoc] at e
  exact e

set_option maxHeartbeats 1000000 in
-- the defeq of the carriers of the lower shriek of Weil objects with `Rf_! K` is slow
/-- **The Leray isomorphism for Weil objects** (blueprint `lem-trf-weil-shriek-operator-fibres`,
the global operators): the compactly supported cohomology of `Rf_! K` is that of `K`,
`RΓ_c(Y, Rf_! K) ≅ RΓ_c(X, K)`, as Weil objects for the identity of the base point. In
particular the global operators of `K` and of `Rf_! K` have the same trace. -/
theorem nonempty_weilCompactCohomology_weilLowerShriekOfFrobenius_iso
    (K : WeilBoundedConstructible ℓ ΦX) :
    Nonempty ((weilCompactCohomology ℓ ΦY).obj
        ((weilLowerShriekOfFrobenius ℓ ΦX ΦY f sq r hrp hrf).obj K) ≅
      (weilCompactCohomology ℓ ΦX).obj K) := by
  refine ⟨IsoAlgebra.isoMk ((boundedConstructibleLowerShriekCompToPoint ℓ f).app K.carrier)
    (WeilBoundedConstructible.isoMk_condition_of_frobenius _ ?_)⟩
  have hn := (boundedConstructibleLowerShriekCompToPoint ℓ f).hom.naturality K.str.hom
  simp only [Functor.comp_map] at hn
  rw [← WeilBoundedConstructible.compactFrobenius, ← WeilBoundedConstructible.compactFrobenius,
    WeilBoundedConstructible.compactFrobenius_eq, WeilBoundedConstructible.compactFrobenius_eq,
    weilLowerShriekOfFrobenius_obj_str]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [hn]
  -- the carriers are `Rf_! K` (resp. `Li^* K`) by `rfl`: make them syntactic so `rw` matches
  dsimp only [weilLowerShriekOfFrobenius_obj_carrier]
  rw [compactPullback_comp_weilLowerShriekFrobeniusComparison_assoc ℓ sq hrp hrf K.carrier]

variable {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] {ΦZ : Z ⟶ Z} [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]
  {i : Z ⟶ X} (hi : ΦZ ≫ i = i ≫ ΦX) {y : RationalPoint Y} (hy : y ≫ ΦY = y)
  (hZ : IsPullback i (toPoint Z) f y)

set_option maxHeartbeats 1000000 in
-- the defeq of the carriers of the lower shriek of Weil objects with `Rf_! K` is slow
omit [IsFinite ΦY.left] [IsUniversalHomeomorphism ΦY.left] in
include hZ in
/-- **Proper base change for Weil objects** (blueprint `lem-trf-weil-shriek-operator-fibres`, the
stalks): for a rational point `y` of `Y` fixed by `Φ_Y` with fibre `Z = X ×_Y y` carrying a
Frobenius `Φ_Z` compatible with `Φ_X`, the stalk at `y` of `Rf_! K` is the compactly supported
cohomology of the restriction of `K` to the fibre, `(Rf_! K)_ȳ ≅ RΓ_c(Z, K|_Z)`, as Weil objects
for the identity of the base point. In particular the local Frobenius of `Rf_! K` at `y` and the
global operator of `K|_Z` have the same trace. -/
theorem nonempty_weilStalk_weilLowerShriekOfFrobenius_iso (K : WeilBoundedConstructible ℓ ΦX) :
    Nonempty ((weilStalk ℓ ΦY y hy).obj
        ((weilLowerShriekOfFrobenius ℓ ΦX ΦY f sq r hrp hrf).obj K) ≅
      (weilCompactCohomology ℓ ΦZ).obj ((weilUpperStar ℓ ΦZ ΦX i hi).obj K)) := by
  obtain ⟨j, hj₁, hj₂⟩ : ∃ j : Z ⟶ X', j ≫ p = i ∧ j ≫ f' = toPoint Z ≫ y :=
    ⟨sq.lift i (toPoint Z ≫ y) (by rw [hZ.w, Category.assoc, hy]), sq.lift_fst _ _ _,
      sq.lift_snd _ _ _⟩
  subst hj₁ hrp hrf
  have hL : IsPullback j (toPoint Z) f' y := IsPullback.of_right (by rw [hy]; exact hZ) hj₂ sq
  have hTw : (j ≫ p) ≫ r = ΦZ ≫ j := sq.hom_ext
    (by simp only [Category.assoc] at hi ⊢; exact hi.symm)
    (by rw [Category.assoc, hZ.w, Category.assoc, hj₂, ← Category.assoc, comp_toPoint])
  have hT : IsPullback (j ≫ p) ΦZ r j := IsPullback.of_bot (by rw [comp_toPoint]; exact hZ) hTw hL
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ
  refine ⟨IsoAlgebra.isoMk (asIso ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
    hZ).app K.carrier)) (WeilBoundedConstructible.isoMk_condition_of_frobenius _ ?_)⟩
  rw [asIso_hom, WeilBoundedConstructible.weilStalk_obj_frobenius_hom_eq,
    ← WeilBoundedConstructible.compactFrobenius,
    WeilBoundedConstructible.compactFrobenius_eq, weilLowerShriekOfFrobenius_obj_str,
    weilUpperStar_obj_str]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have hn := (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).naturality K.str.hom
  simp only [Functor.comp_map] at hn
  rw [hn]
  -- the carriers are `Rf_! K` (resp. `Li^* K`) by `rfl`: make them syntactic so `rw` matches
  dsimp only [weilLowerShriekOfFrobenius_obj_carrier,
    weilUpperStar_obj_carrier]
  rw [baseChange_comp_weilLowerShriekFrobeniusComparison_stalk_assoc ℓ sq hy hZ hL hT hi
    K.carrier]

end Compatibilities

end AlgebraicGeometry.ProEtale.CondensedRing
