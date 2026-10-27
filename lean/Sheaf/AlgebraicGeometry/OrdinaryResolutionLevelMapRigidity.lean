/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.LabeledOrdinaryResolutionDescentData
import WeilConjectures.Blowup.BlowupUniversal
import WeilConjectures.Blowup.Principalization

/-! # Rigidity of smooth pullback maps into ordinary resolution levels

Source: ILO, Travaux de Gabber, VIII 2.3.4, printed p.91.
-/

@[expose] public section
set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.OrdinaryResolutionDescent

private theorem invertible_comap_transition {S : Scheme.{u}} (A : OrdinaryBlowupTower S)
    (i j : Fin (A.length + 1)) (hij : i ≤ j) (J : (A.level i).IdealSheafData)
    (hJ : J.IsInvertible) : (J.comap (A.transition i j hij)).IsInvertible := by
  induction j using Fin.induction with
  | zero =>
    have he : i = 0 := le_antisymm hij (Fin.zero_le i)
    subst i
    simpa only [A.transition_id, Scheme.IdealSheafData.comap_id] using hJ
  | succ k ih =>
    by_cases hik : i ≤ k.castSucc
    · have he : A.transition i k.succ hij =
          (A.blowupIso k).hom ≫ (A.center k).blowupMap ≫
            A.transition i k.castSucc hik := by
        rw [← Category.assoc, A.blowup_fac, A.transition_comp]
      rw [he, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
      exact ((ih hik).comap_blowupMap (A.center k)).comap_of_flat (A.blowupIso k).hom
    · have he : i = k.succ := by
        apply Fin.ext
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at hij hik ⊢
        omega
      subst i
      simpa only [A.transition_id, Scheme.IdealSheafData.comap_id] using hJ

private theorem center_comap_transition_invertible {S : Scheme.{u}}
    (A : OrdinaryBlowupTower S) (k : Fin A.length) (j : Fin (A.length + 1))
    (hkj : k.succ ≤ j) :
    ((A.center k).comap
      (A.transition k.castSucc j ((le_of_lt k.castSucc_lt_succ).trans hkj))).IsInvertible := by
  have he : A.transition k.castSucc j ((le_of_lt k.castSucc_lt_succ).trans hkj) =
      A.transition k.succ j hkj ≫ (A.blowupIso k).hom ≫ (A.center k).blowupMap := by
    rw [A.blowup_fac, A.transition_comp]
  rw [he, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
  exact invertible_comap_transition A k.succ j hkj _
    ((A.center k).isInvertible_comap_blowupMap.comap_of_flat (A.blowupIso k).hom)

private theorem tower_levelMap_unique {S P : Scheme.{u}} (A : OrdinaryBlowupTower S)
    (j : Fin (A.length + 1)) (p : P ⟶ A.level j) [Flat p]
    (i : Fin (A.length + 1)) (hij : i ≤ j)
    (f : P ⟶ A.level i) (hf : f ≫ A.toBase i = p ≫ A.toBase j) :
    f = p ≫ A.transition i j hij := by
  induction i using Fin.induction with
  | zero =>
    apply (cancel_mono A.initial.hom).mp
    change f ≫ A.transition 0 0 le_rfl ≫ A.initial.hom =
      p ≫ A.transition 0 j hij ≫ A.initial.hom at hf
    rw [A.transition_id, Category.id_comp] at hf
    exact hf
  | succ k ih =>
    have hkj : k.castSucc ≤ j := (le_of_lt k.castSucc_lt_succ).trans hij
    have hl : f ≫ A.transition k.castSucc k.succ (le_of_lt k.castSucc_lt_succ) =
        p ≫ A.transition k.castSucc j hkj := by
      apply ih hkj
      rw [Category.assoc]
      have ht : A.transition k.castSucc k.succ (le_of_lt k.castSucc_lt_succ) ≫
          A.toBase k.castSucc = A.toBase k.succ := by
        simp only [OrdinaryBlowupTower.toBase, ← Category.assoc, A.transition_comp]
      rw [ht]
      exact hf
    have hi := (center_comap_transition_invertible A k j hij).comap_of_flat p
    rw [← Scheme.IdealSheafData.comap_comp] at hi
    apply (cancel_mono (A.blowupIso k).hom).mp
    apply (A.center k).hom_ext_of_isInvertible_comap hi
    · simpa only [Category.assoc, A.blowup_fac] using hl
    · simp only [Category.assoc, A.blowup_fac, A.transition_comp]

/-- A map into a resolution level from its smooth pullback is determined by its map
on the base. Source: ILO VIII 2.3.4, uniqueness of morphisms between blowups;
Stacks 0806, 080A and 02OO for the universal property and invertible ideals
(blueprint: lem-trf-ordinary-resolution-level-map-rigidity).

Proof: An invertible ideal remains invertible after every later tower transition:
induct over those transitions, use stability under blowup pullback and pullback
by the specified blowup isomorphism. A center becomes invertible immediately after
its own blowup, so it remains invertible on every higher level. A flat map into that
higher level preserves this invertibility. Now induct over a lower target level.
At level zero, cancel the initial isomorphism. At a successor, the induction hypothesis
identifies the two maps to the preceding level; the invertible pullback ideal and the
universal property of that blowup identify the lifts. Finally the specified comparison
map is flat by its cartesian square and smoothness of the base map. Apply the preceding
uniqueness at the same source and target level. No reducedness, density or separation
argument is needed, and zero-length towers and empty schemes are included. -/
theorem smoothComparison_levelMap_unique
    {L : Type w} [LinearOrder L] (S T : RationalResolutionInput.{u})
    (h : T.scheme ⟶ S.scheme) [Smooth h]
    (A : LabeledTower L S.scheme) (B : LabeledTower L T.scheme)
    (c : Comparison h A B) (i : Fin (A.tower.length + 1))
    (f : B.tower.level (c.count i) ⟶ A.tower.level i)
    (hf : f ≫ A.tower.toBase i = B.tower.toBase (c.count i) ≫ h) :
    f = c.levelMap i := by
  have : Flat (c.levelMap i) :=
    MorphismProperty.of_isPullback (c.cartesian i).flip inferInstance
  have he := tower_levelMap_unique A.tower i (c.levelMap i) i le_rfl f
    (hf.trans (c.cartesian i).w.symm)
  simpa only [A.tower.transition_id, Category.comp_id] using he

end AlgebraicGeometry.OrdinaryResolutionDescent
