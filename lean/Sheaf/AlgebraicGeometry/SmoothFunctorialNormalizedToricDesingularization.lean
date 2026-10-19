/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
import Mathlib.Algebra.Field.ULift

/-!
# Smooth-functorial normalized toric desingularization over the rationals

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé VIII,
Theorem 2.3.10, normalized restriction in 2.3.9 and Remark 2.3.12(i),
Corollary 2.3.17, printed pp. 93--95, with the application in 3.2.19,
p. 106 (blueprint: lem-trf-toric-normalized-desingularization).

The rule below records the finite normalized towers, their coherent centers,
the stagewise torus actions, and the canonical smooth-pullback contractions.
The field `baseIso` identifies level zero with the toric realization, while
`toBase` records the structural map of every later blowup level.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Monoscheme

/-- A normalized toric tower over a fine torsion-free monoscheme, with its
structural maps and stagewise torus actions.  Source: ILO VIII, 2.3.9,
2.3.12(i), and 2.3.17 (blueprint: lem-trf-toric-normalized-desingularization). -/
structure NormalizedToricTower (M : Fine.{u}) where
  length : ℕ
  tower : NormalizedTower.{u} length
  baseIso : tower.level 0 ≅ realization (ULift.{u} ℚ) M
  toBase : ∀ i : Fin (length + 1),
    tower.level i ⟶ Spec (.of (ULift.{u} ℚ))
  toBase_zero : toBase 0 =
    baseIso.hom ≫ realizationToBase (ULift.{u} ℚ) M
  toBase_comp : ∀ i : Fin length,
    tower.arrow i ≫ toBase i.castSucc = toBase i.succ
  centers : ∀ i : Fin length,
    (tower.center i).ofFiniteType ∧
      Set.Nonempty ((tower.center i).support : Set (tower.level i.castSucc)) ∧
      IsNowhereDense ((tower.center i).support : Set (tower.level i.castSucc))
  desingularization : tower.IsDesingularization
  action : ∀ (C : ToricComponent M) (i : Fin (length + 1)),
    pullback (torusToBase (ULift.{u} ℚ) C) (toBase i) ⟶ tower.level i
  action_naturality : ∀ (C : ToricComponent M) (i : Fin length),
    (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ tower.arrow i)
      (by rw [Category.assoc, toBase_comp]; exact pullback.condition)) ≫ action C i.castSucc =
      action C i.succ ≫ tower.arrow i
  action_base : ∀ C : ToricComponent M,
    (pullback.lift (pullback.fst _ _)
      (pullback.snd _ _ ≫ componentι (ULift.{u} ℚ) C ≫ baseIso.inv)
      (by
        rw [Category.assoc, Category.assoc, toBase_zero, Iso.inv_hom_id_assoc,
          componentToBase]
        exact pullback.condition)) ≫ action C 0 =
      torusAction (ULift.{u} ℚ) C ≫ componentι (ULift.{u} ℚ) C ≫ baseIso.inv
  center_preserved : ∀ (C : ToricComponent M) (i : Fin length),
    (tower.center i).comap (action C i.castSucc) =
      (tower.center i).comap (pullback.snd (torusToBase (ULift.{u} ℚ) C)
        (toBase i.castSucc))

/-- A smooth pullback comparison of normalized toric towers.  Source: ILO VIII,
2.3.4 and 2.3.9 (blueprint: lem-trf-toric-normalized-desingularization). -/
structure NormalizedToricComparison {M N : Fine.{u}}
    (T : NormalizedToricTower M) (S : NormalizedToricTower N)
    (h : realization (ULift.{u} ℚ) N ⟶ realization (ULift.{u} ℚ) M) where
  pulled : NormalizedTower.{u} T.length
  pulledBase : pulled.level 0 ≅ realization (ULift.{u} ℚ) N
  pullback : NormalizedPullback T.tower pulled
  base_commutes : pulledBase.hom ≫ h = pullback.lift 0 ≫ T.baseIso.hom
  contraction : NormalizedContraction pulled S.tower
  contraction_base :
    (contraction.iso 0).hom ≫
        eqToHom (congrArg S.tower.level contraction.first) ≫ S.baseIso.hom =
      pulledBase.hom

/-- The level map supplied by a normalized comparison.  Source: ILO VIII,
2.3.4 (blueprint: lem-trf-toric-normalized-desingularization). -/
noncomputable def NormalizedToricComparison.levelMap
    {M N : Fine.{u}} {T : NormalizedToricTower M}
    {S : NormalizedToricTower N}
    {h : realization (ULift.{u} ℚ) N ⟶ realization (ULift.{u} ℚ) M}
    (c : NormalizedToricComparison T S h) (i : Fin (T.length + 1)) :
    S.tower.level (c.contraction.index i) ⟶ T.tower.level i :=
  (c.contraction.iso i).inv ≫ c.pullback.lift i

/-- One rule simultaneously assigns a tower to every fine torsion-free
monoscheme, including finite disjoint unions, and supplies all smooth
pullback, identity, composition, and surjectivity clauses.  Source: ILO VIII,
2.3.10 and 2.3.17 (blueprint: lem-trf-toric-normalized-desingularization). -/
structure SmoothFunctorialNormalizedToricDesingularization where
  tower : ∀ M : Fine.{u}, M.IsTorsionFree → NormalizedToricTower M
  comparison : ∀ (M N : Fine.{u})
    (hM : M.IsTorsionFree) (hN : N.IsTorsionFree)
    (h : realization (ULift.{u} ℚ) N ⟶ realization (ULift.{u} ℚ) M),
    Smooth h →
    NormalizedToricComparison (tower M hM) (tower N hN) h
  identityIndex : ∀ (M : Fine.{u}) (hM : M.IsTorsionFree)
    (i : Fin ((tower M hM).length + 1)),
    (comparison M M hM hM (𝟙 _) (by infer_instance)).contraction.index i = i
  identityMap : ∀ (M : Fine.{u}) (hM : M.IsTorsionFree)
    (i : Fin ((tower M hM).length + 1)),
    HEq ((comparison M M hM hM (𝟙 _) (by infer_instance)).levelMap i)
      (𝟙 ((tower M hM).tower.level i))
  compositionIndex : ∀ (M N P : Fine.{u})
    (hM : M.IsTorsionFree) (hN : N.IsTorsionFree) (hP : P.IsTorsionFree)
    (g : realization (ULift.{u} ℚ) N ⟶ realization (ULift.{u} ℚ) M)
    (h : realization (ULift.{u} ℚ) P ⟶ realization (ULift.{u} ℚ) N)
    (k : realization (ULift.{u} ℚ) P ⟶ realization (ULift.{u} ℚ) M)
    (hg : Smooth g) (hh : Smooth h) (hk : Smooth k)
    (_hc : k = h ≫ g) (i : Fin ((tower M hM).length + 1)),
    (comparison M P hM hP k hk).contraction.index i =
      (comparison N P hN hP h hh).contraction.index
        ((comparison M N hM hN g hg).contraction.index i)
  compositionMap : ∀ (M N P : Fine.{u})
    (hM : M.IsTorsionFree) (hN : N.IsTorsionFree) (hP : P.IsTorsionFree)
    (g : realization (ULift.{u} ℚ) N ⟶ realization (ULift.{u} ℚ) M)
    (h : realization (ULift.{u} ℚ) P ⟶ realization (ULift.{u} ℚ) N)
    (k : realization (ULift.{u} ℚ) P ⟶ realization (ULift.{u} ℚ) M)
    (hg : Smooth g) (hh : Smooth h) (hk : Smooth k)
    (_hc : k = h ≫ g) (i : Fin ((tower M hM).length + 1)),
    HEq ((comparison M P hM hP k hk).levelMap i)
      ((comparison N P hN hP h hh).levelMap
        ((comparison M N hM hN g hg).contraction.index i) ≫
        (comparison M N hM hN g hg).levelMap i)
  surjective_no_contraction : ∀ (M N : Fine.{u})
    (hM : M.IsTorsionFree) (hN : N.IsTorsionFree)
    (h : realization (ULift.{u} ℚ) N ⟶ realization (ULift.{u} ℚ) M)
    (hh : Smooth h),
    Surjective h →
      Function.Injective (comparison M N hM hN h hh).contraction.index

/--
Source: ILO VIII, Theorem 2.3.10, with the normalized restriction of 2.3.9,
Remark 2.3.12(i), Corollary 2.3.17 and the application in 3.2.19
(blueprint: lem-trf-toric-normalized-desingularization).

Proof.
1. Work on all reduced finite-type `ℚ`-schemes, so that products with acting tori
   lie in the domain.  Fix one ordinary smooth-functorial resolution rule `R`
   (lem-trf-smooth-functorial-ordinary-resolution).  For a normal member `S` with
   `R(S) = (S_i, I_i)` put `N_0 = S`, `N_i = S_iᶰ` for `i > 0`, and `K_i = I_i 𝒪_{N_i}`.
   By lem-trf-normalized-blowup-calculus, `N_{i+1} → N_i` is the normalized blowup
   of `K_i`.  The normalization maps are surjective and birational, so each `K_i` is
   coherent with nonempty nowhere dense zero scheme; the last level is regular,
   being the normalization of a regular scheme.  Call this tower `Rᶰ(S)`.
2. For a smooth `T → S` of normal members, compare `R(T)` with the pulled-back
   ordinary tower and normalize the levels.  Smooth comparison of normalized blowups
   identifies each normalized level with the pullback of `N_i` and each center with
   `K_i 𝒪`.  All levels are normal, so a unit pulled-back ideal gives an identity
   normalized blowup and the stage is deleted; this yields `Rᶰ(T)` with the other
   ideals in order.  Identity and composition comparisons follow from those of the
   two cited nodes.
3. For an arbitrary reduced finite-type `X` let `D_X` be the conductor ideal
   (lem-trf-conductor-smooth-base-change) and `P(X) = B_{D_X}(X)`, normal of finite
   type.  Let `H(X)` be the stage `P(X) → X` followed by `Rᶰ(P(X))`.  If `D_X` is the
   unit ideal, `X` is normal and the first stage is omitted; otherwise `V(D_X)` is
   nonempty.  So `H(X)` is a finite normalized tower with nonempty nowhere dense
   centers and regular last level; the empty scheme gets the trivial tower.
4. For a smooth `h : Y → X`, `D_Y = D_X 𝒪_Y`, `P(Y) = P(X) ×_X Y` and `P(Y) → P(X)`
   is smooth.  A first stage with unit ideal is an identity on a normal scheme.
   Step 2 compares the tails, so `H(Y) = (h^* H(X))^c` with ordered ideals, and the
   identity and composition laws follow stagewise.  If `h` is surjective, every
   map of pulled-back levels is surjective, every nonempty center has nonempty
   inverse image, and no stage is deleted.
5. By lem-trf-toric-realization-finite-type the schemes `ℚ[M]`, including finite
   disjoint unions, are reduced of finite type; put `𝓕(X) = H(X)`.  Steps 3--4 give
   the tower and smooth-comparison clauses for all smooth scheme morphisms.  Fix
   the torus `T` of one torsion-free component, acting trivially on the other
   components.  Projection `p` and action `a : T × X → X` are smooth and surjective
   (`a` is `p` after the automorphism `(t, x) ↦ (t, t x)`), so Step 4 gives
   identical uncontracted towers `p^* H(X) = H(T × X) = a^* H(X)`.
6. Induct on the level.  Equality of the first ideals gives `p^* J_0 = a^* J_0`,
   i.e. `J_0` is equivariant in the sense of def-trf-monoscheme-toric-realization.
   The smooth normalized-blowup comparisons identify the next levels with `T × X_1`
   and `X_1 ×_{X,a} (T × X)`; their identification followed by projection is the
   lifted action `a_1`, and its unit and associativity diagrams hold by uniqueness
   in the normalized-blowup universal property on the normal, dominating levels.
   Repeating at each level gives `p_i^* J_i = a_i^* J_i` and the action on
   `X_{i+1}`; repeating for each component proves the final clause.
-/
theorem exists_smooth_functorial_normalized_toric_desingularization :
    Nonempty (SmoothFunctorialNormalizedToricDesingularization.{u}) := by
  sorry

end AlgebraicGeometry.Monoscheme
