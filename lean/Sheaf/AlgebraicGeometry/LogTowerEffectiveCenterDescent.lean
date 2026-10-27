/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.AlgebraicGeometry.LogTowerCenterDescentDatum
import Sheaf.AlgebraicGeometry.CoherentLogIdealChartConstruction
import Sheaf.AlgebraicGeometry.EtaleLocalNoetherianDescent

/-!
# Effective descent of ordered log towers through their centers

Source: ILO VIII 3.3.7--3.3.10, pp.107--108, and the initial descent assertion
in the proof of 3.3.15, p.109 (blueprint: lem-trf-log-tower-effective-center-descent).

The realization retains every index. Its maps identify the given local levels
and their overlaps with scheme-theoretic fiber products. Its section formula and
uniqueness clause descend the actual ideal subsheaves, rather than abstract sheaves.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A realization of the given ordered datum, including the exact descended subideals.
All levels are locally Noetherian and fs by `FineSaturatedLogScheme`; all centers are
nonempty coherent and all arrows are universal saturated blowups by `isBlowup`.
The equality `centers` identifies the entire restricted ideals, hence also every
nonempty finite system of local generators, with the same generators on the same
charts. The `recursive` squares identify each local blowup with strict restriction.
The overlap map is normalized by its two projections, and its Cartesian square
identifies the overlap with the first recursive overlap pullback. The equation
`induces` identifies the prescribed Čech datum with the datum of the descended tower.
Source: ILO VIII 3.3.7--3.3.10 and proof of 3.3.15, pp.107--109
(blueprint: lem-trf-log-tower-effective-center-descent). -/
structure LogTowerCenterDescentRealization {X U : FineSaturatedLogScheme.{u}}
    (uMap : EtaleLogHom U X) (S : LogBlowupTowerOver U)
    (D : LogTowerCenterDescentDatum uMap S) (B : LogBlowupTowerOver X) where
  length : B.tower.length = S.tower.length
  map : ∀ j : Fin (B.tower.length + 1),
    EtaleLogHom (S.tower.level (Fin.cast (congrArg (fun n ↦ n + 1) length) j))
      (B.tower.level j)
  initial : HEq (map 0) uMap
  strict : ∀ j, (map j).IsStrict
  etale : ∀ j, Etale (map j).base
  surjective : ∀ j, Surjective (map j).base
  cartesian : ∀ j, (map j).IsFSPullback (B.toBase j)
    (S.toBase (Fin.cast (congrArg (fun n ↦ n + 1) length) j)) uMap
  schemeCartesian : ∀ j, IsPullback (map j).base
    (S.toBase (Fin.cast (congrArg (fun n ↦ n + 1) length) j)).base
    (B.toBase j).base uMap.base
  recursive : ∀ i : Fin B.tower.length,
    (S.tower.arrow (Fin.cast length i)).IsFSPullback
      (map i.castSucc) (map i.succ) (B.tower.arrow i)
  centers : ∀ i : Fin B.tower.length,
    (map i.castSucc).pullbackIdeal (B.tower.center i) =
      S.tower.center (Fin.cast length i)
  induces : ∀ (T : FineSaturatedLogScheme.{u}) (a b : EtaleLogHom T U)
    (h : a.comp uMap = b.comp uMap) (j : Fin (B.tower.length + 1))
    (s : LogTowerPoint S (Fin.cast (congrArg (fun n ↦ n + 1) length) j) T a),
    (D.transport T a b h _ s).val.comp (map j) = s.val.comp (map j)
  overlap : ∀ j, ∃ r : pullback (map j).base (map j).base ⟶
      pullback uMap.base uMap.base,
    r ≫ pullback.fst uMap.base uMap.base =
      pullback.fst (map j).base (map j).base ≫
        (S.toBase (Fin.cast (congrArg (fun n ↦ n + 1) length) j)).base ∧
    r ≫ pullback.snd uMap.base uMap.base =
      pullback.snd (map j).base (map j).base ≫
        (S.toBase (Fin.cast (congrArg (fun n ↦ n + 1) length) j)).base ∧
    IsPullback (pullback.fst (map j).base (map j).base) r
      (S.toBase (Fin.cast (congrArg (fun n ↦ n + 1) length) j)).base
      (pullback.fst uMap.base uMap.base)
  sections : ∀ (i : Fin B.tower.length) (V : (B.tower.level i.castSucc).scheme.Etale)
    (m : (B.tower.level i.castSucc).logStructure.monoidSheaf.obj.obj (op V)),
    m ∈ B.tower.center i V ↔
      (map i.castSucc).sectionMap V
        (Scheme.Etale.mk (pullback.fst (map i.castSucc).base V.hom))
        (pullback.snd (map i.castSucc).base V.hom) pullback.condition.symm m ∈
          S.tower.center (Fin.cast length i)
            (Scheme.Etale.mk (pullback.fst (map i.castSucc).base V.hom))
  uniqueIdeal : ∀ (i : Fin B.tower.length)
    (K : (B.tower.level i.castSucc).logStructure.IdealFamily),
    (B.tower.level i.castSucc).logStructure.IsIdeal K →
      (map i.castSucc).pullbackIdeal K = S.tower.center (Fin.cast length i) →
        K = B.tower.center i
  proper : (∀ i : Fin S.tower.length, S.tower.center i ≠ fun _ ↦ Set.univ) →
    ∀ i : Fin B.tower.length, B.tower.center i ≠ fun _ ↦ Set.univ

/-- Ordered effective descent with the sectionwise characterization of each center.
No stage is deleted, including whole-center or proper principal-center stages.
Length zero and the empty base are included.

Source: ILO VIII 3.3.7--3.3.10, pp.107--108, and proof of 3.3.15, p.109
(blueprint: lem-trf-log-tower-effective-center-descent).

Proof:
1. Induct on reconstructed stages, starting with X and its given strict etale cover.
   `lem-trf-log-tower-cover-synchronization` identifies the pullback of each prefix
   with the scheme pullback and its overlap with U_i times over X_i with U_i.
   Center preservation identifies the two restrictions of the next actual ideal.
2. Define I_i(V) by the displayed section condition. Restrictions and multiplication
   preserve it. Glue ambient log sections first, and use the sheaf axiom for J_i
   on the pulled-back cover to prove that this is an ideal subsheaf
   (`def-weil-pbc-etale-sheaf-of-sets`, `def-weil-pbc-etale-site`).
3. On an etale W over U_i, use center preservation on W times over X_i with U_i
   to show J_i is contained in the restriction of I_i. Restriction along the graph
   section gives the converse. For any other subideal restricting to J_i, the sheaf
   axiom on V times over X_i with U_i detects membership and proves uniqueness.
4. Choose finite nonempty chart generators for J_i. The restriction equality uses
   those very same generators. Their charts, composed with the surjective strict
   etale cover, exhibit nonempty coherence of I_i (`def-trf-fs-log-blowup`).
5. `lem-trf-coherent-log-ideal-chart-construction` constructs the universal saturated
   blowup of I_i. Its strict restriction is the blowup of J_i. The two universal
   objects have unique inverse comparison maps. Synchronization supplies the next
   surjective strict etale map and scheme pullback; local Noetherianity descends by
   `lem-trf-etale-local-noetherian-descent` (fs is built into the construction).
6. The induced overlap comparison and the prescribed theta both compare the same
   universal blowup objects. Uniqueness makes them equal. Repeat through precisely
   the original number of stages, retaining every center and the specified datum.
7. If I_i is whole, its restriction J_i is whole; hence proper J_i give proper I_i.
   The induction starts and ends at X for length zero. On an empty base the same
   sheaf formulas and universal constructions retain the prescribed length; if all
   centers are proper, that length must be zero. -/
theorem log_tower_effective_center_descent
    {X U : FineSaturatedLogScheme.{u}} (uMap : EtaleLogHom U X)
    (hstrict : uMap.IsStrict) (hetale : Etale uMap.base)
    (hsurjective : Surjective uMap.base) (S : LogBlowupTowerOver U)
    (D : LogTowerCenterDescentDatum uMap S) :
    ∃ B : LogBlowupTowerOver X, Nonempty (LogTowerCenterDescentRealization uMap S D B) := by
  sorry

end AlgebraicGeometry
