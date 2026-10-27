/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q137
-/
module

public import Sheaf.AlgebraicGeometry.QEOrdinaryResolutionRule
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import Sheaf.AlgebraicGeometry.GabberModificationData
public import WeilConjectures.Blowup.Gluing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.ReducedNoetherianBlowupGeometry
import Sheaf.AlgebraicGeometry.NoetherianNormalizedBlowupFinality
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.Irreducible
import WeilConjectures.AlgebraicGeometry.Dimension
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.Blowup.FlatBaseChange
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.GRingAffineCover
import Sheaf.AlgebraicGeometry.JTwoAffineCover

/-! # Local dimension bounds for ordinary blowup towers

Source: Temkin, Functorial desingularization of quasi-excellent schemes in characteristic
zero: the non-embedded case, arXiv:0904.1592v2, section 4.3, printed p. 30;
Stacks Project, Tags 0BAE, 0BFM, 0808, 0805, 04MU and 07QU
(blueprint: lem-per-blowup-local-dimension-bound).

The four statements give the local-ring bound, its stalk-spectrum base change,
quasi-excellence of the schemes involved, and their rational resolution input structures.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A coherent nowhere dense ordinary blowup tower over a reduced Noetherian local
ring has dimension at most that ring. A reduced nowhere dense closed subscheme has
dimension at most `n - 1` for `1 ≤ n`, including the empty subscheme.

Source: Temkin, section 4.3, Extensions 1,...,n, p. 30; Stacks 0BAE, 0BFM and 04MU
(blueprint: lem-per-blowup-local-dimension-bound).

Proof:
1. Induct through the tower, starting with affine_isReduced_iff. Apply
   lem-per-reduced-noetherian-blowup-geometry at each coherent center to obtain
   reducedness, Noetherianness and finite type. Compose the finite-type arrows using
   lem-sfb-finite-type-composition-base-change; a zero-length tower is the base case.
2. The ordinary-blowup clause of lem-per-noetherian-normalized-blowup-finality gives
   bijections on component generic points with isomorphic residue fields. Compose them.
   Apply lem-sfb-generic-residue-transcendence-dimension-bound with generic transcendence
   degree zero and base dimension n (def-weil-pbc-krull-dimension-ring). This is the
   inequality of Stacks 0BAE and requires no catenarity.
3. A chain of irreducible closed subsets in W lies in a component of the final scheme
   (lem-sc-irreducible-components-cover). There are finitely many components by
   lem-weil-pbc-noetherian-finitely-many-components, so nowhere density implies W contains
   none of them. Appending the containing component increases the chain length by one.
   The bound follows from def-kun-topological-krull-dimension. Empty W has dimension
   bottom. Apply lem-pc-scheme-dimension-local-rings for the local-ring bounds.
-/
theorem blowup_local_dimension_bound
    (A : Type u) [CommRing A] [IsLocalRing A] [_root_.IsReduced A] [IsNoetherianRing A]
    (n : ℕ) (hn : ringKrullDim A = (n : WithBot ℕ∞))
    (T : OrdinaryBlowupTower (Spec (.of A)))
    (hcoh : ∀ i : Fin T.length,
      RingedSpace.IsCoherent (T.level i.castSucc).toRingedSpace (T.center i).toModules)
    (hdense : ∀ i : Fin T.length,
      IsNowhereDense ((T.center i).support : Set (T.level i.castSucc))) :
    IsReduced (T.level (Fin.last T.length)) ∧
      IsNoetherian (T.level (Fin.last T.length)) ∧
      topologicalKrullDim (T.level (Fin.last T.length)) ≤ (n : WithBot ℕ∞) ∧
      ∀ (W : Scheme.{u}) (j : W ⟶ T.level (Fin.last T.length))
        [IsClosedImmersion j] [IsReduced W],
        IsNowhereDense (Set.range j) → 1 ≤ n →
          topologicalKrullDim W ≤ ((n - 1 : ℕ) : WithBot ℕ∞) ∧
            ∀ w : W, ringKrullDim (W.presheaf.stalk w) ≤ ((n - 1 : ℕ) : WithBot ℕ∞) := by
  sorry

/-- The same bounds after base change of an ordinary tower to a stalk spectrum.
No quasi-excellence, separation, rationality or finite-type hypothesis on X is needed.

Source: Temkin, section 4.3, Extensions 1,...,n, p. 30; Stacks 0805 and 081I
(blueprint: lem-per-blowup-local-dimension-bound).

Proof:
4. Choose an affine neighborhood of x. Its Noetherian coordinate ring has localization
   O_{X,x}, which is Noetherian by lem-weil-pbc-localization-noetherian and reduced by
   def-pc-reduced-scheme. The canonical map is flat by lem-sbc-canonical-stalk-spectrum-flat;
   each stage projection is flat by lem-weil-pbc-flat-morphism-base-change.
5. The open complement of a center is dense and quasi-compact by
   lem-sfb-noetherian-open-immersion-qc. Since its ambient stage is reduced by the induction
   of Step 1, lemma-nagata-reduced-dense-image-schematic makes it schematically dense.
   lemma-nagata-dense-flat-pullback preserves this density after the flat projection.
   def-nagata-blowup-flat-base-change-map and thm-nagata-blowup-flat-base-change identify
   each pulled-back arrow with the ordinary blowup of the extended ideal. The images of
   finite generators generate the extended ideal. Inductively all stages are Noetherian,
   so pqf-lem-coherent-ft-locnoeth makes their centers coherent. Empty pulled-back centers
   are allowed. Apply Steps 1--3 of blowup_local_dimension_bound to this tower.
-/
theorem blowup_stalk_dimension_bound
    (X : Scheme.{u}) [IsReduced X] [IsNoetherian X] (x : X)
    (n : ℕ) (hn : ringKrullDim (X.presheaf.stalk x) = (n : WithBot ℕ∞))
    (T : OrdinaryBlowupTower X)
    (hcoh : ∀ i : Fin T.length,
      RingedSpace.IsCoherent (T.level i.castSucc).toRingedSpace (T.center i).toModules)
    (hdense : ∀ i : Fin T.length,
      IsNowhereDense ((T.center i).support : Set (T.level i.castSucc))) :
    IsReduced (pullback (T.toBase (Fin.last T.length)) (X.fromSpecStalk x)) ∧
      IsNoetherian (pullback (T.toBase (Fin.last T.length)) (X.fromSpecStalk x)) ∧
      topologicalKrullDim
        (pullback (C := Scheme.{u}) (T.toBase (Fin.last T.length)) (X.fromSpecStalk x)) ≤
        (n : WithBot ℕ∞) ∧
      ∀ (W : Scheme.{u})
        (j : W ⟶ pullback (T.toBase (Fin.last T.length)) (X.fromSpecStalk x))
        [IsClosedImmersion j] [IsReduced W],
        IsNowhereDense (Set.range j) → 1 ≤ n →
          topologicalKrullDim W ≤ ((n - 1 : ℕ) : WithBot ℕ∞) ∧
            ∀ w : W, ringKrullDim (W.presheaf.stalk w) ≤ ((n - 1 : ℕ) : WithBot ℕ∞) := by
  sorry

/-- Quasi-excellence of local schemes, all stages, their local base changes, and
reduced closed subschemes. Reducedness and Noetherianness are retained as well.
The closed subschemes in this permanence assertion need not be nowhere dense.

Source: Temkin, section 4.3, p. 30; Stacks 07QU
(blueprint: lem-per-blowup-local-dimension-bound).

Proof:
6. As in Step 4, write the stalk as a localization of an affine coordinate ring.
   lem-per-quasi-excellent-localization makes it quasi-excellent. Its G-ring and J-2
   properties extend from the one affine chart of its spectrum to every affine open by
   lem-trf-g-ring-affine-cover and lem-trf-j2-affine-cover. Noetherianness on affine opens
   follows from pqf-lem-affine-open-locnoeth. These are exactly def-exc-excellent-ring.
7. Each blowup arrow is finite type by Step 1; apply
   lem-per-quasi-excellent-finite-type-stability successively both over X and over its
   stalk spectrum, using Step 5 for the latter tower. A closed immersion is affine-locally
   a quotient ring map (def-weil-closed-immersion), hence locally of finite type. Apply
   the same stability to every reduced closed subscheme. Noetherianness passes to closed
   subschemes; reducedness is assumed for them. This proves every asserted triple.
-/
theorem blowup_quasiExcellent
    (X : Scheme.{u}) [IsReduced X] [IsNoetherian X]
    (hqe : GabberModification.QuasiExcellent X) (T : OrdinaryBlowupTower X)
    (hcoh : ∀ i : Fin T.length,
      RingedSpace.IsCoherent (T.level i.castSucc).toRingedSpace (T.center i).toModules)
    (hdense : ∀ i : Fin T.length,
      IsNowhereDense ((T.center i).support : Set (T.level i.castSucc))) :
    (∀ x : X, IsReduced (Spec (X.presheaf.stalk x)) ∧
      IsNoetherian (Spec (X.presheaf.stalk x)) ∧
      GabberModification.QuasiExcellent (Spec (X.presheaf.stalk x))) ∧
    (∀ i : Fin (T.length + 1), IsReduced (T.level i) ∧ IsNoetherian (T.level i) ∧
      GabberModification.QuasiExcellent (T.level i) ∧
      ∀ (W : Scheme.{u}) (j : W ⟶ T.level i) [IsClosedImmersion j] [IsReduced W],
        IsNoetherian W ∧ GabberModification.QuasiExcellent W) ∧
    (∀ (x : X) (i : Fin (T.length + 1)),
      IsReduced (pullback (T.toBase i) (X.fromSpecStalk x)) ∧
      IsNoetherian (pullback (T.toBase i) (X.fromSpecStalk x)) ∧
      GabberModification.QuasiExcellent (pullback (T.toBase i) (X.fromSpecStalk x)) ∧
      ∀ (W : Scheme.{u}) (j : W ⟶ pullback (T.toBase i) (X.fromSpecStalk x))
        [IsClosedImmersion j] [IsReduced W],
        IsNoetherian W ∧ GabberModification.QuasiExcellent W) := by
  sorry

/-- Over Q the schemes above, and their reduced closed subschemes, are objects of
the existing reduced Noetherian quasi-excellent rational input category. The structure
maps are exactly the composites with the given map of X, recorded by heterogeneous
equality to accommodate the displayed equality of underlying schemes.

Source: Temkin, section 4.3, p. 30; Stacks 07QU
(blueprint: lem-per-blowup-local-dimension-bound).

Proof: Step 7 continues by composing X's rational structure map with the stalk-spectrum
map, tower projections, pullback projections and closed immersions. Steps 1 and 4--7,
as in blowup_quasiExcellent, give reducedness, Noetherianness and affine-local
quasi-excellence for each scheme. Package these properties and these particular composites
in QERationalResolutionInput. No choices of modifications or extra finiteness assumptions
are involved. A zero-length tower and an empty closed subscheme are included.
-/
theorem blowup_rationalInputs
    (X : Scheme.{u}) [IsReduced X] [IsNoetherian X]
    (hqe : GabberModification.QuasiExcellent X)
    (q : X ⟶ Spec (.of (ULift.{u} ℚ))) (T : OrdinaryBlowupTower X)
    (hcoh : ∀ i : Fin T.length,
      RingedSpace.IsCoherent (T.level i.castSucc).toRingedSpace (T.center i).toModules)
    (hdense : ∀ i : Fin T.length,
      IsNowhereDense ((T.center i).support : Set (T.level i.castSucc))) :
    (∀ x : X, ∃ D : QERationalResolutionInput.{u},
      D.scheme = Spec (X.presheaf.stalk x) ∧
        HEq D.structureMap (X.fromSpecStalk x ≫ q)) ∧
    (∀ i : Fin (T.length + 1), ∃ D : QERationalResolutionInput.{u},
      D.scheme = T.level i ∧ HEq D.structureMap (T.toBase i ≫ q)) ∧
    (∀ (i : Fin (T.length + 1)) (W : Scheme.{u}) (j : W ⟶ T.level i)
      [IsClosedImmersion j] [IsReduced W], ∃ D : QERationalResolutionInput.{u},
        D.scheme = W ∧ HEq D.structureMap (j ≫ T.toBase i ≫ q)) ∧
    (∀ (x : X) (i : Fin (T.length + 1)), ∃ D : QERationalResolutionInput.{u},
      D.scheme = pullback (T.toBase i) (X.fromSpecStalk x) ∧
        HEq D.structureMap
          (pullback.snd (T.toBase i) (X.fromSpecStalk x) ≫ X.fromSpecStalk x ≫ q)) ∧
    (∀ (x : X) (i : Fin (T.length + 1)) (W : Scheme.{u})
      (j : W ⟶ pullback (T.toBase i) (X.fromSpecStalk x))
      [IsClosedImmersion j] [IsReduced W], ∃ D : QERationalResolutionInput.{u},
        D.scheme = W ∧ HEq D.structureMap
          (j ≫ pullback.snd (T.toBase i) (X.fromSpecStalk x) ≫ X.fromSpecStalk x ≫ q)) := by
  sorry

end AlgebraicGeometry
