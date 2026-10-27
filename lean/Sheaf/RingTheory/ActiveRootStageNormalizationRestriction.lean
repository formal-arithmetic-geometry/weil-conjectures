/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.ActiveRootNormalizationData
public import WeilConjectures.RingTheory.ProEtale.IndEtale

/-! # Restricting a finite-stage splitting to the actual normalization

Source: Stacks, Tag 0CBF; ILO IX Proposition 2.1, pp.133--134.
(blueprint: lem-sfb-active-root-stage-normalization-restriction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace Algebra.ActiveRootNormalization

/-- A fixed-stage active-root splitting restricts to the actual base-changed closure.
Source: Stacks, Tag 0CBF, lemma-integral-closure-commutes-colim-smooth, and the
coordinatewise monic-equation argument of the parent node, steps 7--8.
(blueprint: lem-sfb-active-root-stage-normalization-restriction).

Proof: send each active root z_i to the image of the full root x_(active i) in S_m,
and coefficients through A -> S_m. These images satisfy the defining monic equations,
so polynomial evaluation descends to T_m -> S_m. The pushout defining puncturing
extends it to k: Q_m -> S_m[1/f], with the two displayed generator equations. Extend
theta_m along k; associativity of tensor pushouts identifies its source with
strictAmbient, while finite products commute with scalar extension by the coordinate
idempotent formulas. This gives Theta, agreeing on D as displayed. The base change
C_m -> S_m of B -> A is ind-etale. Apply 0CBF to the ambient algebra D_m, so the
canonical inclusion of the actual base change of E_m identifies it with the integral
closure of S_m in strictAmbient. Under Theta an integral tuple has integral coordinates,
by applying projections to its monic equation. The assumed integral-closedness formula
places each coordinate in S_m; injectivity of its puncture makes these lifts unique.
Conversely every tuple of lifted coordinates is integral, since each entry is integral
and a finite product of integral algebras is integral (equivalently use the product of
X-a_j). For d=0 the target is the zero ring, whose sole element is annihilated by X.
Thus Theta restricts to a bijective S_m-algebra map to S_m^d. Its induced isomorphism
is epsilon, and the canonical comparison formula s tensor e maps to s tensor e gives
exactly the final equality of ambient inclusions. No regularity, cover degree, roots
of unity, finiteness of D, or geometric-point assumption enters this fixed-stage step. -/
theorem activeRootStage_normalization_restriction
    {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r s : ℕ} (t : Fin r → B) (active : Fin s → Fin r) (p : ℕ)
    (m : RootTowerIndex {n : ℕ+ | Nat.Coprime (n : ℕ) p})
    (hA : (algebraMap B A).IndEtale)
    (hinj : Function.Injective (strictPuncture (A := A) t m.1).hom)
    (hclosure : ∀ x : asAlgebra (strictPuncture (A := A) t m.1),
      IsIntegral (strictStage (A := A) t m.1).right x ↔
        ∃ a : (strictStage (A := A) t m.1).right,
          (strictPuncture (A := A) t m.1).hom a = x)
    (D : Under (CommRingCat.of (Localization.Away (∏ i, t i)))) (d : ℕ)
    (theta_m : extend D ((activeDiagram (A := A) t active p).obj m) ≅
      diagonal ((activeDiagram (A := A) t active p).obj m).right d) :
        ∃ k : (activeDiagram (A := A) t active p).obj m ⟶
            strictPunctureOverBase (A := A) t m.1,
          (∀ a : A,
            k.right (activeInclusion (A := A) t active p m
              (algebraMap A _ a)) =
                (strictPuncture (A := A) t m.1).hom ((strictStage (A := A) t m.1).hom a)) ∧
          (∀ i : Fin s,
            k.right (activeInclusion (A := A) t active p m
              (simultaneousRoot (fun i ↦ algebraMap B A (t (active i))) m.1 i)) =
              (strictPuncture (A := A) t m.1).hom
                (strictStageMap (A := A) t m.1 (simultaneousRoot t m.1 (active i)))) ∧
          ∃ Theta : strictAmbient (A := A) t m.1 D ≅
              (Under.map (strictPuncture (A := A) t m.1).hom).obj
                (diagonal (strictPuncture (A := A) t m.1).right d),
            (∀ (x : D.right) (j : Fin d),
              Theta.hom.right (strictAmbientInclusion (A := A) t m.1 D x) j =
                k.right (theta_m.hom.right (extendInclusion D _ x) j)) ∧
            ∃ epsilon : strictClosure (A := A) t m.1 D ≅
                diagonal (strictStage (A := A) t m.1).right d,
              ((Under.pushout (strictStageMap (A := A) t m.1)).map
                  (closureInclusion (ambient t m.1 D))).right ≫ Theta.hom.right =
                epsilon.hom.right ≫
                  diagonalLocalization (strictPuncture (A := A) t m.1) d := by sorry

end Algebra.ActiveRootNormalization
