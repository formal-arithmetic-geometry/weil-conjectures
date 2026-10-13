/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.Paper.EtaleCEStationaryPageNaturality

/-! # Stationary CE comparisons at outer filtration bounds

Source: Stacks Project, Tag 012K, cycle and boundary formulas and graded cohomology.
(blueprint: lem-weil-pbc-ce-stationary-comparisons-at-bounds).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option maxHeartbeats 1000000 in
-- Elaborate the dependent presentation, page-realization and comparison families together.
/-- Stationary comparison naturality whenever the two outer filtration steps stabilize.
There is no support assumption, first-page formula, augmentation, or inverse-image lift.
Source: Stacks Project, Tag 012K, formulas for cycles, boundaries and graded cohomology;
explicit outer-step version of steps 4--5 of lem-weil-pbc-supported-ce-filtered-totals.
(blueprint: lem-weil-pbc-ce-stationary-comparisons-at-bounds).

Proof. Replace the outer steps in the cycle and boundary formulas by bottom and top.
The resulting quotient is the quotient of actual cycles in step q by cycles in step
q+1 and total boundaries lying in step q. Map it to the successive quotient of the
cohomology images of the two steps. Its kernel is exactly those cycles and boundaries,
and it is surjective, yielding the canonical quotient-to-image isomorphism. Transport
it along D.c n and use D.H_formula, then compose with e. This constructs eInf from
representative equations, not an arbitrary isomorphism; proof irrelevance identifies
all witnesses of the outer equalities.
For a filtered total map b, restrict its homology map to each cohomology image and
transport along the c-isomorphisms, obtaining t and ht. Inclusion compatibility
follows by cancelling the target step arrow. The page-map representative hypothesis
and the canonical comparison send each actual cycle to the same image under b.
The projections from actual cycles onto stationary page quotients are epimorphic;
cancel them to prove the cokernel.map equation. Proof irrelevance removes the choice
of hc. Zero totals and zero steps use the same quotient universal properties. -/
theorem exists_etaleCE_stationary_comparisons_at_bounds
    (D : ∀ (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
      EtaleTermwiseHypercohomology X K)
    (e : ∀ (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
      EtaleCEQuotientRealization (D X K)) :
    ∃ (eInf : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (q n r : ℤ) (hr : 1 ≤ r) (hR : (D X K).L.complexStep (q + r) (n + 1) = ⊥ ∧
          (D X K).L.complexStep (q - r + 1) (n - 1) = ⊤),
        ((D X K).sequence.page r hr).X (q, n - q) ≅ ((D X K).H n).gradedPiece q),
      ∀ {X Y : Scheme.{u}}
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (b : (D X K).sectionsTotal ⟶ (D Y L).sectionsTotal)
        (N : (D X K).sequence ⟶ (D Y L).sequence),
        (∀ q : ℤ, ∃ s : ((D X K).L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ) ⟶
            ((D Y L).L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ),
          s ≫ ((D Y L).L.step q).arrow = ((D X K).L.step q).arrow ≫ b) →
        EtaleCEPageMapOnRepresentatives (D X K) (D Y L) (e X K) (e Y L) b N →
          ∀ n : ℤ,
            ∃ (t : ∀ q : ℤ, (((D X K).H n).step q : AddCommGrpCat.{u + 1}) ⟶
            (((D Y L).H n).step q : AddCommGrpCat.{u + 1}))
          (ht : ∀ q : ℤ, t q ≫ (((D Y L).H n).step q).arrow =
            (((D X K).H n).step q).arrow ≫
              (((D X K).c n).inv ≫
                HomologicalComplex.homologyMap
                  b n ≫ ((D Y L).c n).hom)),
          ∀ (hc : ∀ q : ℤ,
            Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))) ≫ t q =
              t (q + 1) ≫
                Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                  (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q)))),
          ∀ (q r : ℤ) (hr : 1 ≤ r) (hX : (D X K).L.complexStep (q + r) (n + 1) = ⊥ ∧
            (D X K).L.complexStep (q - r + 1) (n - 1) = ⊤)
          (hY : (D Y L).L.complexStep (q + r) (n + 1) = ⊥ ∧
            (D Y L).L.complexStep (q - r + 1) (n - 1) = ⊤),
            (N.hom r hr).f (q, n - q) ≫ (eInf Y L q n r hr hY).hom =
              (eInf X K q n r hr hX).hom ≫
                cokernel.map
                  (Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                    (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                    (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (t (q + 1)) (t q) (hc q) := by sorry

end AlgebraicGeometry.Etale
