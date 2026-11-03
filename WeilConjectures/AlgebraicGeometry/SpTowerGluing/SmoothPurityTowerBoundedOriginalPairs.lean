/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.SpTowerChartCounit.SmoothPurityTowerChartCounit

/-! # Bounded representing pairs in the original tower coordinates

Source: latest blueprint, smooth tower gluing, Local pairs, Gluing and Uniformity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- Objectwise smooth compact-support representability, retaining every common interval.
Source: latest blueprint `sk-prop-sp-tower-geometric-gluing.proof.md`, Local pairs,
Gluing and Uniformity; the fibre correction in repair note bpq #42
(blueprint: lem-sp-tower-bounded-original-representing-pairs).

Proof. Choose a finite smooth coordinate cover. Restrict the normalized projective-line
adjunction to the affine line by the open adjunction, iterate along the ordered affine
projections and compose with the etale fibre-sum adjunction. Use compact-support
compositors and section-preserving realizations to obtain the local pairs for the given
operations. Their cohomological and Tor intervals are those of K shifted by -2d.
Restrict pairs by open adjunction and the canonical open compact-support compositor.
Transpose the two counits on each overlap to obtain mutually inverse comparison maps;
injectivity proves counit preservation and the cocycle relation. For a binary union take
the fibre, namely Cone[-1], of Rj_U*H_U plus Rj_V*H_V to Rj_W*H_W, whose arrows are the
restriction units and the overlap comparison with the second component negated.
The split local triangles identify its restrictions with the given local objects.
Exact restriction and levelwise evaluation retain the common cohomological interval;
constructibility and each Tor interval are local on the open cover. Apply compact support
to the open-extension triangle of this object. Counit compatibility annihilates its first
arrow, so Hom exactness lifts the sum of the local counits to eps. For each test M the
open-extension triangle and its rotations give the two Hom exact sequences. The exterior
comparison maps are the local representing bijections, including shifted tests, and the
five lemma gives the global bijection. Induct over the finite cover. On the empty source
use the zero object and the unique counit. This construction determines a representing
pair independently of a choice of interval: the same pair has every shifted interval
satisfied by K, by its fixed local identifications and locality of those bounds.
No functor on K, further-chart comparison or coefficient-level adjunction is asserted. -/
theorem tower_bounded_original_representing_pairs
    (pchar : ℕ) [Fact pchar.Prime]
    (k : Type u) [Field k] [CharP k pchar] (hne : pchar ≠ l)
    (x : SpTowerShriek.OpenExchange l E b o) (laws : SpTowerShriek.Laws l E b o x)
    (g : GraphCoordinates l E b o)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (t : ∀ r : ℕ, SpCoordinateAdjunction.ProjectivePresentation l E b o
      (affineTraceTower Y.left r))
    (hF : ∀ M : SpTowerCalculus.C l E b q X.left,
      spConstructibleTorTowers l E Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F l E b o q
          (CondensedRing.compactificationOverField f)).obj M.obj)) :
    ∀ K : SpTowerCalculus.C l E b q Y.left,
      ∃ (H : SpTowerCalculus.C l E b q X.left)
        (eps : (support l E b o q (CondensedRing.compactificationOverField f) hF).obj H ⟶ K),
      (∀ M : SpTowerCalculus.C l E b q X.left,
        Function.Bijective (fun a : M ⟶ H ↦
          (support l E b o q (CondensedRing.compactificationOverField f) hF).map a ≫ eps)) ∧
      ∀ (lo hi lt ht : ℤ),
        (∀ n : ℕ,
          proEtaleCohomologicalSupport
              ((spDerivedCoefficientEvaluation l E Y.left (q.abelian Y.left) n).obj K.obj) ⊆
            Set.Icc lo hi ∧
          HasProEtaleTorAmplitude Y.left (SpTowerShriek.R l E n)
            ((spDerivedCoefficientEvaluation l E Y.left (q.abelian Y.left) n).obj K.obj)
            lt ht) →
        ∀ n : ℕ,
          proEtaleCohomologicalSupport
              ((spDerivedCoefficientEvaluation l E X.left (q.abelian X.left) n).obj H.obj) ⊆
            Set.Icc (lo - 2 * (d : ℤ)) (hi - 2 * (d : ℤ)) ∧
          HasProEtaleTorAmplitude X.left (SpTowerShriek.R l E n)
            ((spDerivedCoefficientEvaluation l E X.left (q.abelian X.left) n).obj H.obj)
            (lt - 2 * (d : ℤ)) (ht - 2 * (d : ℤ)) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerGluing
