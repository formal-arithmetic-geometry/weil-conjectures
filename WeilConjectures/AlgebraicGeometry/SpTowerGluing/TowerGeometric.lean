/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage

/-!
# The geometric adjunction on coefficient towers

This is the Lean statement of Proposition 10.17 in the current blueprint.  The
categories `SpTowerCalculus.C` are the unnormalised constructible finite-Tor
tower categories from `sk-def-sp-normalized-towers`, and `support` is the
compact-support functor from `sk-lem-sp-tower-bound`.  The `Levels` record
contains the finite adjunctions, their evaluation comparisons, and the actual
coefficient-reduction mate formula.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-prop-sp-tower-geometric/_section.md`, Proposition 10.17.
(blueprint: sk-prop-sp-tower-geometric)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- In the standing characteristic-`p` setting, compact support on unnormalised
constructible coefficient towers has a right adjoint.  Its finite evaluations
are the finite exceptional inverse images and its transitions are the canonical
coefficient-reduction mates (including the scalar-unitor case `m = n`).

The implementation packages these finite-level and transition assertions in
`Levels`; its `comparison`, `adjunction`, `counit`, `unit`, and `reduction`
fields are exactly the corresponding clauses of Proposition 10.17.
Source: current blueprint Proposition 10.17, as recorded by this node's
`blueprint_update` at commit a2fea16eed3e719689ac4c5330c89ea8d7bd7ab6.
The fixed interfaces are def-sp-tower-shriek-data,
def-sp-coefficient-tower-shriek-interfaces, and def-sp-tower-gluing-interfaces.

Proof:
1. Apply sk-lem-sp-tower-bound to the compactification functor F. It preserves
   uniform constructible finite-Tor bounds and evaluates to finite compact support.
   Exact evaluations from det-sp-coefficient-towers-abelian compute cohomology
   levelwise, so the common lower bound places every input in D+(Tow).
2. Since ell is invertible, det-sp-tower-classes supplies the exact tower Kummer
   sequence, coefficient-linear Chern and diagonal classes, and the projective-line
   splitting b_q. Twist and shift b_q inverse, then project to its second summand
   to obtain the trace as one derived-tower morphism with its finite evaluations.
3. Apply det-sp-tower-p1-adjunction. The projection formula followed by tensoring
   with the trace gives its counit; the diagonal class gives its unit. Their
   triangle identities hold in D(Tow), and the adjunction restricts to the uniformly
   constructible finite-Tor tower categories.
4. Apply det-sp-tower-gluing to the local chart representing pairs. Induction on
   a finite cover glues the pairs by the open-cover cone and the exact Hom sequence;
   the five lemma proves representability and the union of the local intervals
   gives uniform bounds. For u : C -> D define G(u) as the unique a with
   F(a) followed by epsilon_D equal to epsilon_C followed by u. The representing
   bijections give existence, uniqueness, identities and composition, and hence
   the adjunction F left adjoint to G.
5. The finite evaluation clause of det-sp-tower-gluing identifies G(C)_n with the
   finite exceptional inverse image, compatibly with both units and counits.
   Transposing the tower counit's transition identity gives its actual reduction
   as the coefficient mate followed by the finite right adjoint of C's reduction.
   This mate and c of sk-lem-sp-reduction are the unique transpose of the same
   scalar-extended counit after inverse compact-support comparison; thus they
   coincide. Equal indices use the scalar unitor, so m = n is included.
(blueprint: sk-prop-sp-tower-geometric) -/
theorem sp_tower_geometric
    (pchar : ℕ) (_hp : 0 < pchar) (_hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left] :
    ∃ hF : ∀ M : SpTowerCalculus.C l E b q X.left,
        spConstructibleTorTowers l E Y.left (q.abelian Y.left)
          ((SpTowerCalculus.F l E b o q
            (CondensedRing.compactificationOverField f)).obj M.obj),
      ∃ G : SpTowerCalculus.C l E b q Y.left ⥤ SpTowerCalculus.C l E b q X.left,
      ∃ adj : support l E b o q (CondensedRing.compactificationOverField f) hF ⊣ G,
        Nonempty (Levels l E b o q (CondensedRing.compactificationOverField f)
          hF G adj) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerGluing
