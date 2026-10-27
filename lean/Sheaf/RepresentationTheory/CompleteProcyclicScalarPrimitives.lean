/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
import Sheaf.NumberTheory.Padics.BanachTranslationDifferenceSplit
import Sheaf.RepresentationTheory.CompactOpenCoinducedContraction
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Algebra.Homology.HomologySequence

/-! # Higher continuous procyclic primitives with complete scalar coefficients

Source: the complete-coefficient argument in steps 2 and 3 of
`lem-sfb-procyclic-scalar-cochain-evaluation`, below paragraph (3) of the
six-functors direct-images proof. Stacks Tag 0DVG gives the cochain convention only.
(blueprint: lem-sfb-complete-procyclic-scalar-primitives).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace ContinuousCohomology

/-- A closed continuous scalar cochain of degree at least two has a continuous primitive
when the coefficient norm field is complete. The parameter may be empty and is retained
throughout; the equations concern actual functions, without closure of coboundaries.

Source: steps 2 and 3 of `lem-sfb-procyclic-scalar-cochain-evaluation`, the agent-written
scalar analytic input below paragraph (3) of the current blueprint direct-images proof.
(blueprint: lem-sfb-complete-procyclic-scalar-primitives).

Proof: The normed algebra over Q_l is ultrametric by
`IsUltrametricDist.of_normedAlgebra`. Give V=C(S,F) its supremum norm. It is complete,
and the pointwise strong triangle inequality gives the same inequality for this norm,
including S empty. Compact-open currying identifies C(S x H^q,F) with C(H^q,V), where
H=Z_l, and intertwines the signed face maps. Apply the Banach translation-difference
splitting to V. With R=C(H,V), constants c, difference Delta, and the continuous right
inverse T, postcomposition gives a degreewise short exact sequence of continuous
cochain complexes 0 -> C(H^bullet,V) -> C(H^bullet,R) -> C(H^bullet,R) -> 0.
The continuous section T proves surjectivity in each degree; evaluation at zero
identifies the kernel with V-valued cochains, also continuously. Both arrows commute
with the differential since c and Delta intertwine the translation actions.
The compact-open coinduced contraction makes both outside terms in the exact segment
H^(q-1)(H,R) -> H^q(H,V) -> H^q(H,R) zero for q>=2. Thus every closed V-valued
cochain is a boundary in the abstract vector-space complex. Its preimage is an actual
continuous cochain by the coordinate range conditions. Uncurry it to obtain the stated
primitive on S x H^(q-1). No completeness assertion is made for an algebraic closure.
-/
theorem complete_procyclic_scalar_primitives (ell : ℕ) [Fact ell.Prime]
    (F : Type u) [NormedField F] [NormedAlgebra ℚ_[ell] F] [CompleteSpace F]
    (S : Profinite.{v}) (n : ℕ) (z : C(S × (Fin (n + 2) → ℤ_[ell]), F))
    (hz : ∀ (s : S) (t : Fin (n + 3) → ℤ_[ell]),
      z (s, fun i ↦ t i.succ) +
        ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i.val + 1) •
          z (s, Fin.contractNth i (· + ·) t) = 0) :
    ∃ b : C(S × (Fin (n + 1) → ℤ_[ell]), F),
      ∀ (s : S) (t : Fin (n + 2) → ℤ_[ell]),
        b (s, fun i ↦ t i.succ) +
          ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i.val + 1) •
            b (s, Fin.contractNth i (· + ·) t) = z (s, t) := by
  sorry

end ContinuousCohomology
