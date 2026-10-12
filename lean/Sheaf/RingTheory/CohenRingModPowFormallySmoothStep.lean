module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Data.ZMod.Basic
public import Sheaf.RingTheory.CohenRing

@[expose] public section

universe u

namespace IsDiscreteValuationRing

/-- The induction step for formal smoothness of a Cohen ring modulo a prime power.
Source: Stacks Project, Algebra, Lemma Tag 0329, using Lemma Tag 031L.
(blueprint: lem-weil-pbc-cohen-ring-mod-pn-formally-smooth-step)

Let R = Z/p^(n+1), S = Λ/(p^(n+1)), and I = (p^n) in R. Since n ≥ 1,
2n ≥ n+1, so I² = 0. A Cohen ring is torsion-free over ℤ: write each nonzero
integer as ±p^a b with p not dividing b. Bezout's identity makes b a unit in the
local ring whose maximal ideal is (p), and p is nonzero since it generates the
nonzero maximal ideal of a DVR. The domain property gives torsion-freeness.
Torsion-free modules over the PID ℤ are flat, and base change makes S flat over R.
The quotients R/I and S/IS are Z/p^n and Λ/(p^n), respectively, because
(p^(n+1)) is contained in (p^n). Their induced map is formally smooth by the
hypothesis. Apply the flat square-zero quotient criterion (Tag 031L) to obtain
formal smoothness of R → S. The ZMod-algebra structures are unique since every
class is an integer cast, so the conclusion holds for every such structure. -/
theorem cohenRing_mod_pow_formallySmooth_step
    (p : ℕ) (Λ : Type u) [CommRing Λ] (hΛ : IsCohenRing p Λ)
    (n : ℕ) (hn : 1 ≤ n)
    (ih : ∀ [Algebra (ZMod (p ^ n)) (Λ ⧸ Ideal.span {(p : Λ) ^ n})],
      Algebra.FormallySmooth (ZMod (p ^ n)) (Λ ⧸ Ideal.span {(p : Λ) ^ n})) :
    ∀ [Algebra (ZMod (p ^ (n + 1))) (Λ ⧸ Ideal.span {(p : Λ) ^ (n + 1)})],
      Algebra.FormallySmooth (ZMod (p ^ (n + 1)))
        (Λ ⧸ Ideal.span {(p : Λ) ^ (n + 1)}) := by
  sorry

end IsDiscreteValuationRing
