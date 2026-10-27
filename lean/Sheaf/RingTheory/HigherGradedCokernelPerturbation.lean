module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Sheaf.RingTheory.HigherAdicGraded

/-!
# Higher graded cokernels of close finite free complexes

Source: ILO, Travaux de Gabber, Expose III, Proposition 4.5(iii)--(iv), pp.39--41;
Stacks, Tag 07VE, first proof paragraph
(blueprint: lem-per-higher-graded-cokernel-perturbation).

We specify graded module and algebra isomorphisms by their underlying linear
equivalence, the homogeneous representative formula, and preservation of the
concrete scalar action, multiplication, and unit. This avoids any dependence on
a choice of bundled ring-law proofs for the higher graded construction. The
representative formula specifies the identity-induced map and preserves degrees.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace Ideal

/-- Higher-width graded cokernel comparison.
Source: ILO, Expose III, Proposition 4.5(iii), pp.39--41, using only the finite
adjustment in Stacks Tag 07VE (blueprint: lem-per-higher-graded-cokernel-perturbation).

Proof: The differences land in `I^(c+1)`. If `p'(x)` lies in `I^j F`, put `k=j-c`
and successively adjust `x` by elements of `range r'` to obtain `x_t` in `I^t M`,
for `0 <= t <= k`, without changing `p'(x_t)`. Given `t<k`, the difference estimate
puts `p(x_t)` in `I^(t+c+1)F`. Artin--Rees for `p` gives `v` in `I^(t+1)M` with
`p(v)=p(x_t)`. Exactness gives `b` with `r(b)=x_t-v`; if `t>=c`, Artin--Rees for
`r` permits `b` in `I^(t-c)L`. Put `x_(t+1)=x_t-r'(b)=v+(r-r')(b)`. In both
`t>=c` and `t<c` the last expression lies in `I^(t+1)M`. The equality `p'r'=0`
preserves its image, and the accumulated adjustment remains in `range r'`.
At `t=k` this transfers the Artin--Rees bound to `p'`, without Krull intersection.

Put `a=n+1-c`. For `q<=c`, replace `p(x)` by `p'(x)`; their difference lies in
`I^(n+1)F`, hence in `I^(q+a)F`. Interchange the maps for the reverse inclusion.
For `q>c`, lift an element of `range p` in `I^qF` to `I^(q-c)M` using its bound;
the difference of its two images lies in `I^(n+1+q-c)F=I^(q+a)F`. Use the
transferred bound for the reverse inclusion. This proves the submodule equality.

The quotient map onto `F/range p` sends `I^qF` onto `I^q(F/range p)`.
The kernel of its map to the width-`a` piece is the intersection with
`I^(q+a)F + (I^qF intersect range p)`. The equality just proved therefore gives
bijective linear maps of all pieces sending the class of `x` to the class of `x`.
Take their direct sum. On homogeneous representatives, scalar multiplication on
both sides is represented by `b*x`; distribute over finite sums to obtain the
asserted action compatibility. Integer powers are interpreted using `toNat`,
so these arguments include all nonpositive degrees. -/
theorem higherGradedCokernelPerturbation
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {L : Type v} [AddCommGroup L] [Module B L] [Module.Free B L] [Module.Finite B L]
    {M : Type w} [AddCommGroup M] [Module B M] [Module.Free B M] [Module.Finite B M]
    {F : Type z} [AddCommGroup F] [Module B F] [Module.Free B F] [Module.Finite B F]
    (r r' : L →ₗ[B] M) (p p' : M →ₗ[B] F)
    (hexact : LinearMap.range r = LinearMap.ker p) (hcomplex : p'.comp r' = 0)
    (c n : ℕ) (hn : c ≤ n)
    (hr : ∀ j : ℤ, (c : ℤ) ≤ j →
      LinearMap.range r ⊓ intAdicPower I M j ≤
        (intAdicPower I L (j - c)).map r)
    (hp : ∀ j : ℤ, (c : ℤ) ≤ j →
      LinearMap.range p ⊓ intAdicPower I F j ≤
        (intAdicPower I M (j - c)).map p)
    (hrr' : LinearMap.range (r - r') ≤ intAdicPower I M (n + 1))
    (hpp' : LinearMap.range (p - p') ≤ intAdicPower I F (n + 1)) :
    (∀ q : ℤ,
      intAdicPower I F (q + (n + 1 - c : ℕ)) ⊔
          (intAdicPower I F q ⊓ LinearMap.range p) =
        intAdicPower I F (q + (n + 1 - c : ℕ)) ⊔
          (intAdicPower I F q ⊓ LinearMap.range p')) ∧
    ∃ e : higherAdicGraded I (F ⧸ LinearMap.range p) (n + 1 - c) ≃ₗ[B]
        higherAdicGraded I (F ⧸ LinearMap.range p') (n + 1 - c),
      (∀ (q : ℤ) (x : F), x ∈ intAdicPower I F q →
        e (higherAdicClass I (F ⧸ LinearMap.range p) (n + 1 - c) q
            ((LinearMap.range p).mkQ x)) =
          higherAdicClass I (F ⧸ LinearMap.range p') (n + 1 - c) q
            ((LinearMap.range p').mkQ x)) ∧
      (∀ (b : higherAdicGraded I B (n + 1 - c))
          (x : higherAdicGraded I (F ⧸ LinearMap.range p) (n + 1 - c)),
        e (higherAdicAction I (F ⧸ LinearMap.range p) (n + 1 - c) b x) =
          higherAdicAction I (F ⧸ LinearMap.range p') (n + 1 - c) b (e x)) := by
  sorry

/-- The same canonical comparison is an algebra isomorphism when the final module
is `B`. Source: ILO, Expose III, Proposition 4.5(iv), pp.39--41
(blueprint: lem-per-higher-graded-cokernel-perturbation).

Proof: Apply the preceding comparison with `F=B`, with exactly the same exactness,
Artin--Rees and congruence hypotheses. Its homogeneous representative formula
uniquely determines the map, so this is the same isomorphism as in (iii). The two
images are ideals because the maps are `B`-linear. On homogeneous representatives,
multiplication in both quotient rings sends the classes of `x,y` to that of `xy`;
the representative formula thus proves multiplication compatibility. The unit is
the degree-zero class of `1`, so it is preserved as well. Distribute over the
finite homogeneous supports to get compatibility for arbitrary elements. Scalar
compatibility is already supplied by (iii). -/
theorem higherGradedCokernelPerturbation_algebra
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {L : Type v} [AddCommGroup L] [Module B L] [Module.Free B L] [Module.Finite B L]
    {M : Type w} [AddCommGroup M] [Module B M] [Module.Free B M] [Module.Finite B M]
    (r r' : L →ₗ[B] M) (p p' : M →ₗ[B] B)
    (hexact : LinearMap.range r = LinearMap.ker p) (hcomplex : p'.comp r' = 0)
    (c n : ℕ) (hn : c ≤ n)
    (hr : ∀ j : ℤ, (c : ℤ) ≤ j →
      LinearMap.range r ⊓ intAdicPower I M j ≤
        (intAdicPower I L (j - c)).map r)
    (hp : ∀ j : ℤ, (c : ℤ) ≤ j →
      LinearMap.range p ⊓ intAdicPower I B j ≤
        (intAdicPower I M (j - c)).map p)
    (hrr' : LinearMap.range (r - r') ≤ intAdicPower I M (n + 1))
    (hpp' : LinearMap.range (p - p') ≤ intAdicPower I B (n + 1)) :
    ∃ e : higherAdicGraded I (B ⧸ LinearMap.range p) (n + 1 - c) ≃ₗ[B]
        higherAdicGraded I (B ⧸ LinearMap.range p') (n + 1 - c),
      (∀ (q : ℤ) (x : B), x ∈ intAdicPower I B q →
        e (higherAdicClass I (B ⧸ LinearMap.range p) (n + 1 - c) q
            ((LinearMap.range p).mkQ x)) =
          higherAdicClass I (B ⧸ LinearMap.range p') (n + 1 - c) q
            ((LinearMap.range p').mkQ x)) ∧
      (∀ (b : higherAdicGraded I B (n + 1 - c))
          (x : higherAdicGraded I (B ⧸ LinearMap.range p) (n + 1 - c)),
        e (higherAdicAction I (B ⧸ LinearMap.range p) (n + 1 - c) b x) =
          higherAdicAction I (B ⧸ LinearMap.range p') (n + 1 - c) b (e x)) ∧
      (∀ (x y : higherAdicGraded I (B ⧸ LinearMap.range p) (n + 1 - c)),
        e (higherAdicQuotientMul I (LinearMap.range p) (n + 1 - c) x y) =
          higherAdicQuotientMul I (LinearMap.range p') (n + 1 - c) (e x) (e y)) ∧
      e (higherAdicQuotientOne I (LinearMap.range p) (n + 1 - c)) =
        higherAdicQuotientOne I (LinearMap.range p') (n + 1 - c) := by
  sorry

end Ideal
