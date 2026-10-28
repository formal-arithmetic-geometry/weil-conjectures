## What changed

Marked `WeilConjectures.integralSystemReduction_map_ext` as
`STATEMENT-DISPUTED`, preserving its signature and its original `sorry`.
The arbitrary-scheme statement has a genuine Milnor obstruction; the detailed
counterexample below is mathematical, not a Lean formalization of a counterexample.

Added the fully proved `integralSystemReduction_map_ext_of_finite` in the item
module. It adds the explicit finiteness assumption on
`Hom(A[1], Res_n Red_n B)`. Naturality of `integralSystemReductionEvaluation`
transports the evaluation equalities to scalar reduction. The existing proved
`derivedComplete_finiteReduction_ext` then gives equality of the underlying
maps, and applying coherent reduction finishes. This is a sufficient criterion,
not a proof or a decomposition of the disputed assertion.

Added one proof-only import, `Sheaf.Paper.DerivedCompleteFiniteReductionDetection`.
Corrected the existing node's truncated `lean.module` value (`MapEx` to `MapExt`)
and replaced its invalid proof plan with the obstruction analysis. No existing
signature, definition, instance, attribute, or public import changes.

Validation: the final item compiles without warnings in 3.2 seconds through
`lcompile.py`. The unchanged direct importer
`Sheaf.Paper.IntegralPullbackTensorCompositionReduced` also compiles against
the delivered item in 4.4 seconds (the item in that run took 6.3 seconds). Its
temporary sandbox copy was removed after verification. Delivery also performs
its own consumer and axiom checks.

## Proved and sorry left

Original holes closed: **0 of 1**. Holes added: **0**. Split off: **0**.

The one remaining hole is
`WeilConjectures.integralSystemReduction_map_ext`, node
`lem-pur-integral-system-reduction-map-ext`. It remains disputed and unproved;
no weaker theorem has silently replaced it.

The added theorem `WeilConjectures.integralSystemReduction_map_ext_of_finite`,
node `lem-pur-integral-system-reduction-map-ext-finite`, has a complete Lean proof
and no new holes. Its proof uses the already proved generic detection theorem;
it does not use the disputed theorem.

## No longer needed

None. No existing imports, nodes, modules, or unit steps are pruned. In particular,
the current parent `IntegralPullbackTensorCompositionReduced` still calls the
disputed assertion, so withdrawing this module would be incorrect. No additional
proof-dependency `sorry` has been introduced.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the proposed argument confuses conservative evaluation of
objects with faithful evaluation of derived morphisms. Localization at
levelwise quasi-isomorphisms does not identify derived morphisms with families
of their images in the component derived categories. The coherent system can
retain a nonzero morphism whose separate evaluations are all zero.

The precise obstruction is in Stacks Project, `more-algebra.tex`, Lemma
`map-into-Rlim`: for a derived-complete target B, the kernel of

    Hom(A, B) -> lim_n Hom(A, Res_n Red_n B)

is `lim^1_n Hom(A[1], Res_n Red_n B)`. The existing finite-field and
algebraically closed finite-type geometric theorems supply hypotheses that
kill this group. The assigned assertion quantifies over every scheme where
ell is invertible, and supplies none of these hypotheses.

Here is an explicit counterexample over `X = Spec Q`, with `ell = 3`,
`E = Q_3`, `A = Z_3`, and `B = Z_3[2]` on the pro-etale site. These are
derived-complete constructible objects: their reductions are the constant
finite coefficient sheaves, in degrees 0 and -2 respectively. Their reduction
supports are uniformly bounded. Three is invertible on X.

Write `G_n = H^1_et(Q, Z/3^(n+1))`, with the coefficient reduction transitions.
For each r >= 1, choose a distinct prime p_r with `v_3(p_r - 1) = r`.
Dirichlet's theorem supplies such primes in the progression
`1 + 3^r modulo 3^(r+1)`. The degree `3^r` subextension of `Q(zeta_(p_r))`
defines a character `chi_r : G_Q -> Z/3^r`, ramified only at p_r and nonzero
modulo 3 on inertia there.

For any N > r, every character `G_Q -> Z/3^N` has zero reduction modulo 3
on inertia at p_r. Indeed wild inertia is pro-p_r, so its image in a 3-group
is zero. The tame relation `sigma tau sigma^-1 = tau^(p_r)` implies
`(p_r - 1) chi(tau) = 0`. Thus its inertia image is killed by `3^r`, hence
lies in `3^(N-r) Z/3^N`, whose reduction modulo 3 is zero.

Now take the element `(chi_(n+1))_n` in `product_n G_n`. It is not in the
image of the Roos difference map `1 - shift`. Otherwise write
`chi_(n+1) = z_n - red(z_(n+1))` and telescope down to `G_0`. For each fixed
r, telescope beyond level r. All terms except `chi_r` are unramified at p_r,
and the terminal higher-level character has zero mod-3 inertia there by the
preceding paragraph. Therefore z_0 is ramified at every p_r. This is impossible:
a continuous finite character of G_Q factors through a finite extension,
which ramifies at only finitely many primes. Consequently `lim^1 G_n` is nonzero.
This directly constructs the obstruction; no countability criterion for
Mittag-Leffler towers is needed.

Apply the Milnor exact sequence to the derived limit presentation of
`B = Z_3[2]`. Its shifted Hom tower is precisely `G_n` (finite-torsion
pro-etale and etale H^1 agree). A nonzero element of `lim^1 G_n` gives a
nonzero map `a : A -> B` whose composite with every reduction unit is zero.
By scalar extension/restriction adjunction, every derived scalar reduction
of a is zero. Naturality of `integralSystemReductionEvaluation` makes every
finite evaluation of coherent reduction of a zero as well. But coherent
reduction is faithful on these objects by
`integralSystemReduction_fullyFaithful`, so its image of a is nonzero.
Taking `p = a` and `q = 0` contradicts exactly the assigned conclusion.

The local tame relation used above is also recorded in
[Moakher, The Taylor-Wiles-Kisin method, proof of Lemma 2.5.4](https://www.math.univ-paris13.fr/~moakher/Rapportfinal-M2.pdf);
the Milnor exact sequence is in the local Stacks source just cited. The
counterexample's Roos calculation is given explicitly above rather than
attributed to a source that does not state it.

The sole direct importer,
`Sheaf.Paper.IntegralPullbackTensorCompositionReduced`, uses the disputed lemma
to pass from its evaluated equations to a coherent-system equation. That proof
requires a repair. For its particular canonical maps, a plausible repair is
to compare normalized whole-system representatives before localization. Merely
adding the finite-Hom hypothesis to that parent would alter its theorem and
would not be a justified repair for arbitrary schemes. The present delivery
preserves all consumers and reports the defect for independent review.

## New nodes

`lem-pur-integral-system-reduction-map-ext-finite` records the fully proved
finite shifted-Hom criterion in the item module. Its dependencies are the
existing coherent-reduction comparison and generic complete-object scalar
reduction detection theorem. It is not a split-off `sorry`, and does not
claim to close the disputed parent node. The original unit route is unchanged.

Change record: `coord/changes/Q1-integral-system-reduction-map-ext-dispute.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralSystemReductionMapExt": "1446321741f7f31c66ee4572abf6db4a1a2ac0c3"}, "results": {"Sheaf.Paper.IntegralPullbackTensorCompositionReduced": {"hash": "1ae82b80992d4412acd53bd91e60b963840ee7f4", "status": "OK"}}, "seconds": 131, "time": "2026-10-28T12:06:38+0800", "transitive": 0, "version": 1}
```

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
