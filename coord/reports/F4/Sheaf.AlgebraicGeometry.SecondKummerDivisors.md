## What changed

Proved `AlgebraicGeometry.IsCurve.exists_addEquiv_secondKummer_divisors` in
`Sheaf.AlgebraicGeometry.SecondKummerDivisors`. Brauer vanishing makes the canonical
Kummer boundary surjective. Compose it with the canonical Picard group isomorphism,
transport the multiplication-by-n kernel, and apply the first isomorphism theorem.
The resulting inverse equivalence sends the boundary of every Picard class to its
quotient class. Proof irrelevance gives compatibility for every invertibility proof.
The theorem signature and all definitions are unchanged. Updated the node proof to
record use of the existing canonical Kummer exactness API.

The final single-file server compile passes. The argument uses no smoothness,
properness, connectedness, reducedness, or nonemptiness. For n = 1, the kernel is
the whole Picard group, as required; empty and zero-dimensional curves require no
extra hypotheses. n = 0 is excluded by the existing field hypothesis hn.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.IsCurve.exists_addEquiv_secondKummer_divisors`
(node `lem-sc-second-kummer-divisors`). 1 of 1 holes closed; 0 holes added;
0 split-offs; no sorry remains in the delivered module. This uses the existing
Brauer-vanishing theorem and the already proved canonical Kummer exactness theorem;
no claim is made that all their transitive dependencies are sorry-free.

## No longer needed

Removed proof imports:
- `WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder`:
  the existing `Scheme.exact_sheafH_rootsOfUnitySheaf_two` gives exactly the
  canonical-boundary kernel and exactness required, so there is no need to
  instantiate the general pullback ladder at the identity.
- `WeilConjectures.AlgebraicGeometry.Sites.Gm`: redundant direct import, supplied
  by the retained public imports and `Sites.Kummer`.

Removed proof dependency and obsolete tool approval
`lem-weil-pbc-pullback-cohomology-long-exact-ladder` from this node. No other node
is pruned by this delivery. In particular Brauer vanishing, Kummer exactness, the
Kummer sequence, and H¹(G_m) = Pic remain used. The public imports remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The DAG proposed using the general pullback long exact ladder, although the source
library already has a proved exactness theorem for the actual canonical Kummer
boundary, with its kernel explicitly identified. The shorter route preserves the
unit's Kummer-sequence argument and all clauses of the theorem, including boundary
compatibility. No statement or definition repair was needed, and no new node was
introduced. Read the current blueprint statement and the Stacks proofs at
`lemma-kummer-sequence` and `lemma-cohomology-smooth-projective-curve`.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
