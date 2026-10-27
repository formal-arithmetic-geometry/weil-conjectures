## What changed

Replaced the direct hole in
`WeilConjectures.IntegralLineReduction.integral_line_restrictions` by a proof from
existing comparisons and one strictly smaller normalized-evaluation statement.
The theorem signature and its original public import stay unchanged. All additional
imports are for proofs. Locally fixed coefficient-size instances avoid an
unconstrained universe in the imported principal-Koszul sheafification instances.

The main module proves completeness of ordinary signed-line tensor by applying
`integralLineTensorComparison_iso` and the first/fifth equivalence of
`roosIntrinsicCompletenessEquivalence`. Thus its comparison is the actual completion
unit, not an arbitrarily chosen isomorphism. Private helpers prove finite-level
constructibility from a K-flat representative, the chosen tensor model's own comparison,
the degree-zero tensor collapse, exact-functor homology and
`finiteLineTensor_conditions`. They combine the normalized derived reduction comparison
with its existing support calculation to preserve the original common interval.
Completed membership follows by the actual comparison.

The proved generic helper `restrict_pair` lifts both ordinary functors and evaluations
through the full subcategory, preserving the given unit and counit. It also proves both
completed evaluation equations: naturality moves inverse comparisons past the forward
comparisons, then their inverse identities cancel. The final proof constructs c as
`asIso` of exactly the whiskered actual comparison and assembles all clauses of
`Restrictions`.

Added `Sheaf.Paper.IntegralLineNormalizedEvaluations`, whose one theorem isolates only
the ordinary derived evaluation normalization and triangle identity. It asserts no
completeness or constructibility and has no finite-reduction or residue-characteristic
hypothesis. Updated the assigned node to the implemented proof.

Both delivered modules compile with `lcompile.py --all`; the original theorem
signature was also checked byte-for-byte against the shared source.

## Proved and sorry left

One original direct hole closed, by name:
`WeilConjectures.IntegralLineReduction.integral_line_restrictions`
(node `lem-pur-integral-line-restrictions`). Its module has no direct sorry remaining.
All private helper proofs are complete.

One direct hole added, and the only hole left in the delivered files:
`WeilConjectures.IntegralLineReduction.integral_line_normalized_evaluations`
(node `lem-pur-integral-line-normalized-evaluations`). Its whole proof is `by sorry`
in its own new module, with a source and a complete natural-language proof.

This is a decomposition: one upper hole closed, one strictly smaller hole added,
net zero direct holes. The completeness, constructibility, full-subcategory restriction,
and comparison-cancellation arguments are implemented in Lean, rather than included in
the remaining statement. No definition contains a hole. Existing dependency holes are
unchanged.

## No longer needed

No original Lean import is removed, no module is withdrawn, and no whole-closure
pruning is claimed. The original module imported only its definitions. The following
original direct proof dependencies no longer need separate implementations in this
module: `lem-sfb-dual-tensor-adjunctions`,
`lem-weil-proetale-countable-products-exact`, `lem-weil-derived-limit-existence`,
`def-weil-integral-reduction-tower`, `def-pur-integral-derived-operations`,
`lem-pur-integral-operations-well-defined`, `lem-pe-roos-cone-calculus`, and
`lem-weil-finite-free-completed-scalar-comparison`. The proved completion comparison
and unit criterion encapsulate the Roos argument. Their own transitive dependencies
are retained; these are direct-edge removals, not declarations removed from the library.

`lem-pc-sheaf-modules-tensor-closed` and
`lem-pur-line-unbounded-derived-tensor` remain needed in the normalized evaluation
node; line flatness is also used in the finite-level constructibility helper.
`def-weil-finite-torsion-constructibility`,
`prop-weil-pbc-proetale-constant-exact`, and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` are handled through existing
constructibility and derived-comparison declarations, rather than reimplemented.
The original power and derived comparison dependencies remain used. No unit route is
bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The DAG's long explicit Roos transport can be replaced
by already implemented comparison-unit and completeness equivalences. The finite closed
tensor need not be identified globally with a different published tensor model: its own
K-flat comparison suffices for each homology computation.

Edge cases checked in the argument: m=0 uses coefficient multiplication, negative m
uses internal dual evaluation, and both ordinary functors have no boundedness assumption.
The finite quotient index zero means the first positive uniformizer exponent. Exact
line tensor preserves the very same support interval, including zero objects and the
empty scheme. The new normalized-evaluation statement includes no restriction or
completion clause and is therefore strictly part of the original argument, not a
renaming of it.

## New nodes

`lem-pur-integral-line-normalized-evaluations`, in
`dag/nodes/sec-smooth-purity/lem-pur-integral-line-normalized-evaluations.json`, records
the descent of the actual opposite-line chain evaluations to the chosen ordinary
derived tensor model, with representative formulas and the triangle identity.
Its statement drops every completeness and constructibility conclusion and is consumed
by the proved full-subcategory and completion transport argument. No existing public
signature or definition changes; no consumer adaptation or change record is required.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
