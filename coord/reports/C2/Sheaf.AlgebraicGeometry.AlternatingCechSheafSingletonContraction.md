## What changed

Replaced the preserved attempt's almost identical insertion-homotopy statement
with two strictly smaller parts of Stacks Tag 02FU: positive-degree contraction
and degree-zero cocycle factorization. The main theorem's signature and existing
docstring are unchanged. Its proof uses the degree-one equation and d²=0 to show
that 1−d₀h₀ is a cocycle endomorphism, factors it through the augmentation, then
adds d₀h₀ to recover the required degree-zero equation. Updated the parent node's
proof and dependencies to this argument.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.alternatingCechSheafAugmentation_restrict_singleton_contraction`.
Two new holes remain:

- `AlgebraicGeometry.alternatingCechSheaf_restrict_positive_contraction`, node
  `lem-pc-s3-alternating-cech-sheaf-positive-contraction`.
- `AlgebraicGeometry.alternatingCechSheafAugmentation_restrict_degreeZero_factorization`,
  node `lem-pc-s3-alternating-cech-sheaf-degree-zero-factorization`.

This is a decomposition, one original hole closed and two added (net −1).
There are no sorries in the item's module and no sorries in definitions.

## No longer needed

The original construction import remains necessary. The preserved attempt's
proof import `Sheaf.AlgebraicGeometry.AlternatingCechSheafSingletonRetraction`
and node `lem-pc-s3-alternating-cech-sheaf-singleton-retraction` are not needed
by this proof. The undelivered new module
`Sheaf.AlgebraicGeometry.AlternatingCechSheafSingletonInsertionHomotopy` and node
`lem-pc-s3-alternating-cech-sheaf-singleton-insertion-homotopy` have been removed
from the sandbox. No claim is made that the existing singleton retraction is
unreachable from other targets. No unit step is bypassed; this node realizes
none of the unit's fixed statement/steps.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's intermediate theorem contained essentially the whole
contraction with a retraction hypothesis and its docstring incorrectly claimed
that the canonical insertion equation used any chosen retraction. Canonical
insertion produces the singleton projection, and an arbitrary retraction needs
an additional adjustment. That attempt was replaced, not delivered.
The new positive-degree lemma leaves out degree-zero exactness; the new
factorization lemma uses only degree-zero cocycles and no homotopy. Their
combination is an actual algebraic argument, not a renamed application.

Both new claims were checked at r=0 (no index i), an empty U i (zero modules),
r=1 (augmentation an isomorphism, positive terms zero), and degrees beyond r.
Read Stacks Tags 02FU and 01FM online, and searched the library, Mathlib and the
blueprint for existing matches. LeanFinder returned generic exactness/Dold–Kan
lemmas, not these sheaf statements; grep returned no match. LeanSearch was
unavailable and is recorded as such.

## New nodes

`lem-pc-s3-alternating-cech-sheaf-positive-contraction`, in
`Sheaf.AlgebraicGeometry.AlternatingCechSheafPositiveContraction`, carries the
positive-degree signed insertion cancellation only.

`lem-pc-s3-alternating-cech-sheaf-degree-zero-factorization`, in
`Sheaf.AlgebraicGeometry.AlternatingCechSheafDegreeZeroFactorization`, carries the
kernel universal property of the augmentation at degree zero on U i.

Each has its exact Lean statement, complete proof in words, source, searches,
and the parent's chapter/unit. No interface change or forced adaptation occurs.

## Second reading by C2

1. Compared the sole existing delivered module with the read-only repository by
   diff and programmatically compared its full theorem signature byte for byte:
   unchanged. Its existing docstring, public construction import, and visibility
   are unchanged. Only two plain proof imports and the proof body were added.
   No definition or existing statement changes, hence no change record is needed.
2. Compiled all three modules in import order with lcompile.py: no errors or
   warnings. Exactly the two named split theorems above contain sorry, each as
   `:= by sorry`; there are no definitions in the delivery, no arbitrary witness
   chosen into data, and no prohibited declarations or attributes. The proof
   correctly precomposes the degree-one identity by d₀ and uses d²=0; it then
   factors id−d₀h₀ and finishes by additive cancellation. An appended scratch
   `#print axioms` probe compiled and checked all three delivered declarations:
   each uses exactly propext, Classical.choice, Quot.sound, and sorryAx. The
   scratch copy was removed; the parent is still conditional on the split holes.
3. Read both split statements against the concrete presheaf products,
   differentials, augmentation, sheafification, and integer extension. Verdict:
   true and strictly smaller than the parent. Positive contraction asserts no
   degree-zero factorization; factorization asserts no homotopy. The latter uses
   the singleton coordinate and pairwise cocycle equality, so it does not assume
   a general lifting property for epimorphisms. Its lift is natural and linear.
   Both carry source, full proof in words, and matching nodes. Independently
   checked r=0 (no i), r=1, empty U i, and degrees at and beyond the last term.
   Also verified 621 integral basis-vector signed insertion identities for
   r=1 through 6, every i, including augmentation at degree zero. This tests the
   signs; the docstrings explain equality of the restriction composites.
   Re-read [Stacks 02FU](https://stacks.math.columbia.edu/tag/02FU) and
   [Stacks 01FM](https://stacks.math.columbia.edu/tag/01FM). New LeanFinder search:
   "contractibility of the Cech resolution on a member of the open cover using
   insertion of a fixed index" returned generic sheaf-condition and extra
   degeneracy results. Loogle `"Cech"` returned generic Čech nerve results.
   Grep `extraDegeneracy|exactAt_cechComplex_of_le` and a separate search over
   lean/ located `TopCat.Presheaf.exactAt_cechComplex_of_bijective` and
   `exactAt_cechComplex_of_le`, and `cechSortedContraction`. Read them: the first
   two give elementwise exactness for all tuples, and the last sorts repeated
   tuples in an abelian-group section complex. None supplies the needed natural
   module-sheaf maps for this increasing-tuple complex. No short closure of either
   split hole was found. A first malformed Loogle query was retried successfully.
4. The reduction is a real argument using the two separate ingredients, not a
   renamed application of the parent. Both proof imports are needed and plain;
   the public import supplies the existing signature. The original parent
   proof_deps contains only the construction, which remains used: no original
   dependency is pruned. The report's removed retraction/insertion-homotopy refer
   only to the preserved undelivered attempt. Inspected the unit record
   sk-thm-picard-f-representable: this node realizes no fixed statement or step;
   the route is retained. Verdict: pass, as a decomposition (net −1), not a
   completed proof independent of sorryAx.
5. Compared the existing node to the repository: only permitted proof fields
   differ. Its steps and proof_deps match the Lean argument. Checked each new
   node's Lean statement verbatim against its module; source, proof, dependencies,
   chapter, unit, and creation records agree. Added missing lean_audit records
   for master and slopmaster2, both state none.

Second reading changed only the two new nodes' audit metadata and this report;
no Lean repair was required.

Validation: deliver3.py --no-push printed OK (commit fdec1c2a6f), with
review class CODEX because this decomposition adds two public theorem modules
and their nodes. All-declaration probes and preflight passed.
