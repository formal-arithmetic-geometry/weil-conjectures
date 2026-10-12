## What changed

Completed `AlgebraicGeometry.IsCurve.dense_open_assertions` with its original signature.
The proof assembles all eight assertion fields from four strict comparison subclaims:
vanishing, finiteness, base change, and restriction. It proves the prime-annihilation
specialization directly: additive coefficient conversion and additive geometric stalk
functors preserve annihilation by r; either r vanishes in k and gives primary torsion,
or it is invertible and gives invertible-order torsion. No directional restatement of
the whole theorem remains.

The four new modules retain the prior attempt's subclaims and named whole-proof sorries.
Their nodes now have self-contained statements, correct blueprint ancestry, real search
records, and proofs describing only their own subclaims. The parent node's proof and
proof dependencies now match the Lean assembly. Its existing docstring and signature stay
unchanged. All imports added to the item are proof-only.

## Proved and sorry left

`AlgebraicGeometry.IsCurve.dense_open_assertions` is proved from the comparison declarations;
there is no sorry in its module. This is a reduction, not a claim that its dependency
closure is sorry-free. Exactly four new named theorem sorries remain:

- `AlgebraicGeometry.IsCurve.dense_open_vanishing_comparison`
  (`lem-pbc-j2-dense-open-vanishing-comparison`).
- `AlgebraicGeometry.IsCurve.dense_open_finiteness_comparison`
  (`lem-pbc-j2-dense-open-finiteness-comparison`).
- `AlgebraicGeometry.IsCurve.dense_open_baseChange_comparison`
  (`lem-pbc-j2-dense-open-base-change-comparison`).
- `AlgebraicGeometry.IsCurve.dense_open_restriction_comparison`
  (`lem-pbc-j2-dense-open-restriction-comparison`).

Each has its source, complete proof in words, matching node, and its own module.
The edge cases U=X, empty X/complement, zero coefficients, characteristic zero, and
primary coefficients with an exceptional invertible-order condition follow the identity,
zero-group, or coprime-annihilator arguments in these proofs.

## No longer needed

The direct comparison route does not need the finite-pushforward assertion package
`lem-weil-pbc-curve-assertions-finite-pushforward`
(`Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions`), nor the all-eight
outer-to-middle devissage `lemma-weil-pbc-eight-curve-devissage`. The boundary sheaf's
cohomology and base-change maps are computed directly and the assertions transported
through the long exact sequences. This prunes these two dependencies from this item's
route; other targets may still use them. No unit realization is bypassed.

Removed direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`
- `Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions`
- `Sheaf.AlgebraicGeometry.CurveCoefficientPair`
- `Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder`
- `Sheaf.Paper.ZeroDimensionalCohomology`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `WeilConjectures.SixFunctors.Finite.Stalk`
- `WeilConjectures.SixFunctors.OpenClosed.Exact`

Except for finite-pushforward assertions, these imports are redundant in the top-level
assembly or their corresponding nodes remain ingredients of the comparison subclaims.
They are not claimed to be globally dispensable. All six original public imports remain,
since they express the theorem's statement. The four comparison imports and
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper` are used by its proof.

## Where the brief, the DAG or earlier work was wrong

The prior sandbox did not compile: the affine predicate's instance binder was handled
incorrectly, coefficient-functor additivity was missing, and the stalk-functor additivity
application left an unresolved universe constraint. These are repaired by inferred affine
binders, additivity of the inverse equivalence and sheaf composition, and explicitly
sized module limits before applying stalk additivity.

The old report described three absent directional wrappers, listed seven sorries although
only four modules existed, and contained an obsolete second-reading heading. It is replaced.
The new nodes previously contained free-variable Lean fragments instead of self-contained
mathematical statements and pointed to a created node as their blueprint ancestor.
Both defects are corrected. LeanSearch is unavailable (HTTP Internal Server Error),
recorded honestly; LeanFinder and Mathlib grep ran successfully without a matching theorem.

Existing dense-open finiteness and base-change lemmas require reduced X, finite coefficient
rings, and prime annihilation, unlike this item's general constructible-torsion clauses.
The existing higher-cohomology lemma uses module extension by zero, whereas this signature
converts the abelian extension by zero through E; no compatibility lemma identifies those
encodings here. These declarations therefore cannot replace the four comparisons directly.
The source proof was read from the official Stacks pages 0GJA and 095L because the remote
clone does not contain the untracked literature source tree.

## Second reading by J2

1. Compared the delivered parent module against the repository version. Verdict: the
existing declaration signature is byte-for-byte unchanged; only its proof and imports
changed.
2. Compiled all five delivered modules with `lcompile.py`; the files compile cleanly. The
parent has no `sorry`; the four named comparison theorems are the only split-off sorries,
each with a docstring and matching node. No forbidden declarations or extra axioms were
found in the delivered source.
3. Checked each split-off statement against the corresponding Lean type and its edge cases
(empty complement, U=X, zero sheaf, characteristic zero, and prime annihilation). Verdict:
the statements are true and are strict subclaims rather than restatements of the parent;
searches found no existing declaration that duplicates them.
4. Checked the parent proof route and imports. Verdict: it assembles the eight fields from
the four comparison subclaims and the direct prime-annihilation argument; the removed
finite-pushforward route and redundant proof imports are pruned, while the unit route is
retained through the comparison nodes.
5. Checked all node `proof`, `proof_deps`, `proof_origin`, Lean records, and report entries
against the source. Verdict: they agree; new nodes have self-contained statements and
blueprint ancestry. Changes made: repaired the prior report and node metadata, fixed the
affine/additivity/universe elaboration issues, and added this second-reading record.

## New nodes

`lem-pbc-j2-dense-open-vanishing-comparison` in
`lean/Sheaf/AlgebraicGeometry/Curve/DenseOpenVanishingComparison.lean` states higher-degree
additive equivalences and the conditional primary-vanishing implications (C1-C3 ingredients).

`lem-pbc-j2-dense-open-finiteness-comparison` in
`lean/Sheaf/AlgebraicGeometry/Curve/DenseOpenFinitenessComparison.lean` states the C4-C5
implications, proved in words from the finite boundary H0 and five-term exact sequence.

`lem-pbc-j2-dense-open-base-change-comparison` in
`lean/Sheaf/AlgebraicGeometry/Curve/DenseOpenBaseChangeComparison.lean` states the C6-C7
implications, using boundary comparison and the commuting cohomology ladder.

`lem-pbc-j2-dense-open-restriction-comparison` in
`lean/Sheaf/AlgebraicGeometry/Curve/DenseOpenRestrictionComparison.lean` states C8 equivalence,
using the commuting square of degree-two counit isomorphisms on X and each open.

There are no statement/definition changes to existing declarations and no change records.
