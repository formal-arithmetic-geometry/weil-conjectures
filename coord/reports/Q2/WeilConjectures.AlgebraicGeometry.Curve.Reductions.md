## What changed

Closed `AlgebraicGeometry.IsCurve.Assertions.of_forall_isReduced` without changing its
signature. The proof takes the actual nilradical reduction, proves that its structure
morphism is a curve by transporting the dimension bound through the reduction
homeomorphism, specializes the hypothesis to each prime on this fixed reduced curve,
extends from prime coefficients to constructible Λ-module coefficients, extends to the
pulled-back torsion sheaf, and transfers the eight assertions back to the original curve.
The three intermediate steps have separate new modules and nodes. Their statements each
cover a distinct proper part of the argument, rather than repeat the original universal
reduction theorem. All imports added to Reductions are proof-only.

The repository acquired a Q1 landing while this worker was developing the dense-open
geometry. Rebased the sandbox onto those landed proofs, retaining their closed C7 and
localisation proofs verbatim; the earlier exploratory geometry is only in scratchpad and
is not part of this delivery. The unit's route is unchanged.

## Proved and sorry left

Newly closed in this delivery:
`AlgebraicGeometry.IsCurve.Assertions.of_forall_isReduced`
(node `lemma-weil-pbc-curve-constructible-primary-reduction`).

The item's two remaining sorries are unchanged:
- `AlgebraicGeometry.exists_mono_lowerShriek_constantModSheaf_lowerStar`
  (`lemma-weil-pbc-normalization-exact-sequence`).
- `AlgebraicGeometry.IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite`
  (`lemma-weil-pbc-curve-normalization-constant`).

The delivery adds exactly these three named theorem sorries:
- `AlgebraicGeometry.IsCurve.assertions_of_constructible_prime_devissage`
  (`lem-weil-pbc-constructible-prime-module-devissage`).
- `AlgebraicGeometry.IsCurve.assertions_of_constructible_approximation`
  (`lem-weil-pbc-constructible-approximation-assertions`).
- `AlgebraicGeometry.IsCurve.assertions_of_reduction`
  (`lem-weil-pbc-reduction-module-assertions`).

Each has its source and full proof in its docstring and corresponding DAG node. The
assembly, including the curve instance and the specializing lambda, compiles. Checked
empty curves, zero sheaves and the zero coefficient ring: no nonempty or nontrivial
hypothesis is needed. Finiteness C4/C5 is taken directly from the constructible hypothesis
when F itself is constructible, never from a colimit of finite groups. Primary and
invertible-order conditions pass to the subobjects used in approximation.

## No longer needed

No import removed relative to the current base: all pre-existing imports support retained
proofs or statements. In particular `WeilConjectures.SixFunctors.Etale.Gabber` remains
necessary for `Etale.shortExact_map_forget₂` in the already-proved devissage theorem.

The old immediate `proof_deps` no longer used directly by the assembly are:
- `lemma-weil-pbc-curve-filtered-cohomology`;
- `lemma-weil-pbc-eight-curve-devissage`;
- `lemma-weil-pbc-universal-homeomorphism-coverings`;
- `lemma-weil-pbc-universal-homeomorphism-site-equivalence`.

Their content remains needed transitively through approximation, prime devissage,
and topological invariance. They are not marked globally unreachable.

No whole node or module can be declared unreachable by this delivery. The old immediate
proof dependencies of the constructible-primary reduction are replaced by its three
specific intermediate steps and the reduction geometry lemma. Filtered cohomology,
short-exact devissage and topological invariance remain needed inside those steps, so they
are not pruned from the target's closure. No exploratory duplicate of the landed Q1
localisation lemmas is delivered.

## Where the brief, the DAG or earlier work was wrong

The brief's snapshot had six sorries, but a concurrent landed delivery closed three while
this worker was working. The delivery now targets one of the three genuinely remaining
sorries and preserves the landed work. The DAG's former four-node plan did not provide
module-coefficient interfaces that express constructible approximation and prime
induction for all eight conditional assertions; these are now stated explicitly.

LeanSearch returned Internal Server Error for all three recorded searches; the failures
are recorded honestly. LeanFinder and source grep ran and found no exact theorem for
these three steps. The proofs follow Stacks 03SC, 03SA, and 03SI; the Stacks pages were read
through the web because this read-only clone contains only literature indexes.

## New nodes

`lem-weil-pbc-constructible-prime-module-devissage`:
`Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage`. On one fixed reduced curve,
prime-field constructible coefficients suffice for arbitrary constructible finite-ring
coefficients. Remaining work is primary decomposition, exponent induction and coefficient
transport, using the already-proved short-exact devissage.

`lem-weil-pbc-constructible-approximation-assertions`:
`Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions`. On one fixed curve,
assertions for constructible finite-ring sheaves extend to a torsion sheaf through
constructible approximation and cohomological continuity. Finiteness is handled only under
its constructibility hypothesis.

`lem-weil-pbc-reduction-module-assertions`:
`Sheaf.AlgebraicGeometry.Curve.ReductionModuleAssertions`. For a fixed curve and fixed sheaf,
all eight assertions transfer from its actual reduction pullback; the remaining work is
cohomology and stalk comparisons and naturality for base-change and open squares.

No definition or existing statement changed; no change record is needed.

## Second reading by Q2

1. I compared the delivered `Reductions.lean` with the repository version. The existing
   declaration signatures are byte-for-byte unchanged; the only existing declaration
   change is the proof of `IsCurve.Assertions.of_forall_isReduced`. The three added
   modules contain only the named split theorems, and no target statement or definition
   was altered.

2. All four delivered modules compile with `lcompile.py --all`. The only remaining
   `sorry`s are the two pre-existing declarations in `Reductions.lean` and the three
   named split theorems listed above. There are no axioms, unsafe declarations, opaque
   definitions, externs, or hollow definitions. The proof uses the reduction
   universal-homeomorphism theorem, constructible generation, filtered cohomology,
   short-exact devissage, and pullback functoriality; the intermediate split theorems
   have exactly the hypotheses shown in their Lean declarations. Explicit scratch
   `#print axioms` checks of the assembled theorem and all three new theorems show
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from open statements.

3. I checked the three new statements against Stacks 03SC, 03SA, and 03SI and searched
   the library by declaration names and by constructible, filtered-colimit, reduction,
   and topological-invariance keywords. The prime devissage theorem is the coefficient
   induction step, the approximation theorem is the filtered-colimit step, and the
   reduction theorem is the universal-homeomorphism transfer step. None restates the
   item. The approximation docstring now explicitly inserts constructible images using
   the Noetherian subobject lemma before invoking continuity.

4. The proof follows the unit route: reduction, constructible approximation, prime
   devissage, then transfer of all eight assertions. Edge cases checked in the worker
   report (empty curve, zero sheaf, zero coefficient ring) require no extra hypotheses.
   The finite conclusions C4/C5 are used only when the sheaf is constructible. The old
   direct dependencies replaced by the split route are recorded individually under
   `No longer needed`, while their mathematical content remains transitively used.

5. DAG proof steps, `proof_deps`, `proof_origin`, Lean declarations, and docstrings now
   agree. The approximation node cites constructible subobject closure in addition to
   continuity and filtered generation. The unit record remains unchanged.

I changed the approximation theorem's proof documentation and node citations to make
constructible-image formation explicit, removed two unused public Mathlib imports from
prime devissage, and expanded the pruning record for the four old direct dependencies.
