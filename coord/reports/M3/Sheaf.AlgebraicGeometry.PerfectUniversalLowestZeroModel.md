## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.perfectUniversalLowest_zero_model`
by a compiling proof with its original signature and visibility. The proof uses the
existing finite-free residue model, transports it explicitly, identifies bottom
homology by derived composition, and applies the full-rank kernel argument.

Added three modules and matching nodes. `finiteFreeResidueModel_pullback` is proved
from the K-flat pullback specification and exact restriction comparisons.
`finiteFreeBottom_differential_zero` is proved using a trivializing cover and
Mathlib's square-matrix transpose-injectivity result. Its private helpers are proved.
`universalLowest_fiber_ranks` isolates the numerical fibre-rank step.

All four modules compile through lcompile.py, with no warnings. No existing
statement, definition, target, or public import was changed. New modules contain
no definitions with postponed proofs and no arbitrary data chosen from a holed
existence theorem: the model transport is an explicit termwise construction.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.perfectUniversalLowest_zero_model`
(node `lem-sc-perfect-universal-lowest-zero-model`), the original module's sole hole.

Proved without new holes: `AlgebraicGeometry.Scheme.finiteFreeResidueModel_pullback`
(node `lem-sc-finite-free-residue-model-pullback`) and
`AlgebraicGeometry.Scheme.finiteFreeBottom_differential_zero`
(node `lem-sc-finite-free-bottom-differential-zero`), including all their private helpers.

Added and left: `AlgebraicGeometry.Scheme.universalLowest_fiber_ranks`
(node `lem-sc-universal-lowest-fiber-ranks`), exactly `:= by sorry`.
It proves only the numerical fibre ranks from residue-field tests; it constructs
no model and asserts no differential vanishing. Its docstring gives the source,
complete argument, and edge cases. No sorry remains in the assigned module.

This is a decomposition: one original hole closed and one lower hole added,
net zero new-hole reduction before pruning or already existing dependency holes.
The proved transport still imports the existing universe-aware open-restriction
comparison; its dependencies may contain existing sorries.

## No longer needed

Removed direct proof imports from the assigned module:
- `Sheaf.AlgebraicGeometry.PerfectJumpLoci`
- `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`
- `Mathlib.LinearAlgebra.Matrix.Nonsingular`
- `Sheaf.AlgebraicGeometry.TorAmplitudeOpenLocal`
- `Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion`
- `Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology`

`PerfectJumpLoci` and `AffineTorAmplitudeCriterion` remain needed in the numerical
fibre-rank subproblem. `Matrix.Nonsingular` remains needed by the proved bottom
kernel lemma. They are relocated proof dependencies, not globally pruned work.

The direct original steps no longer need nodes
`lem-pc-tor-amplitude-open-local`, `lem-pc-flat-complex-derived-pullback`, or
`lem-pc-derived-open-pullback-homology`. Fixed-interval locality only proves the
opposite implication to the restriction required here. The transport uses the
K-flat counit of `def-pc-derived-pullback` directly. Bottom homology is compared
through derived composition and localization, so no separate open-homology
comparison is needed. These modules may remain reachable through other imports;
this report does not claim a whole-target closure count.

The old direct proof dependencies `lem-sc-perfect-jump-loci` and
`lem-pc-affine-tor-amplitude-criterion` are now needed only through
`lem-sc-universal-lowest-fiber-ranks`. The old direct dependency
`lem-sc-square-injective-free-map-dual-coker-zero` is now needed through
`lem-sc-finite-free-bottom-differential-zero`, using its recorded Mathlib match.
Together with the three removed nodes listed above, this accounts for every old
proof dependency absent from the assigned node's new direct dependency list.
No whole-closure module pruning is claimed.

The second reader removed the redundant public import
`Sheaf.AlgebraicGeometry.PerfectComplex` from the new transport module;
`DerivedPullback` already supplies every type needed by its statement.

## Where the brief, the DAG or earlier work was wrong

The planned Tor-amplitude locality dependency is not a restriction theorem:
`torAmplitude_of_open_neighbourhoods` gives global amplitude from local tests,
whereas the plan needs global tests restricted to an open. The residual fibre-rank
lemma explicitly supplies that argument using open pushforward and exact restriction.
The existing affine criterion also assumes a<=b; the new proof sketch first enlarges
b to max a b. This retains all needed lower vanishing and handles b<a unchanged.

The square-kernel argument does not require a further affine shrinking. Finite free
sheaves have the required free global sections on every scheme, and a trivializing
open cover of the homology suffices. No full-rank direct-summand assertion is used.

The unit `sk-prop-av-cube` has no realized nodes in its statement or step lists;
the prescribed cube route is untouched. Blueprint searches for zero bottom
differential, finite free kernel, termwise pullback, fibre Betti, and square injective
found no blueprint duplicates. Source pages read: Stacks 0BDL, 0BCD, 0EWY, 0BDI,
08E9, 09U8 and 09U9. LeanFinder/Loogle and Mathlib grep searches are logged;
LeanSearch returned HTTP 500 and is recorded as unavailable.

Edge cases checked in the statements and arguments: empty schemes, rank zero,
zero next term, arbitrary integer a, b<a, and nonreduced rings. In particular an
injective square map need not be invertible; only its transpose injectivity is used.

## New nodes

`lem-sc-universal-lowest-fiber-ranks`: the sole new unfinished statement; numerical
vanishing and rank at h(t), with only residue-field rank tests.

`lem-sc-finite-free-residue-model-pullback`: proved transport of a given bounded-above
free model with its prescribed degreewise ranks; no perfection, amplitude, or
cohomology-rank assumption is required.

`lem-sc-finite-free-bottom-differential-zero`: proved sheaf linear-algebra lemma
for a given complex with full-rank bottom homology. Its statement applies over
arbitrary schemes and at every integer degree. No change record is necessary.


## Second reading by M3

1. PASS: Compared the assigned module against the repository with `diff -u`
   and checked the entire theorem signature byte for byte with an assertion.
   Only its proof and plain proof imports differ. Existing docstring, public
   imports, declaration visibility, definitions, and target interfaces are unchanged.
   All other delivered modules are new; no change record is required.
2. PASS: All four modules compiled locally without errors or warnings. Scratch
   copies with `#print axioms` showed exactly `propext`, `Classical.choice`, and
   `Quot.sound` for `finiteFreeBottom_differential_zero`. The transport, numerical
   lemma, and assigned theorem also use `sorryAx`, as expected from the listed
   new numerical hole and existing dependencies. The only delivered source hole
   is the named theorem `universalLowest_fiber_ranks`; there are no new definitions,
   forbidden trust mechanisms, or arbitrary data definitions from existence holes.
   The transport complex is explicitly constructed by two termwise functors.
3. PASS: Read each new statement and its proof, including the square-matrix
   helpers, and checked the numerical lemma against Stacks 0BDL and 09U8 and the
   kernel argument against 0EWY. Empty schemes, r=0, zero next-term rank,
   arbitrary integer a, b<a, nonreduced rings, and residue-field extensions cause
   no exceptions. The numerical lemma uses only residue tests, and asserts neither
   a model nor differential vanishing: it is strictly part of the argument, not
   a restatement. Its source, complete natural-language proof, and matching node
   are present. Independent LeanFinder search for Tor amplitude, residue-field
   vanishing, and rank versus fibre dimension found module rankAtStalk results,
   not the derived sheaf statement; independent Mathlib grep likewise found no
   exact match. Repository search found degree-zero private helpers in
   PerfectUniversalH0BottomModel, but no usable public theorem replacing any new
   lemma. Closing the numerical lemma requires substantial affine restriction,
   tensor, and residue-section comparisons, so it remains explicitly open.
4. PASS after repair: The target proof starts with the existing residue model,
   uses explicit K-flat transport and the existing derived composition, then a
   proved elementary matrix argument. It introduces no alternative upper model
   hole. The redundant PerfectComplex public import in the new transport module
   was removed and the result recompiled. All removed old direct proof dependency
   nodes are accounted for above, distinguishing relocation from genuine pruning.
   sk-prop-av-cube has empty realized statement and step lists; the cube route
   is preserved and no unit file is changed.
5. PASS: Checked the Lean declarations against all four node records. Each
   proof_deps is exactly the union of its proof-step uses, every referenced node
   exists, and proof_origin describes the actual argument. New nodes have the
   required source, statement dependencies, searches, creation, blueprint,
   chapter/unit, and Lean records. The square-matrix dependency is an existing
   Mathlib leaf, matching the three matrix results actually used.

Changes by this reader: removed one redundant public import from the new transport
module, completed the report's old-dependency accounting, and recorded independent
signature, compilation, axiom, mathematical, duplicate-search, and DAG checks.
One assigned hole closed, one strictly simpler hole added: decomposition, net zero.
