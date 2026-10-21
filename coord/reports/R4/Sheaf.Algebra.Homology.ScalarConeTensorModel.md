## What changed

Proved `DerivedCategory.scalarCone_totalTensor_model` in
`Sheaf.Algebra.Homology.ScalarConeTensorModel`, with its statement and the
`scalarConeCochainFunctor` definition unchanged. Assemble the existing upstream
cochain and derived comparisons into natural isomorphisms. Naturality of the
invertible scalar-cone tensor comparison, and reflection of quasi-isomorphisms
through `Q`, prove right tensor preservation; braiding proves left tensor
preservation. Naturality of the derived comparison proves inversion after
localization. Choose derived right tensoring itself for the descent, its
comparison for η, and the identity for δ.

Updated the item's DAG `proof`, `proof_deps`, and `proof_origin` to this route.
No signatures, definitions, public imports, target statements, or consumers changed.
The existing theorem docstring describes the original six-step plan; the proof's
inline comment records that it takes the shorter comparison route.

Validation: server single-file compilation passed (5.6 seconds after pruning).
`#print axioms DerivedCategory.scalarCone_totalTensor_model` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. The diagnostic command was removed
from the delivery. All Lean lines are at most 100 characters. The argument works
for arbitrary b, including zero, units, and zero divisors, and for unbounded and
zero complexes: it imposes no extra conditions on b or C.

## Proved and sorry left

Closed 1 of 1 original holes:
`DerivedCategory.scalarCone_totalTensor_model`
(node `lem-pe-scalar-cone-tensor-model`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered module,
and the theorem has no transitive sorry dependency according to its axiom check.

## No longer needed

Removed these proof-only imports:

- `Mathlib.Algebra.Homology.HomologySequence`
- `Mathlib.Algebra.Homology.HomologySequenceLemmas`
- `Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four`
- `Mathlib.CategoryTheory.Localization.Predicate`

Removed these dependencies from this item's proof route:

- `lem-weil-pbc-complex-ses-homology-long-exact`
- `lem-weil-pbc-complex-ses-long-exact-naturality`
- `lem-weil-pbc-five-lemma`
- `lem-weil-pbc-localization-universal-property`

The upstream invertible comparison replaces the long exact sequence and five
lemma argument. The already available derived tensor functor supplies the
descent witnesses directly, so no localization lift is needed. These removals
concern this item's direct imports and DAG proof dependencies; no library module
is withdrawn, and no assertion is made that Mathlib modules become globally
unreachable. The derived monoidal construction and its existing tool approval
are retained. The Nakayama unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable definition was found. The original plan does
extra work: the upstream comparisons suffice for two-sided preservation and
explicit descent. The stage-2 review already noted that the inversion and
descent clauses follow formally from θ; the proof implements that observation.

Delivery attempt: `deliver3.py R4 Sheaf.Algebra.Homology.ScalarConeTensorModel`
failed before pushing because the compile server's search path no longer found
the `WeilConjectures` root. The same ordinary `lcompile.py` command that had
passed twice also reproduced this missing-root failure afterward (0.1 seconds).
The reported search path contains only the project's `.lake/build/lib/lean`
and the Lean toolchain library. This is a compile-server environment failure,
not a Lean proof error. No launcher scripts or shared repository files changed.
The complete proved packet remains in the sandbox.

A second normal delivery attempt reproduced the identical missing-root failure;
neither attempt pushed a commit.

Resumed packet review on 2026-10-21 compared the retained Lean file with the
current source and checked the revised DAG against the proof and Nakayama unit.
The statement, definition, and public imports remain unchanged. Saved
delivery retries returned `no answer from the compile server within 196 s`
(server busy or unreachable), with nothing pushed. These are service timeouts,
so the worker follows the brief by backing off and retrying the ordinary tool.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
