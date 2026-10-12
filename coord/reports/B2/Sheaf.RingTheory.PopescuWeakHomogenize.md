## What changed

Proved `Algebra.exists_homogenized_local_equations` in
`Sheaf.RingTheory.PopescuWeakHomogenize`, keeping its signature and visibility unchanged.
Added proof-only imports of `Mathlib.RingTheory.Localization.Integer`,
`Mathlib.Tactic.Choose`, and `Mathlib.Tactic.Ring`.

A proved private helper, `Algebra.partial_homogenization_eval`, establishes the monomial
scaling identity. The main proof clears a finite family's denominators, constructs the
support degree bounds and the displayed polynomials, and takes a product of annihilators
in the prime-complement submonoid. Evaluation is independent of coordinate zero, so that
coordinate can be replaced by the common annihilator. The node's proof now records the
actual Mathlib lemmas and construction. The original four-step route and unit route stay.

The common denominator is taken for all coordinates of `y`; the first `n` output
coordinates are still exactly `a`. This harmless choice permits the same finite-family
Mathlib theorem throughout. Empty supports have supremum zero, and empty products are one;
the proof includes `n=0`, `m=0`, `c=0`, and zero polynomials without nonemptiness assumptions.

Validation: the module compiles using `lcompile.py`. A temporary axiom probe reported
exactly `propext`, `Classical.choice`, and `Quot.sound` for the public theorem; it was removed.
All delivered Lean lines are at most 100 characters.

## Proved and sorry left

Closed 1 of 1 original holes:
`Algebra.exists_homogenized_local_equations`
(node `lem-weil-pbc-popescu-weak-homogenize`).

No `sorry` remains in the module. No holes were added or split off. The private evaluation
helper is fully proved. This is a proof, not a decomposition.

## No longer needed

None. Both original public imports and both original definition-node dependencies remain
needed. No planned nodes or modules are pruned. Exploratory imports of the umbrella
`Mathlib.Tactic` and `Mathlib.Data.Finset.Lattice.Fold` were removed before delivery; only
the two required tactic modules remain as proof-only imports.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or unusable statement was found. The original assertion in the
proof docstring that `m=0` uses denominator one was an unnecessary choice: the implementation
clears all of `y`, and may choose another denominator when the initial family is nonempty.
The docstring and node proof describe that construction accurately; no statement changes.
The cited Stacks paragraphs were read in the existing local literature mirror because
this checkout omits the untracked literature files.

## Second reading by B2

1. Compared the delivered module with the repository version: the theorem signature and all
existing declarations are unchanged byte for byte; only proof-only imports, documentation,
the private helper, and the proof body changed. Verdict: pass.
2. Compiled the module with `lcompile.py`; no errors, warnings, `sorry`, forbidden declarations,
or hollow definitions remain. An axiom probe for the public theorem reports only `propext`,
`Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Checked the helper and the main construction against the stated edge cases (`n=0`, `m=0`,
`c=0`, empty supports, and zero polynomials). No new statement was split off, and the existing
node statement is unchanged and exactly what the proof establishes. Verdict: pass.
4. Reviewed the proof route for shorter available Mathlib declarations and checked that the
added imports are proof-only and minimal for the implementation. The original proof dependencies
and unit route remain in use; no nodes or modules are pruned. Verdict: pass.
5. Compared the node's proof, dependencies, origin, and Lean declaration with the delivered
proof and confirmed they agree. Verdict: pass.

Changed only the proof implementation and its proof metadata: added the fully proved private
evaluation helper, completed the target theorem, updated its proof description, and recorded the
actual denominator-clearing route in the node.
