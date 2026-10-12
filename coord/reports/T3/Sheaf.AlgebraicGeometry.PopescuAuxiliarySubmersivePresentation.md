## What changed

Proved `Algebra.popescu_auxiliary_submersivePresentation` in
`Sheaf.AlgebraicGeometry.PopescuAuxiliarySubmersivePresentation` without changing its signature,
visibility, definitions, or imports. The proof constructs the naive quotient pre-presentation,
composes it with Mathlib's localization pre-presentation, proves its Jacobian is a unit, and
reindexes to the prescribed finite types. No other project module is used.

Updated `popescu-auxiliary-submersive-presentation`'s proof, proof dependencies, and proof origin
to describe this Lean proof. Searches using LeanFinder, Loogle, and grep identified Mathlib's
presentation composition, localization Jacobian, and determinant composition formulas.

## Proved and sorry left

Closed the sole hole: `Algebra.popescu_auxiliary_submersivePresentation`
(node `popescu-auxiliary-submersive-presentation`). No holes remain and none were added.
This is a full proof, not a decomposition. The delivery dry run checks the declaration's axioms.
The argument includes empty relation types and zero-ring localizations; it assumes neither
nontriviality nor that the localization element is nonzero.

## No longer needed

No imports were removed and no library module is claimed globally pruned.
The proof dependency edge to `lem-weil-pbc-popescu-delocalize-jacobian-localization`
(module `Sheaf.AlgebraicGeometry.PopescuDelocalizeJacobianLocalization`) is unnecessary and
removed from this node. That module is still the upstream consumer of this theorem and must
remain in the library. The existing public Mathlib import is retained for the unchanged statement.
No new nodes or project proof-dependency imports are required.

## Where the brief, the DAG or earlier work was wrong

The original node listed `lem-weil-pbc-popescu-delocalize-jacobian-localization` as a proof
dependency, but its Lean theorem already proves standard smoothness by applying the present
item. Importing it would create a cycle. Its signature was read and is not used. Mathlib's
pre-presentation composition implements the inverse-relation presentation directly, avoiding
any new polynomial quotient/localization comparison theorem. The unit route remains unchanged.
The local literature checkout lacks `literature/stacks-project/smoothing.tex`; this proof uses
the argument already documented in the item and its consumer and the Mathlib sources read here.

## Second reading by T3

1. The delivered module was diffed against the repository version. The theorem signature,
visibility, definitions, and public import are byte-for-byte unchanged; only the proof body
was filled in. Verdict: pass.
2. The module compiles cleanly with `lcompile.py`; there are no remaining `sorry`s, forbidden
declarations, or hollow definitions. A scratch `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`. Verdict: pass.
3. The sole proved declaration is the existing target theorem. No new statement was split off;
the proof uses Mathlib presentation, localization, determinant, and reindexing declarations.
Searches found no duplicate project or Mathlib declaration. Verdict: pass.
4. The proof follows the explicit quotient-plus-localization route and retains the unit's route;
the obsolete dependency on `lem-weil-pbc-popescu-delocalize-jacobian-localization` is removed
because that theorem consumes this one. No unused imports remain. Verdict: pass.
5. The node now records `status: proved`, with proof steps and empty `proof_deps` matching the
Lean proof; the unit metadata is unchanged. Verdict: pass.

Changed in second reading: marked the completed node proved and documented this review; no Lean
code changes were necessary.
