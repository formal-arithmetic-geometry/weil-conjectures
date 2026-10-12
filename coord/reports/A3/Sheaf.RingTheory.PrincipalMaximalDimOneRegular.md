## What changed

Proved `Ring.isRegularLocalRing_of_principal_maximalIdeal` in
`Sheaf.RingTheory.PrincipalMaximalDimOneRegular` without changing its signature.
Rewrite the maximal ideal using `hmax` and its spanFinrank using
`Submodule.spanFinrank_singleton hπ`; rewrite the dimension using `hdim`, and
apply `isRegularLocalRing_iff`. This implements the original one-step plan
using proved Mathlib declarations. Updated the node's proof text to record
these exact steps; its proof dependencies and source are unchanged.
Retained both original public imports: they provide the regular-local and
Krull-dimension notions in the statement. No proof-only import is needed.

## Proved and sorry left

Closed: `Ring.isRegularLocalRing_of_principal_maximalIdeal`
(blueprint: `lem-weil-pbc-principal-maximal-dim-one-regular`).
One of one original holes proved; zero holes added, zero split off.
No sorry remains in the delivered module. The final single-file compilation
passed with no errors or warnings. The dry run also checks declaration axioms.

## No longer needed

No import removed. Both original public imports are retained for the statement
and its existing public interface.
No DAG node or proof dependency is pruned: `def-weil-regular-scheme` remains
the definition used. No additional Sheaf or WeilConjectures module is needed.
The item's node is not a unit realization in `dag/units/sk-thm-p1.json`,
and the original unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The docstring and node's one-generator argument
are realized directly by `Submodule.spanFinrank_singleton`. The first trial
using the upper-bound criterion compiled but did not use `hπ`; the final proof
uses it and compiles without the unused-variable warning.

The first dry run rejected removal of a public import without a change record;
the import has been restored, preserving the original public interface.

## Second reading by A3

1. Compared the delivered module with the repository version: only the original
   theorem's proof body changed. Its signature, docstring, module header and
   public imports are byte for byte unchanged. No definitions or targets changed.
   Verdict: pass.
2. Independently compiled the delivered file without errors or warnings. Compiled
   a scratch copy with `#print axioms
   Ring.isRegularLocalRing_of_principal_maximalIdeal`: exactly `propext`,
   `Classical.choice`, `Quot.sound`. No sorry or forbidden declaration remains,
   and no data is chosen from an unproved theorem. Verdict: pass.
3. No new declarations, split-off statements, nodes or holes were added.
   Read Mathlib's `spanFinrank_singleton` proof: a nonzero singleton has at most
   one generator and cannot have zero generators. The zero-generator edge case
   is excluded by `hπ`; a field cannot satisfy the displayed principal nonzero
   maximal ideal hypothesis. Verdict: pass; split-off searches are inapplicable.
4. Read Mathlib's `isRegularLocalRing_iff` and singleton span-finrank lemma.
   The proof uses these directly, with no upstream unproved dependency. This is
   already the short definitional route. Both public imports concern notions
   in the signature; no proof-only import was added. Compared the old dependency
   list: its sole entry `def-weil-regular-scheme` is still used through its exact
   Mathlib match. No dependency is missing from No longer needed. Read the unit's
   `realized` statement and steps: this auxiliary node is not among them, and
   the unit route is preserved. Verdict: pass.
5. Compared the node JSON: only the proof step text changed, accurately recording
   the two rewrites, singleton rank calculation, and regular-local criterion.
   Its uses, proof_deps and documented proof_origin still agree with the proof.
   No new node fields require review. Verdict: pass.

Second reading changed only this report, adding the independent review and
explicit axiom-check evidence. The Lean proof and node need no repair.
