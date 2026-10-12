## What changed

Proved `CochainComplex.TotalFreeFiltration.differential_mem` in
`Sheaf.Algebra.Homology.TotalFreeFiltrationTerms` without changing any existing
statement, definition, visibility or import. Six proved private helpers implement
the existing node's generator argument: inclusion of full/lower generators,
the total differential formula, horizontal stability, and stability of full and
lower generators. The main proof takes the supremum into the comap of the target
stage under the differential. Non-successor differentials vanish by shape.

The proof follows `lem-pc-derived-total-filtration-stable` exactly; its
`proof_deps` remains empty and its node needs no update. The unit record has no
realized node for this item, and its route is unchanged. Searches through
LeanFinder, Loogle, the source library and Mathlib found the total differential
component formulas, which this proof uses directly.

## Proved and sorry left

Closed the sole hole: `CochainComplex.TotalFreeFiltration.differential_mem`
(node `lem-pc-derived-total-filtration-stable`). Holes closed: 1; holes added: 0.
No sorry remains in the item or is added elsewhere. All six private helpers
are proved. The file compiles cleanly through `lcompile.py`.

The proof handles stage zero and inactive summands through bottom submodules,
column zero through the positive-column vanishing hypothesis, every other column
through its predecessor, arbitrary integer degrees, and non-successor degrees
through the complex shape equation. It needs neither exactness nor splitting of
the short complexes: their first arrows being cochain maps suffices.

## No longer needed

None. No proof-dependency imports were present, none were added, and the four
existing public Mathlib imports support the module's definitions and category
instances. No node or module of the existing proof plan is bypassed.

## Where the brief, the DAG or earlier work was wrong

None. Mathlib's signed differential formulas implement the argument already
recorded in the node and declaration docstring.

## Second reading by E2

1. Compared the delivered module with the repository version. All existing declaration
   signatures, definitions, visibility, and imports are unchanged; only the proof of
   `CochainComplex.TotalFreeFiltration.differential_mem` and private proof helpers were added.
   Verdict: pass.
2. Compiled the complete delivered module with `lcompile.py`; it has no errors or warnings,
   no `sorry`, and no forbidden declarations. The generator argument proves the stated
   differential-stability theorem, including the zero and non-successor cases. Verdict: pass.
3. Checked the sole target statement and the private helper statements against the existing
   node and source proof. The helpers are strict intermediate facts, and no split-off theorem
   or duplicate declaration was added. Verdict: pass.
4. Reviewed the proof route and imports. It uses the existing total-complex formulas and
   submodule closure operations, preserves the unit route, and leaves no unused imports or
   proof dependencies. Verdict: pass.
5. Checked the DAG node and unit metadata: the node's declaration and statement remain exact,
   its proof remains the recorded Tag 09KP route, and no unit realization is bypassed.
   Verdict: pass.

Changed only this report by adding the required second-reading record; no Lean or DAG changes
were needed.
