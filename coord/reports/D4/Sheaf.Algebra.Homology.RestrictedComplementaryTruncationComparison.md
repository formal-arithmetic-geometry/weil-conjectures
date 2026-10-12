## What changed

Proved `CochainComplex.restrictedComplementaryTruncationComparison_quasiIso` with its signature
unchanged. The second reader removed the unnecessary proof-only import
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels`; the original public import suffices.
Two proved private helpers show that restriction preserves cokernels and preserves
quasi-isomorphisms when both integer complexes have zero degree -1. The main proof identifies
the arbitrary cokernel with the restricted canonical cokernel and uses Mathlib's complementary
truncation quasi-isomorphism. Updated the existing node's proof to match this uniform argument.

## Proved and sorry left

Closed the only hole: `CochainComplex.restrictedComplementaryTruncationComparison_quasiIso`
(node `lem-sp-restricted-complementary-truncation-comparison`). No holes remain and none were added.
The two private helpers are proved. This is a complete proof from Mathlib, not a decomposition.
Single-file compilation passed without warnings; `#print axioms` lists only `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed

No original imports, nodes, or modules were removed. The unnecessary newly added proof-only
import `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels` was removed at second reading.
No Sheaf or WeilConjectures proof dependencies are needed; the old `proof_deps` was empty. The planned separate argument for nonpositive cutoffs is unnecessary: Mathlib's
strict-support preservation for smart truncation gives zero degree -1 uniformly for all cutoffs.

## Where the brief, the DAG or earlier work was wrong

No statement or interface defect was found. The DAG's degree-zero restriction step needed
explicit Lean glue: natural degree zero has predecessor zero, whereas integer degree zero has
predecessor -1. The proof compares the short complexes by zero, identity, identity, using the
zero target of the first component to prove it is epi. The inherited unit has no realized nodes;
no unit statement or proof step was bypassed.

The earlier attempt was blocked by a delivery-tool import mismatch. On this retry, the unchanged
proof compiled successfully and the required `deliver3.py --no-push` dry run printed OK.
No tool was edited or bypassed, and nothing was pushed. The independent second reading is recorded below.


## Second reading by D4

1. Compared the only delivered module with the repository using `diff`. The existing theorem
   signature is byte-for-byte unchanged (also checked programmatically against its node's Lean
   statement), as are its docstring, variables, visibility, and public import. No definitions,
   other modules, or change records are delivered. Verdict: pass.
2. Compiled the delivered file using `lcompile.py`, without errors or warnings. Scanned for
   `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, and kernel-check bypasses:
   none occur. A scratch copy with `#print axioms` for the main theorem and both private lemmas
   reports only `propext`, `Classical.choice`, and `Quot.sound`. The cokernel is constructed by
   Mathlib, and its identifying isomorphism comes from uniqueness, not arbitrary existence.
   Verdict: genuine complete proof, one original hole closed and no holes added.
3. There are no split-off statements or new public declarations. Read both proved private
   helpers: evaluation proves preservation of cokernels; the restriction comparison has an
   epimorphic zero first component and identity second and third components. At natural degree
   zero the artificial incoming differential is zero; at positive degrees the triples agree.
   Checked zero complexes, degree-zero complexes, and cutoffs a = -1, 0, 1 against the argument:
   strict-support preservation and the epimorphic cokernel projection give zero degree -1 in
   all cases, with no sign assumption on a. Verdict: pass.
4. Searched the local Sheaf/WeilConjectures library and Mathlib for restriction, homology, and
   quasi-isomorphism lemmas, and independently queried LeanFinder for homology of restriction
   when the omitted predecessor is zero. Mathlib's `restrictionHomologyIso` requires matching
   predecessor indices, which fails at natural degree zero; the explicit short-complex
   comparison is appropriate. The integer comparison already uses Mathlib's canonical proved
   quasi-isomorphism. Tested removal of the added Kernels import in a scratch copy: compilation
   still passed, so removed it. The sole original public import is needed by the signature.
   The old `proof_deps` is empty, so no old nodes are omitted from the pruning report. Read
   `dag/units/sk-prop-av-pqf-finite.json`: its `realized` lists are empty and this is an auxiliary
   node; no realized unit statement or step was bypassed. Verdict: pass after import pruning.
5. Compared the node diff: only `proof` and `proof_origin` change; `proof_deps` stays empty and
   its Lean statement agrees exactly with the module. Its four steps match cokernel transport,
   the integer comparison and support, restriction in degree zero and positive degrees, and
   final composition with the identifying isomorphism. No new nodes are needed for proof-local
   closed helpers. Verdict: pass.

Changed only the unnecessary newly added proof import and this report; kept the sound proofs
and node update. No original dependency module became pruned.
