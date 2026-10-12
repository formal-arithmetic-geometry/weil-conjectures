## What changed

`Sheaf.AlgebraicGeometry.FormalFunctionsStalk` now proves
`AlgebraicGeometry.formal_functions_stalk` by applying the existing
`AlgebraicGeometry.theorem_formal_functions` to the actual local base change and
transporting its isomorphism through the new geometric dictionary. The original
signature, public imports, and the existing proof of
`AlgebraicGeometry.formal_functions_stalk_structureSheaf` are unchanged.

Added ordinary proof imports of `Sheaf.AlgebraicGeometry.TheoremFormalFunctions`,
`Sheaf.AlgebraicGeometry.FormalFunctionsLocalDictionary`, and
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`. The new module states only
uncompleted stalk/cohomology and finite-level quotient-system identifications,
including their compatibility with canonical stalk pullbacks. It makes no completed
cohomology/limit comparison assertion. Its local schemes, modules, ideals and functors
are specified by actual existing constructions inside the theorem's type.

The main proof computes every projection of the transported equivalence using
completion functoriality, the formal-functions quotient factorization, the natural
isomorphism of systems, and the limit-preservation isomorphism for restriction of
scalars. This proves annihilation and transition compatibility. The proved private
helper `AlgebraicGeometry.completion_map_linear` upgrades the equivalence to completed
ring linearity by evaluating Cauchy representatives on each limit projection. Its proof
contains no hole. Declaration-local heartbeat limits and transparency options support
the cohomology/restriction-of-scalars elaboration; no file-level options were added.

Both delivered modules compiled together without warnings through `lcompile.py`.
The main module took about 30 seconds, and the new statement module about 5 seconds.

## Proved and sorry left

Closed the one original direct hole:
`AlgebraicGeometry.formal_functions_stalk`
(node `lem-weil-pbc-formal-functions-stalk`). This is a decomposition, not a proof
independent of all remaining sorries: one upper hole is replaced by one strictly
geometric lower hole, and the existing formal-functions theorem is used as intended
in stage 3. No sorry remains in the item's module.

Added one hole, exactly the complete proof of the public theorem
`AlgebraicGeometry.formalFunctions_local_dictionary`, in
`Sheaf.AlgebraicGeometry.FormalFunctionsLocalDictionary`
(node `lem-weil-pbc-formal-functions-local-dictionary`). It combines the original
geometric steps 1-7, before the application of formal functions; it does not restate
the completion comparison. The upper proof genuinely applies Theorem 02OC and proves
all subsequent algebraic glue in Lean. No other holes were added or moved, and there
are no hollow definitions. The pre-existing degree-zero proof is retained verbatim.

## No longer needed

No original imports were removed, and no modules are claimed pruned. The original
geometric dependencies are still needed for the local dictionary and remain named
in its node. The main node's direct proof edges now point to that dictionary, the
existing formal-functions theorem, the completion and fibre definitions, and the
unchanged degree-zero argument; replacing direct edges is not a claim that their
geometric descendants are unnecessary.

`WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar` is not imported for the
stalk comparison: its recorded declaration is insufficient, as explained below.
The generic flat-base-change mathematical input itself is still necessary.

## Where the brief, the DAG or earlier work was wrong

The Lean record of `lem-pc-flat-base-change-cohom` points to
`AlgebraicGeometry.Scheme.Modules.finrankH_pullback` in
`WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`. Reading its signature
shows that it is a dimension equality for a field extension, not the generic flat
base change isomorphism needed for `Spec O_(Y,y) -> Y`. It cannot be applied in
step 3 of the original stalk proof. The local dictionary keeps the true mathematical
input from Stacks Tag 02KH in its proof plan, and leaves its implementation to the
next worker rather than pretending the dimension equality supplies it. No existing
node statement, definition, target, or module interface was changed.

The source was read at the available read-only copy
`/home/ubuntu/work-bp/sheaf/literature/stacks-project/coherent.tex`, lines 5721-5800:
the proof of Tag 02OD separates exactly into local base change, identification of
infinitesimal neighbourhoods and their cohomology, then the application of formal
functions. The unit `sk-thm-p1` and its `realized` nodes are unchanged, and this
reduction preserves the formal-functions route used for the henselian input.

The new dictionary was checked against p=0, the zero module, an empty fibre, and a
local ring with zero maximal ideal. It asserts no finite-level surjectivity: the
quotient-to-fibre cohomology maps can fail to be surjective, and the proof correctly
uses Theorem 02OC only after taking the inverse limit. Its system isomorphism is
between quotient-sheaf cohomology and fibre cohomology, not between module quotients
of the stalk and fibre cohomology.

LeanSearch was unavailable (HTTP Internal Server Error), recorded as unavailable.
LeanFinder returned only unrelated sheaf/affine-limit declarations. Mathlib grep
found no matching geometric dictionary. Loogle did locate `AdicCompletion.congr`,
which is used in the main proof. The full-blueprint search for formal functions
returned only the finite-fibre vanishing result; no duplicate dictionary was found.

## New nodes

`lem-weil-pbc-formal-functions-local-dictionary`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-formal-functions-local-dictionary.json`,
states the coherent local pullback, uncompleted stalk equivalence, finite-level
system isomorphism over the local ring, and the canonical pullback map formula.
The node retains the detailed geometric proof steps from the original node and
has the new module, source, actual three-kind search records, and inherited
chapter/unit and blueprint ancestry. The original node's proof and dependencies
are updated to the Lean composition and completed-scalar argument.

No change records or forced adaptations are needed: only the item's proofs, ordinary
proof imports, and proof-plan metadata changed, and the other Lean module is new.

## Second reading by P3

1. **Statements and interfaces.** Compared the delivered stalk module with the repository version. Existing declaration signatures, including `formal_functions_stalk` and the degree-zero theorem, are byte-for-byte unchanged. The added local-dictionary theorem is a separate split-off statement with explicit geometric data and no completion conclusion. Verdict: pass.

2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py`; compilation is clean. The stalk target has no `sorry`; the only remaining hole is the named public `formalFunctions_local_dictionary`, with its matching DAG node and source/docstring. No forbidden declarations or hollow definitions occur. Verdict: pass.

3. **New statement review.** The local dictionary is strictly below the target: it supplies coherence, the uncompleted stalk equivalence, finite-level system isomorphism, and canonical map formula. It does not assert finite-level surjectivity or a completed limit comparison. Its edge cases (degree zero, zero module, empty fibre, and zero maximal ideal) are consistent. Search records report no duplicate library or Mathlib declaration. Verdict: pass.

4. **Route and pruning.** The proof applies the existing formal-functions theorem after the local geometric dictionary, then proves transition, kernel, projection, and completed-scalar compatibility. The unit route through local base change, infinitesimal quotients, and formal functions is retained. Imports are limited to the theorem, dictionary, completion functoriality, concrete limits, and existing degree-zero/coherence support; no proof-only import was removed because each remaining import is used. Verdict: pass.

5. **DAG agreement.** The target node proof and `proof_deps` describe the Lean composition, and the new dictionary node carries the split theorem, module/declaration record, source, proof plan, and searches. The unit `realized` route is unchanged. Verdict: pass.

Changed only the proof of `formal_functions_stalk`, added the private completed-linearity helper, added the split-off `FormalFunctionsLocalDictionary` module and node, and recorded the review here.
