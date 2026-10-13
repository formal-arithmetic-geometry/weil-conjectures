## What changed

Replaced the sole hole in `Sheaf.RingTheory.FinitePresentationModelStage` by a
compiling reduction to construction of the comparison system and a proved
filtered-pushout bijectivity theorem. Its existing signature and docstring stay
unchanged. Added proof-only imports of `FinitePresentationComparisonSystem` and
`FilteredPushoutBijectiveStage`.

The new general theorem `CommRingCat.exists_bijective_stage_of_filtered_pushouts`
is proved directly from Mathlib factorization and eventual equality. It factors
the inverse, descends its identity on the finitely generated target, constructs
an inverse by pushout descent, and proves both identities by pushout hom-ext.
The final theorem constructs the required ring equivalence by conjugating this
bijective map and returns the exact compatibility equation.

All three modules compile locally through lcompile.py. No existing statement,
definition, visibility, or public import was changed. No forced adaptations.

## Proved and sorry left

Closed: `RingHom.exists_finitePresentation_model_stage`
(node `lem-weil-pbc-finite-presentation-model-stage`). This is a decomposition,
not a net reduction in holes: one existing hole closed and one new hole added.

Also proved without sorry:
`CommRingCat.exists_bijective_stage_of_filtered_pushouts`
(node `lem-weil-pbc-filtered-pushout-bijective-stage`).

The only remaining/additional sorry is
`RingHom.exists_finitePresentation_comparison_system`
(node `lem-weil-pbc-finite-presentation-comparison-system`). It constructs maps,
colimit cocones, and pushout squares; it does not descend any stage inverse or
assert any stage bijectivity. Its complete construction is in its docstring
and node. Thus it is strictly the construction part of the original argument.

Edge cases checked mathematically: the upper set is nonempty (contains i) even
without a Nonempty I assumption, because i₀ is supplied. Constant diagrams and
identity transitions reduce to tensor universal properties. Zero rings and
empty presentations require no cancellation by a nonzero element; the proved
bijectivity argument uses only finite presentation, eventual equality, and
pushouts. No flatness assumption on P → Q was introduced.

## No longer needed

Second reading removed the redundant proof-only import
`Mathlib.CategoryTheory.Limits.Final` from the new
`FilteredPushoutBijectiveStage` module; `Filtered.Final` already imports it.
No existing import was removed: the original file imported only the Mathlib
modules needed by its statement. The former planned dependency
`lem-weil-pbc-colimit-category-fp-algebras`, module
`Sheaf.RingTheory.ColimitCategoryFpAlgebras`, is no longer used on this route.
Mathlib's exact ring-map factorization and eventual-equality lemmas prove the
inverse argument directly, avoiding tensor reassociation for both inverses.

The former planned `lem-weil-pbc-filtered-colimit-modules-criterion` is also
unneeded: comparison-system construction can verify the ring universal
property directly from representatives and eventual equality. The other
former dependencies (category colimit, elementwise tensor base change,
finite-presentation factorization, and base-change/composition) remain needed
in the new construction node; they are moved below it, not pruned globally.
Explicit accounting for the old model-stage `proof_deps`: the two nodes named
above are bypassed; `def-weil-pbc-category-colimit`,
`lem-weil-pbc-directed-colimit-base-change-elementwise`,
`lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit`, and
`lem-weil-pbc-finite-presentation-base-change-composition` remain used by the
construction or its signature (factorization also by the proved bijectivity
lemma), rather than directly by the model-stage proof. No claim is made that
the bypassed modules are unreachable from all other targets.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound. Its imported file did not actually
contain the planned proof-dependency imports. The inverse argument needs only
a finitely presented comparison map in a cartesian ring system: it does not
need two separate presentations of tensor algebras at the final application.
The new proved lemma exposes this shorter inverse argument.

The nearest-blueprint-ancestor script returned None because the existing split
records module names in created.item. New nodes instead follow the existing
colimit-flat-ring-map blueprint reference to
`lemma-weil-pbc-h1-constructible-representation`, recording the intervening nodes.
The sk-thm-p1 realized unit nodes and route are untouched.

Stacks Tags 02JO, 05N9, and 00QO were checked online; this checkout lacks
literature/stacks-project/algebra.tex. LeanSearch returned Internal Server Error,
recorded as unavailable. LeanFinder and Mathlib/source/DAG grep found components
but no exact comparison-system or filtered-pushout-bijectivity theorem.

## New nodes

`lem-weil-pbc-finite-presentation-comparison-system` is the construction part of
Tag 02JO (3): factor P and Q, construct comparison maps on pure tensors, verify
pushout transitions and finite presentation, and construct their colimits.
Its module contains one public theorem with exactly `by sorry` as its proof.

`lem-weil-pbc-filtered-pushout-bijective-stage` is a fully proved general lemma:
a finitely presented cartesian ring system with a bijective colimit comparison
has a bijective component. The source and index universes are related by
UnivLE; the original theorem applies it in the common maximum universe.

No change records: no existing interface changed.

## Second reading by F1

1. Compared the delivered model-stage module with the repository using diff.
   Its existing signature, docstring, visibility, and public imports are byte
   for byte unchanged. Only its proof and two private imports were added.
   The other two modules are new; no existing definition or target changed.
   Verdict: pass.
2. Compiled all three modules in import order through lcompile.py. Scanned for
   forbidden declarations and holes: the only sorry is the named comparison
   construction theorem, exactly `by sorry`; there are no definitions or
   forbidden declarations. Scratch-copy #print axioms gives only propext,
   Classical.choice and Quot.sound for the bijectivity theorem; the model-stage
   and construction theorems additionally use sorryAx, exactly as reported.
   The factorization, eventual equality, pushout descent, both inverse
   identities and final conjugation were read against the Lean proof.
   Verdict: pass as a decomposition, not a complete proof of the original item.
3. Checked the construction theorem against Stacks 02JO (3), 05N9 and the
   Mathlib finite-presentation cancellation theorem. It descends only forward
   maps and their pushout/colimit system; it does not assert a stage inverse.
   Thus it is strictly the construction part, not a renamed original conclusion.
   Its source, complete natural-language construction, node and canonical
   universe lifts are present. Constant and identity diagrams, zero rings,
   empty presentations and upper-set nonemptiness were checked; no flatness
   or nonzero-ring hypothesis is needed. Independent LeanFinder searches and
   Mathlib/upstream/Sheaf grep found components but no exact replacement.
   Closing the remaining tensor-system construction is substantial work, not
   a few-minute omitted application. Verdict: pass.
4. Checked the top-down reduction and its imports. Removed one redundant
   proof import, Limits.Final, and verified compilation after removal.
   Made all six former proof dependencies explicit in No longer needed,
   distinguishing bypassed dependencies from those moved to construction.
   Read dag/units/sk-thm-p1.json and its realized statement and steps: this
   change is below those nodes and preserves the unit route. Verdict: pass.
5. Checked the existing node's proof and dependencies against the two actual
   theorem applications, and checked both new nodes against their statements
   and proof/construction steps. Their required origin, source, search,
   creation, blueprint, chapter, unit and Lean records are present.
   Made new lean.statement fields verbatim multiline signatures and added the
   exact Mathlib source for the eventual-equality step. Restored non-owned
   fields of the existing node to the repository version. Verdict: pass.

Second reading changed only the redundant proof import, node metadata and
report accounting. No statement or proof argument was changed. One old hole
closed, one construction hole added, net zero; the separate general
bijectivity theorem is proved with no sorry dependency.
