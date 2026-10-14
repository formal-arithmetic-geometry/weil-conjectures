## What changed

In `lean/Sheaf/RingTheory/ProjectiveResolutionExtDegree.lean`, the forward
implication of `ModuleCat.projective_resolution_ext_degree` now rewrites with
Mathlib's `hasProjectiveDimensionLT_iff` rather than applying its constructor.
The degree equality passed to `ProjectiveResolution.extMk_surjective` is proved
by `rfl` rather than arithmetic automation. The signature, visibility, imports,
and reverse implication are unchanged. The node's existing proof and dependencies
already describe this route, so no node change is needed.

The current repository already contains a complete proof. This is a small
proof refactoring of the item still listed in `coord/repairs.txt` under upstream
review #1428, not a new proof or decomposition. Mathlib supplies the Ext criterion,
the bound-zero projectivity criterion, and kernel dimension shifting; the
project-specific equivalence additionally constructs an actual bounded resolution
using the existing proved successor-splicing theorem.

## Proved and sorry left

`ModuleCat.projective_resolution_ext_degree`
(node `lem-weil-pbc-projective-resolution-ext-degree`) is completely proved and
compiles in the sandbox. It was already completely proved in the supplied
repository: zero holes closed, zero holes added, zero holes remaining in the
item. No statements, definitions, or target signatures change. No new modules
or postponed lemmas are introduced. The delivery dry run checks the axioms of
the theorem against the permitted standard axioms.

## No longer needed

None. No imports, nodes, or modules are pruned in this delivery.
`Sheaf.RingTheory.GlobalDimension` supplies the explicit resolution predicate;
`Mathlib.CategoryTheory.Abelian.Projective.Dimension` supplies the statement's
dimension predicate and the reused Ext criterion and dimension shifting;
`Mathlib.CategoryTheory.Abelian.Projective.Ext` supplies the cocycle computation;
`Sheaf.RingTheory.ProjectiveResolutionSuccSplice` supplies the actual bounded
resolution construction. The unit route `sk-thm-p1` is unchanged.

## Where the brief, the DAG or earlier work was wrong

The brief says the item still contains `sorry`, but the supplied module has none.
The repair entry's original duplicate Ext criterion has already been replaced by
an explicit bounded-resolution/dimension bridge in earlier landed repairs. The
current DAG agrees with the compiled proof. This delivery does not claim the
previous work as new progress.

Required searches were made through `msearch.py` using leanfinder, loogle, and
grep, supplemented by local searches of both library roots and pinned Mathlib.
The online Loogle index mentions
`ObjectProperty.hasFiniteResolutionOfLength.iff_hasProjectiveDimensionLE`, but
its module is absent from the pinned Mathlib checkout, so it cannot be imported
here. The pinned `hasProjectiveDimensionLT_iff` characterizes Ext vanishing,
not existence of the project's explicit bounded resolution. At bound zero the
reverse implication uses the identity resolution; at successor bounds the
kernel bound and concrete splicing establish the required support bound. Zero
modules satisfy both predicates for every bound; no finite-generation or
nonzero-module assumption is introduced.

## Second reading by U2

1. **Diff and statement preservation.** Compared the delivered module with the repository version. The theorem signature, visibility, imports, and reverse implication are unchanged; only the forward proof uses `rw [HasProjectiveDimensionLE, hasProjectiveDimensionLT_iff]` and replaces arithmetic automation with `rfl` for the definitional degree equality. Verdict: pass.

2. **Compilation and axioms.** Compiled the module with `lcompile.py` successfully. A scratch axiom probe for `ModuleCat.projective_resolution_ext_degree` reports only `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations. Verdict: pass.

3. **Statements and searches.** The theorem is already fully proved, so no statements were split off and no new nodes were added. Rechecked Mathlib and local declarations for an existing bounded-resolution equivalence; Mathlib supplies the Ext and projective-dimension criteria but no duplicate explicit-resolution bridge. Verdict: pass.

4. **Pruning and route.** The proof uses `GlobalDimension`, Mathlib projective dimension and Ext, and `ProjectiveResolutionSuccSplice`; all are required. No old proof dependency or import is unused, and the `sk-thm-p1` unit route and its realized nodes are preserved. Verdict: pass.

5. **DAG and report consistency.** The existing node proof, `proof_deps`, and `proof_origin` describe the proof in the module, including the successor splicing construction. No node or change record needs updating. Verdict: pass.

No code or DAG changes were needed during this second reading.
