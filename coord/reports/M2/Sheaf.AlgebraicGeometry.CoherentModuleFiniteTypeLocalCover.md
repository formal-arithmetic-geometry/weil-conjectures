## What changed

Proved `AlgebraicGeometry.coherent_module_finite_type_local_cover` in
`Sheaf.AlgebraicGeometry.CoherentModuleFiniteTypeLocalCover`, with the original signature
unchanged. Removed two redundant public imports during the second reading;
`Sheaf.AlgebraicGeometry.Coherent` already exports both transitively. Added three fully proved private helpers:
`restrictionEquivalence`, `transportGenerators`, and `imageCover`.
The transport construction adapts the already proved open-site comparison in
`CoherentKernelConditionRestriction`, without importing that module or its kernel theorem.
No other library module is changed.

Coherence supplies finite local generating families. Mathlib site equivalences transport
these families to the corresponding image opens of X, preserving the finite index sets.
A direct pointwise argument proves that these opens cover X, giving finite local-generators
data on X. The node's proof records these three steps; its proof dependencies remain empty.

Validation: the file compiles through lcompile.py with default heartbeat and time limits.
The proof handles an empty cover on an empty scheme: the cover argument has no points to
consider. No nonempty, quasi-coherent, Noetherian, or compactness hypothesis is introduced.
Sources checked: https://stacks.math.columbia.edu/tag/01BV and
https://stacks.math.columbia.edu/tag/01B5. Searches via leanfinder, loogle and grep located
the Mathlib generators API but no exact cover-descent theorem.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.coherent_module_finite_type_local_cover`
(node `lem-weil-pbc-coherent-module-finite-type-local-cover`).
One hole closed, zero holes added, zero split off. No sorry remains in the delivered module;
all private helpers are completely proved. The construction uses proved Mathlib theorems
and the coherence hypothesis, with no unproved auxiliary statements.

## No longer needed

Removed redundant direct imports `Mathlib.AlgebraicGeometry.Modules.Sheaf` and
`Mathlib.AlgebraicGeometry.Restrict`: both remain transitively exported by
`Sheaf.AlgebraicGeometry.Coherent`. The original node had no proof dependencies,
so no old proof dependency is omitted from this list. No nodes or modules leave
the target import closure; no modules are pruned.
The unrelated coherent kernel condition is not used in the argument, but no dependency on
its descent module was present to remove.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The DAG's single locality step was correct but
omitted the Lean transport between open subscheme modules and slice-site modules;
this delivery proves that comparison using Mathlib equivalences rather than leaving it
as a new hole. The unit route is preserved (this node realizes no unit statement or step).


## Second reading by M2

1. **Existing interface: pass.** Compared the only delivered Lean module with the
   repository using `diff`; also compared the declaration text up to `:=` byte for
   byte. `coherent_module_finite_type_local_cover` has exactly the original scheme,
   module, universe, arbitrary index type, covering equality, coherence hypotheses,
   and finite-type conclusion. No existing definition was changed. All three new
   helpers are private. No statement or definition change record or forced adaptation is needed.
   The redundant-public-import deletion has the administrative record
   `coord/changes/CoherentModuleFiniteTypeLocalCoverPublicImports.md`.
2. **Proof and axioms: pass.** Compiled the original delivery and the import-pruned
   delivery through `lcompile.py`, without errors or warnings. A scratch copy with
   `#print axioms` for `restrictionEquivalence`, `transportGenerators`, `imageCover`,
   and the public theorem reports exactly `propext`, `Classical.choice`, and
   `Quot.sound` for each, with no `sorryAx`. Searched the delivered Lean for forbidden
   declarations and holes: none. The equivalence is constructed from restriction
   functors and their proved composition/congruence isomorphisms. The generating
   data chosen in the proof comes from proved Mathlib theorems, never an unproved
   existence statement; no public data definition is introduced.
3. **Split statements and edge cases: pass.** No statements were split off and no
   holes were added. Read the three private helpers: restriction along an isomorphism
   has the inverse restriction as quasi-inverse; `transportGenerators` identifies
   the module and structure unit under the open-site equivalences before applying
   `GeneratingSections.map` and `ofEpi`; the finite index set is preserved by their
   Mathlib instances. `imageCover` chooses a cover member and a generating open
   containing the point, then intersects the image with the test open. Empty opens,
   an empty cover of the empty scheme, and zero generators require no additional
   hypothesis. Definitions 01BV and 01B5 were read at the official Stacks pages:
   https://stacks.math.columbia.edu/tag/01BV and
   https://stacks.math.columbia.edu/tag/01B5. Coherence supplies finite type by its
   first conjunct; the kernel condition is unnecessary for this conclusion.
4. **Shortest route, imports, and unit: pass after cleanup.** Independently searched
   with Loogle `SheafOfModules.IsFiniteType`, Lean Finder "finite generation of a
   sheaf descends from restrictions to an open covering", and `rg` in Mathlib and
   both library roots. The searches returned the generators API, no exact public
   descent theorem. Related `finiteType_of_cover` helpers in
   `QuasicoherentFiniteTypeAffine` and `CoherentFiniteTypeSubKernel` are private and
   concern slice-site restrictions, so they cannot replace the scheme/site
   comparison here. Kept the proved direct argument. Removed the two redundant
   public imports listed above; recompilation succeeds with `Coherent` alone.
   Checked `dag/units/sk-thm-p1.json`, including every `realized` list: this node
   realizes no unit statement or step, and none of those routes is bypassed. The
   old `proof_deps` is empty; the pruning report is complete.
5. **DAG agreement: pass.** Compared the node JSON with the repository: only `proof`
   and `proof_origin` differ. Its unchanged statement matches the Lean signature.
   Its three proof steps match extracting coherent finite local generators,
   transporting each family to the image open, and assembling the image cover.
   Each uses definitions and proved Mathlib operations, with no open project lemma;
   `proof_deps = []` is correct. No new nodes need validation.

Second-reading changes: removed two redundant imports, added the source and blueprint
reference to the module docstring, and corrected the report's import accounting.
The mathematical proof and its original public statement were kept.


Preflight required a change record for the redundant public-import deletion. Added
`coord/changes/CoherentModuleFiniteTypeLocalCoverPublicImports.md`, with the old/new
import blocks and all 396 transitive users from the read-only downstream index.
Every user retains the same effective exports through the remaining public import;
no adaptation or target-definition change is involved.
