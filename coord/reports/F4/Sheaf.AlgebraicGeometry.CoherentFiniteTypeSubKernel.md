## What changed

Completed `Sheaf.AlgebraicGeometry.CoherentFiniteTypeSubKernel` without changing its
public statement or visibility. Reused and repaired the earlier sandbox proof.
Both clauses follow Stacks 01BY (1), (2), whose statement and first two proof
paragraphs were checked at https://stacks.math.columbia.edu/tag/01BY.

The submodule clause uses `kernelCompMono`. The kernel clause chooses finite local
free presentations, proves the induced kernel map epi by Mathlib abelian
refinements, pushes finite generators through epis, and flattens the local covers
using the iterated-slice equivalence. All seven private proof helpers are proved.
The categorical argument is kept generic over its site, with the necessary slice
binary products explicitly supplied from pullbacks; this avoids the expensive
concrete-site elaboration in the previous attempt. No heartbeat limit is raised.

Removed the two unused Sheaf proof imports listed below. Added the proof-only import
`Mathlib.CategoryTheory.Limits.Constructions.Over.Products`. The second reading
removed redundant explicit Kernels and Refinements imports: their declarations
are already available through the retained public Coherent import.
Updated the existing node's proof, proof dependencies, and proof origin to match.
No statement, definition, public import, or other module was changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.RingedSpace.coherent_finiteType_submodule_kernel`
(node `lem-weil-pbc-coherent-finite-type-sub-kernel`). Both conjuncts are proved.
No sorry remains in the delivered module, and no hole or node is added.
This is a proof, not a decomposition.

Validation: the module compiles with the prescribed `lcompile.py` runner.
The axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed proof imports and proof-dependency nodes:

- `Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting`, node
  `lem-weil-pbc-ringed-space-module-exactness-local-lifting`: replaced by the
  proved categorical refinement argument and sectionwise kernel calculation.
- `Sheaf.AlgebraicGeometry.ModuleFiniteTypeImageExtension`, node
  `lem-weil-pbc-module-finite-type-image-extension`: only the quotient clause was
  needed; proved directly here for arbitrary sites by pushing finite generators.

These two modules and nodes are unnecessary for this item's proof; other target
paths may still reach them. The three definition/convention dependencies remain.
Also removed the redundant proof-only imports
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels` and
`Mathlib.CategoryTheory.Abelian.Refinements` added in the first attempt; both are
already available transitively from the retained public import.
The unit `sk-thm-p1` has no realization at this node or either removed dependency,
so no protected unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan and statement are correct. The plan's two theorem
modules are unnecessary: the relevant special cases follow directly from Mathlib.
At second reading their current repository versions have proofs; the generic
site argument here still avoids importing their stronger ringed-space results.
The previous attempt had no report or node update and its main proof exceeded the
heartbeat limit. Its local presentation and cover calculations were useful, but
could not be treated as a validated delivery. This attempt completes the proof and
records the actual route. No interface correction or forced adaptation is needed.


## Second reading by F4

1. **Interfaces — PASS.** Compared the entire delivered Lean module with the
   repository using `diff`; independently extracted the original public theorem's
   signature and checked byte-for-byte equality. Its visibility, universes,
   hypotheses, conclusion, and sole public import are unchanged. There are no
   definitions or interface changes, no adapted modules, and no change records.
2. **Proof and axioms — PASS.** Independently compiled the delivered module with
   `lcompile.py`, then a fresh scratch copy with `#print axioms` for
   `AlgebraicGeometry.RingedSpace.coherent_finiteType_submodule_kernel`. After the
   import repair both pass without warnings; the axioms are exactly `propext`,
   `Classical.choice`, and `Quot.sound`. All seven private helpers are used and
   proved. No `sorry`, forbidden declaration, hollow definition, or witness from
   an unproved existence theorem occurs. The only choices of local generators
   and refinements come from proved Mathlib results.
3. **Split statements and mathematical reading — PASS.** No statements or holes
   are split off. Read all helpers and checked the zero-rank/empty-generator and
   zero-map cases: finite reindexing allows `n = 0`, and the kernel refinement
   argument only uses epi lifting and the kernel equation. The flattened cover
   is indexed by pairs and uses the genuine iterated-slice equivalence, preserving
   finite index types. Checked Stacks 01BY (1), (2) against its first two proof
   paragraphs. Searched Mathlib and the project independently for epi kernel maps,
   finite-type images and coherent kernels; the additional Loogle query
   `CategoryTheory.Limits.kernel.map, CategoryTheory.Epi` finds the pushout-specific
   theorem, which requires a different square. The direct refinement proof here
   is short and sound. No new public declaration duplicates an existing result.
4. **Route, shortest proof, imports and pruning — PASS after repair.** The proof
   descends from the original theorem to genuine local finite generators, uses
   `kernelCompMono` and proved Mathlib refinements, and leaves no lower holes.
   Read the upstream Modules/Coherent module and Mathlib Generators/Quasicoherent;
   the latter's `QuasicoherentData.bind` confirms the cover-flattening construction
   but does not give the finite-type-only assertion needed here. The current
   `finiteType_image_extension` is a stronger ringed-space theorem; the generic
   site helper is needed on slice sites and avoids its extra dependencies.
   Independently removed each of the three added Mathlib imports in scratch
   copies: Kernels and Refinements are redundant; Products is needed for the
   slice binary-product instance. Removed the two redundant imports together and
   successfully recompiled with the axiom check. `## No longer needed` lists both
   removed original proof dependencies and both redundant Mathlib imports.
   Checked `dag/units/sk-thm-p1.json`: neither this node nor either removed
   dependency realizes a protected statement or step, so the unit route is kept.
5. **DAG agreement — PASS.** Compared the existing node files: only `proof`,
   `proof_deps`, and `proof_origin` change. The dependency list is exactly the union
   of step `uses`. The steps accurately describe restriction, composition with a
   mono, finite free local presentations, epi kernel refinements, and finite
   generator transport/cover flattening. The source and origin match Stacks 01BY.
   No new node is needed and no statement metadata changes.

Second reading changed only the two redundant proof imports and this report:
updated the import list, corrected the stale description of the now-proved
image/extension and lifting modules, and recorded the independent review.
No mathematical proof repair or statement change was necessary.
