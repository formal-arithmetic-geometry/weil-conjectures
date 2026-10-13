## What changed

Filled all three proofs in `Sheaf.RingTheory.ProjectiveResolutionKernelProjective` without
changing their signatures or visibility. Added the fully proved private helper `kernel_dimension`.
The first theorem computes Ext vanishing directly from the bounded resolution and iterates
Mathlib's dimension shifting along the finite exact sequence. The second identifies the initial
monomorphism with a kernel. The third proves that the degree-zero augmentation is an isomorphism.
Proof-only imports: added `Mathlib.CategoryTheory.Abelian.Projective.Dimension` and
`Mathlib.CategoryTheory.Abelian.Projective.Ext`; removed `Sheaf.Algebra.Schanuel`.
The node's proof, proof dependencies, and proof origin now describe this route.
All three existing public imports are used by the statements or their definitions.

Compilation is clean with `lcompile.py`. The argument treats every length, including `e=0`,
`d=0`, and `d=1`, and preserves all universe parameters. No new definitions or statements
visible to importers, and no forced adaptations.

## Proved and sorry left

Closed 3 holes:

- `ModuleCat.projective_kernel_of_partial_projective_resolution`.
- `ModuleCat.projective_of_exact_partial_projective_resolution`.
- `ModuleCat.projective_of_projective_resolution_length_zero`.

No `sorry` remains in this module; none was added anywhere. This is a proof, not a
hole decomposition. The private helper is proved completely. The direct Mathlib route also
avoids relying on any unproved Sheaf Ext-comparison theorem.

## No longer needed

Removed import and dependency module: `Sheaf.Algebra.Schanuel`.
Removed planned proof dependencies:

- `lem-weil-pbc-schanuel` (`Sheaf.Algebra.Schanuel`).
- `lem-weil-pbc-ses-projective-quotient-splits` (the splitting argument is unused).
- `lem-weil-pbc-projective-direct-sum` (no stabilized sums are constructed).

The Schanuel induction and its auxiliary stabilized resolutions are unnecessary for this item.
No claim is made that these nodes or modules are globally unreachable from all targets.
The Ext exact-sequence and projective Ext-criterion nodes in the updated DAG are realized
by Mathlib's dimension-shift and projectivity lemmas directly; no Sheaf modules for those
facts, and no `Sheaf.RingTheory.ProjectiveResolutionExtCharacterization` import, are needed.
The item is not a statement or a step in `dag/units/sk-thm-p1.json`'s `realized` lists;
the unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

No statement error. The DAG's earlier search correctly identified the Ext dimension-shifting
route, but the initial comparison with bounded resolutions need not be left as a separate
theorem: `ProjectiveResolution.extMk_surjective` and `extMk_zero` prove the required
forward vanishing directly from the zero terms. The original Lean docstring explicitly
labels the Schanuel argument as a proof plan; it remains intact, while the actual new route
is recorded in the delivered DAG and this report.

## Second reading by X3

1. **Unchanged interface — pass.** Compared the whole delivered Lean module with
   the repository using `diff`, and checked all three existing theorem headers through
   `:= by` byte for byte. Their signatures, universes, visibility, and existing
   docstrings are unchanged. There are no definition changes, other delivered modules,
   change records, or forced adaptations. The only added declaration is the proved
   private helper. The node comparison changes only `proof`, `proof_deps`, and
   `proof_origin`.
2. **Proof and axioms — pass.** Independently compiled the module with `lcompile.py`
   without errors or warnings. A scratch copy with `#print axioms` for the private
   helper and all three public theorems reports exactly `propext`, `Classical.choice`,
   and `Quot.sound` for each. Scanned the delivered Lean for `sorry` and forbidden
   declarations/options: none. The resolution witness is a hypothesis unpacked inside
   a proof; no object is defined using an unproved existence theorem.
3. **Split statements and edge cases — pass.** There are no split-off statements or
   added holes. Read the helper's complete induction: at `e=0` the epimorphism gives
   the kernel short exact sequence; at a successor, tail exactness supplies the
   epimorphic kernel lift, and its kernel agrees with the first kernel because the
   kernel inclusion is monic. The dimension bound drops by exactly one at each
   step. `n=0` gives projectivity, including `e=0` and `d=0` or `d=1` under
   `d ≤ e+1`. In the second theorem `d=0` contradicts `hd`, and `d=1` reduces to
   the single augmentation kernel. The third theorem uses the zero degree-one term
   and the augmentation's actual cokernel universal property.
4. **Shortest route, imports, and pruning — pass.** Searched Mathlib using the
   registered `msearch.py` grep route with a different query combining
   `ComposableArrows`, projective dimension, and projective kernels; inspected the
   localization dimension-shift hit and Mathlib's dimension and Ext lemmas.
   Searched `lean/Sheaf`, `lean/WeilConjectures`, and the upstream source for the
   arbitrary partial-resolution assertion. Found no existing finite-sequence lemma
   replacing the induction. The existing Sheaf short-exact dimension theorem uses
   the resolution/Ext comparison and supplies no shorter route. All imports have
   a direct role; both added Mathlib imports are proof-only. Compared old and new
   `proof_deps`: the three removed nodes are exactly those listed under
   `## No longer needed`. Read the unit's `realized` lists: this item realizes no
   unit statement or step, and the unit route is unchanged.
5. **DAG agreement — pass.** Read the node beside the Lean proof. Its four steps
   describe the direct bounded-resolution Ext computation, the fully proved
   kernel induction, the projective Ext criterion, and the two particular cases.
   Checked that `proof_deps` is the union of the step `uses` lists. The Ext and
   projective criterion dependencies are Mathlib nodes and are realized by the
   imported Mathlib declarations; the direct-summand dependency contributes its
   isomorphism-invariance assertion via `Projective.of_iso`. The proof origin names
   the actual Mathlib route. No new node is needed for an unfinished result.

Changes from this reading: appended this independent review; no Lean proof or DAG
repair was necessary. Three original holes closed, zero holes added, zero split off.
