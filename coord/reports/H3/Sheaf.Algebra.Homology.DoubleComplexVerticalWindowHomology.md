## What changed

Replaced the sorry in `HomologicalComplex₂.verticalWindow_total_homology_iso` without
changing its statement. The proof applies the natural single-window isomorphism
columnwise, maps it through totalization and homology, uses the proved single-row
complex isomorphism, and finishes with Mathlib's `extendHomologyIso` for i ↦ i+q.
The two new Sheaf modules are proof-only imports of the item's module. Mathlib's
`Embedding.ExtendHomology` is also a proof-only import.

Completed the earlier sandbox's `DoubleComplexSingleRowTotalIso` construction.
Its proof constructs the inverse diagonal map by the coproduct universal property,
proves that all other diagonals vanish, checks the total differential on the
surviving summand, and assembles a complex isomorphism. It uses no sorry.
The surviving index is explicitly n-q; no object is chosen from an unproved
existence theorem. All private definitions and lemmas are complete.

Added matching DAG nodes for the two parts and updated the original node's proof
and dependencies to follow the compiled Lean composition.

## Proved and sorry left

Closed: `HomologicalComplex₂.verticalWindow_total_homology_iso` (the item's only
original hole), by reduction to the single-window identification and the proved
single-row calculation.

Fully proved new theorem: `HomologicalComplex₂.singleRow_total_iso`, node
`lem-sp-double-complex-single-row-total-iso`. Its private lemmas
`rowInclusion_isIso`, `row_total_isZero`, `rowXIso_hom`, and `rowInclusion_comm`
are also fully proved. The construction covers q=0, degrees below q, and all
surviving degrees; the main homology composition also covers p=0.

Added and left: `HomologicalComplex₂.verticalWindow_single_iso`, node
`lem-sp-vertical-window-single-iso`, in `VerticalWindowSingleIso.lean`. This is
only the columnwise smart-truncation identification: it involves no bicomplex,
no totalization, and no horizontal homology. Its naturality is necessary for
mapping it over the horizontal complex. The entire remaining proof is exactly
`by sorry`, with a source and complete proof in words in the declaration docstring.

Hole accounting: one original hole closed and one lower hole added. This is a
decomposition, not a sorry-free proof of the original theorem. There are no
sorries in the item's module or the single-row module. All three modules compile
in dependency order through the required local compiler.

## No longer needed

No existing import, node, or module is pruned from the item's original interface.
The original window definition remains a statement dependency, and is reached
through the new window lemma. Both numbered steps of the original argument stay.

The earlier sandbox's unused `Mathlib.Algebra.Homology.SingleHomology` import in
`VerticalWindowSingleIso` was replaced by `Mathlib.Algebra.Homology.Single`.
The single-row module uses `Mathlib.Algebra.Homology.Embedding.Extend`, without
importing its homology theory; `Embedding.ExtendHomology` is imported privately
where the final homology comparison actually uses it.
The integer-row shift and symmetry modules found by searching are unnecessary;
the proof directly handles nonnegative indices and extension by zero.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox had no nodes or report and its main proof used the nonexistent
field `Iso.mapHomologicalComplex`. The correct API is
`NatIso.mapHomologicalComplex`. Its row scratch proof also failed on dependent
index transport. The revised proof uses an explicit index n-q and proves the
transport identity by a general equality of indices before assembling the complex.

A first compile could not find the compiled window dependency. The next cache
refresh supplied it; no dependency was recreated or modified as a workaround.

The blueprint and Stacks source files cited by the original node are not present
in this read-only checkout. WANTED: the blueprint proof step 2 and Stacks Homology
`lemma-ss-double-complex`, item (5), for the two new nodes. The new proofs in words
are written by the worker from the existing node's two steps and the Mathlib APIs,
and their `proof_origin.by` is `agent`; no claim of inspecting missing literature
is made. LeanSearch was unavailable; its actual failed searches are recorded,
without an absence verdict. Loogle/LeanFinder and local source searches found the
single-term, truncation, and totalization APIs but no exact statement to apply.

No statement or definition of the existing library was changed. No unit-level
route was bypassed; both original steps are preserved, and the recorded unit's
`realized` entries do not designate this calculation as a separate unit step.

## New nodes

`lem-sp-vertical-window-single-iso`, module
`Sheaf.Algebra.Homology.VerticalWindowSingleIso`: natural identification of the
smart window with vertical homology in a single degree; the sole remaining hole.

`lem-sp-double-complex-single-row-total-iso`, module
`Sheaf.Algebra.Homology.DoubleComplexSingleRowTotalIso`: totalization of a single
nonnegative row is extension by zero along degree translation; fully proved.
Both nodes inherit the original node's chapter, unit, source, and blueprint ancestor.
No change record is needed: the existing statement and public imports are unchanged.

## Second reading by H3

1. **Statements and interfaces.** I compared the delivered item module against the repository version. The target declaration `HomologicalComplex₂.verticalWindow_total_homology_iso` has the same signature byte for byte; only its proof and proof-only imports changed. The two added declarations are new nodes with signatures matching their DAG records.

2. **Proof and axioms.** All three delivered modules compile with `lcompile.py --all`. The single-row totalization theorem is fully proved, with no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The only remaining `sorry` is the named public theorem `HomologicalComplex₂.verticalWindow_single_iso`, documented with its complete construction and represented by node `lem-sp-vertical-window-single-iso`; this is the intentional lower-level split. The composed target proof uses only the declared natural isomorphisms and Mathlib homology APIs.

3. **New statements.** `verticalWindow_single_iso` is exactly the natural single-degree smart-window identification required by the first proof step. `singleRow_total_iso` is exactly the totalization calculation for a complex concentrated in row q required by the second proof step. Both are strictly simpler than the target, cover q=0 and zero-extension edge cases, and are not duplicates of declarations found by local source searches or the recorded Mathlib searches.

4. **Pruning and route.** The proof follows the unit route: columnwise window identification, totalization, single-row identification, and translated homology. Imports used only by proofs are private imports. The original public imports and definitions remain unchanged; no old proof dependency is bypassed or removed. The DAG proof and `proof_deps` agree with the Lean composition, and the unit's realized route is preserved.

5. **Nodes and documentation.** Both new node files include their statements, sources, proof steps, search records, Lean declarations, and chapter/unit metadata. The target node records the two new proof dependencies and the intentional split. The remaining hole has a source and a natural-language proof in its docstring. No change record is required because no existing statement or definition changed.

I changed this report only by adding this second-reading section; no Lean statement or definition was altered during review.
