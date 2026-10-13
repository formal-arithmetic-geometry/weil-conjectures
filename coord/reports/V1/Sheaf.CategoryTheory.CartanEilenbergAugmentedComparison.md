## What changed

Replaced the sole hole in `Sheaf.CategoryTheory.CartanEilenbergAugmentedComparison` with a
complete Lean induction and assembly proof. The statement and public imports are unchanged.
The proof retains an augmented boundary comparison as its recursive state, chooses the next
object and boundary maps together, proves horizontal commutation from the image-factorization
squares, and extends by zero below the common bound.

Added `Sheaf.CategoryTheory.CartanEilenbergComparisonColumnStep`, which isolates the two
horseshoe lifts at one fixed degree. Its hypotheses require resolution and injectivity data
only for that degree and its outgoing boundary. It has neither boundedness hypotheses nor a
conclusion asserting comparisons in every degree. Thus it is a local induction step, not a
renaming or repackaging of the original theorem. Updated both DAG proof records accordingly.

Both modules compile through `lcompile.py --all`, without warnings. No definitions or existing
signatures changed. All choices are local to the existential proof; no chosen data is exported
as a definition.

## Proved and sorry left

Closed: `CategoryTheory.exists_cartanEilenberg_augmented_comparison`
(node `lem-weil-pbc-ce-augmented-comparison`). Its body has no holes.

Added, and still sorry: `CategoryTheory.exists_cartanEilenberg_comparison_column_step`
(node `lem-weil-pbc-ce-comparison-column-step`). This is a decomposition: one upper hole
closed and one strictly local hole added, for net zero. The remaining lemma has the complete
natural-language horseshoe proof in its docstring and node. Existing dependency holes in
`exists_horseshoe_morphism_lift_exact_source` and its dependencies are untouched.

## No longer needed

Removed the direct proof imports `Mathlib.Algebra.Homology.ModelCategory.Injective` and
`Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource` from the original module.
They now belong to the local column-step module and its proof plan. The original node no
longer directly uses `lem-weil-pbc-lift-along-injective-quasi-iso` or
`lem-weil-pbc-horseshoe-morphism-lift-exact-source`; both remain dependencies of the new
local step, so no module is globally pruned. The second reader also removed the redundant direct
`Mathlib.Algebra.Homology.Additive` import from the new column-step module; it is already
publicly imported by `HomologicalComplexAbelian`. All original public imports are retained for the existing
statement. No unit statement or realized step is bypassed (the unit's realized lists are empty).

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The local file `literature/stacks-project/derived.tex`
is absent on this machine; read Stacks Tags 015H, 015I, 015K and 013P from their official web
pages instead. LeanFinder returned only generic injective-resolution comparison results;
LeanSearch was unavailable (HTTP internal server error), recorded honestly. Source searches
found no existing one-column comparison theorem.

The formal bookkeeping must retain the chosen outgoing boundary map: independently choosing
an original-object comparison for each degree would not establish horizontal commutation.
The new proof performs this retention with a dependent `Nat.rec`, and proves the differential
square from the two equations involving that same boundary map. Lean does not simplify the
index transports in a square while its intermediate boundary morphism has a dependent type;
compose away that intermediate morphism first, then remove transports by equality elimination.

## New nodes

`lem-weil-pbc-ce-comparison-column-step`, in
`dag/nodes/sec-curve-estimates/lem-weil-pbc-ce-comparison-column-step.json`, is the fixed-degree
horseshoe extension of an already prescribed augmented boundary map. Its conclusions supply
one object map and the next boundary map, with augmentation and endpoint squares. Edge cases
checked mathematically: zero complexes give zero maps; at the lowest degree the zero incoming
boundary is permitted; nonzero prescribed incoming maps are retained, not replaced. It needs
no source injectivity, no global bound, and no choices outside the adjacent degree. The
blueprint ancestor and unit are inherited from the original node. No change record is needed.

## Second reading by V1

1. **Interfaces: PASS.** Read the complete diff of the existing module against the
   repository. Independently compared the raw declaration signature slices: the signature
   of `CategoryTheory.exists_cartanEilenberg_augmented_comparison` is byte-for-byte identical.
   Only its proof and private proof imports changed. There are no changed definitions,
   forced adaptations, target edits, or unrecorded interface changes.
2. **Proof and axioms: PASS as a decomposition.** Both modules compile locally without
   warnings. Scratch copies with `#print axioms` for both declarations returned exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The only direct hole delivered
   is the public named theorem `exists_cartanEilenberg_comparison_column_step`, with its
   source, proof docstring and node. No forbidden declarations or holed definitions occur.
   The dependent recursion retains the very outgoing boundary map supplied by each step;
   image factorization then proves horizontal commutation. All existential choices remain
   inside the theorem proof and introduce no exported data definitions.
3. **Local statement: PASS.** Read its complete Lean signature, node, and the exact-source
   horseshoe dependency. Checked the two short exact sequences, the cancellation converting
   `hb` into the boundary augmentation square, and both successive prescribed-endpoint
   lifts. A quasi-isomorphism from a degree-zero single complex to a nonnegative complex
   has monic degree-zero augmentation; the other components are maps from zero and monic.
   This supplies the monomorphic quasi-isomorphisms needed by Tag 013P(2), with no source
   injectivity or enough-injectives assumption. Checked zero complexes, the initial zero
   boundary, arbitrary negative `p`, and a nonzero prescribed boundary map (which is kept,
   not replaced). The fixed-degree result omits global bounds and global assembly, so is
   strictly a part of the original argument. Independent LeanFinder search for extension
   of a prescribed boundary chain map returned only shape-embedding APIs; Loogle search
   for injective-resolution complex morphisms returned no hits; Mathlib grep for horseshoe
   and prescribed endpoint results returned no hits. Read the related local library
   comparison and horseshoe files: none proves this step directly. Closing it requires
   substantial exact-sequence and augmentation transport work, not a short application.
   Independently read official Stacks Tags [015H](https://stacks.math.columbia.edu/tag/015H),
   [015I](https://stacks.math.columbia.edu/tag/015I),
   [015K](https://stacks.math.columbia.edu/tag/015K), and
   [013P](https://stacks.math.columbia.edu/tag/013P). The detailed prescribed-endpoint
   extension is the agent's argument using the existing horseshoe lemma, rather than a
   claim that Tag 015K itself contains that detailed statement.
4. **Route and pruning: PASS.** Reviewed the zero extension below the common bound,
   including the differential crossing into the first retained degree. The original
   proof uses the column-step theorem and its assembly; the split step keeps both original
   dependency nodes. `No longer needed` names every removed direct proof dependency and
   import and correctly claims no globally pruned module. The unit record `sk-prop-h2`
   has empty realized statement/step lists, and neither its statement nor route is edited.
   Its referenced blueprint source file is absent locally; the unit JSON contains its
   statement and step in full. There are no matching open change records in `coord/changes`.
5. **Nodes: PASS.** Compared the existing node diff: only `proof`, `proof_deps` and
   `proof_origin` changed. In both nodes, `proof_deps` equals the union of the proof steps'
   `uses`. The new node has its source, searches, origin, blueprint ancestry, inherited
   chapter/unit, creation record, and verbatim Lean statement. Both proof plans agree with
   the actual induction/assembly and the remaining fixed-degree obligation.

**Second-reading changes:** removed only the redundant public Additive import from the new
column-step module, updated the import accounting above, and added this review. No proof,
statement, definition, or node repair was needed. Holes closed: one; holes added: one;
net zero, explicitly a decomposition. Scratch axiom-probe copies were removed.
