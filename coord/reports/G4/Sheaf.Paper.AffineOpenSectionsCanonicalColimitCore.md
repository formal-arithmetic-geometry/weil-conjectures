## What changed

Completed the existing sandbox reduction of `affineOpenSections_canonical_colimit_core`.
Its original signature, including universes and the supplied adjunction and component formula,
is unchanged. The proof imports two new modules, `Sheaf.Paper.AffineOpenSectionsDescent` and
`Sheaf.Paper.AffineOpenSectionsZeroDetection`, and Mathlib's group filtered-colimit machinery.
Section descent supplies representatives. Zero detection applied to `a - b` supplies eventual
equality. `Types.FilteredColimit.isColimitOf'` constructs the underlying type colimit, and
`reflectsColimit_of_reflectsIsomorphisms` with `isColimitOfReflects` lifts it to additive groups.
No object is selected from an unproved existence theorem to define new data.

Added the missing nodes for the two new modules and updated the original node's proof,
proof dependencies, and proof origin. The new nodes describe the affine-site continuity
argument using existing site-colimit, inverse-image restriction, and elementwise-colimit
nodes. Their theorem docstrings give the complete argument and its source tags.
The node is below the unit's realized statements and steps; none of `sk-thm-p1`'s realized
nodes is bypassed or removed.

## Proved and sorry left

Closed the sole hole in the item:
`affineOpenSections_canonical_colimit_core`
(node `affine-open-sections-canonical-colimit-core`). Its Lean proof is complete from the
following two strictly smaller statements.

Added exactly two holes, each in its own new module:

- `affineOpenSections_descent` (node `affine-open-sections-descent`): only representative
  existence, with no equality detection or universal property.
- `affineOpenSections_zero_detection` (node `affine-open-sections-zero-detection`): only
  finite-stage vanishing of a given section, with no representative existence or universal property.

This is a decomposition, not a completed proof of the geometric continuity theorem.
There are no holes in the item's proof. The delivery closes one and adds two holes,
so its hole balance is minus one. The two new holes are precisely `:= by sorry`.
Singleton systems, zero sheaves, and empty affine limits satisfy the new statements;
`IsCofiltered` excludes an empty indexing category. The empty-limit case follows by
finite-cover descent; the singleton case is the open-immersion restriction comparison.

The three modules compile together using the launcher compiler. The final delivery dry
run also checks their declarations for forbidden axioms.

## No longer needed

No original import, original proof-dependency node, or original module is pruned: the
original node had no proof dependencies and the original imports are statement imports.
Removed the earlier sandbox's redundant direct import
`Mathlib.CategoryTheory.Limits.Types.Filtered`; it is already publicly imported through
`Mathlib.Algebra.Category.Grp.FilteredColimits`. The resulting proof compiles.
Pruned project nodes/modules: none. The proof does not require higher cohomology,
Cech complexes, or the spectral sequence in steps (4)-(5) of Tag 03Q6; those were never
listed as dependencies of this item, so no pruning credit is claimed for them.

## Where the brief, the DAG or earlier work was wrong

The previous attempt left three Lean files but no report or DAG records for its two
new holes. Its proof compiled; the missing metadata made it an unfinished delivery.
This delivery completes that reduction and supplies the two missing nodes.
The original DAG's single continuity step hid both representative descent and equality
detection. The updated proof records each separately and explains the Mathlib glue.

LeanFinder's closest results are `exists_appTop_π_eq_of_isAffine_of_isLimit` and
`exists_appTop_map_eq_zero_of_isAffine_of_isLimit`. These concern the structure sheaf,
not an arbitrary abelian etale sheaf, so they do not close this theorem. Existing directed
set-valued and cohomological continuity declarations require different functors,
coefficient systems, or site presentations. The local-stalk descent declarations only
cover a particular neighbourhood diagram and are above this general affine-open theorem.
They were not imported to avoid reversing the intended dependency direction.

LeanSearch returned HTTP 500 and is recorded as unavailable, not as evidence of absence.
LeanFinder and a Mathlib grep ran successfully; their exact queries are recorded in the
new nodes and the sandbox search log. Blueprint searches for sections and colimits found
no imported blueprint statement identical to either of the two new subclaims.
The ancestor helper returned `None` for this recently created node; the new records
instead follow its recorded parent chain to `lemma-weil-pbc-gabber-effacement`.

Sources read: Stacks Tags [03Q6](https://stacks.math.columbia.edu/tag/03Q6),
[0EYL](https://stacks.math.columbia.edu/tag/0EYL), and
[0A35](https://stacks.math.columbia.edu/tag/0A35).

A dependency-graph audit encountered the pre-existing cycle between
`lem-weil-pbc-sheaf-algebraic-structures-objects` and
`lem-weil-pbc-sheaf-algebraic-structures-abelian-component`. Both edges exist in the
read-only baseline. Neither new subclaim has a dependency path back to itself, the
other new subclaim, or the item. This shared infrastructure cycle was not edited.

## New nodes

`affine-open-sections-descent` is stated by `affineOpenSections_descent` in
`lean/Sheaf/Paper/AffineOpenSectionsDescent.lean`. It isolates surjectivity of the canonical
comparison on sections. Its proof fixes an affine stage, uses affine-site continuity
and the inverse-image section formula, identifies stage restrictions, and extracts a representative.

`affine-open-sections-zero-detection` is stated by `affineOpenSections_zero_detection` in
`lean/Sheaf/Paper/AffineOpenSectionsZeroDetection.lean`. It isolates eventual vanishing.
Its proof fixes the supplied stage, applies the same section formula and detects equality
with zero at a later stage. Combined with subtraction, this gives exactly the equality
condition needed by the Mathlib recognition theorem.

No definition or existing statement changed; no change record or forced adaptation is needed.

## Second reading by G4

1. Interface preservation: compared the item module with the read-only repository
   using diff, and separately compared the entire theorem signature byte for byte.
   They agree, including universe levels, all hypotheses, the component formula,
   and the conclusion. There are no changed definitions, target statements, or
   forced adaptations. The existing node changes only proof, proof_deps, and
   proof_origin. Verdict: pass.
2. Proof and axioms: compiled all three modules in import order with lcompile.py.
   Each compiled without diagnostics. A scratch copy of the item with three
   #print axioms commands showed exactly propext, Classical.choice, Quot.sound,
   and sorryAx for each declaration. The only two textual sorries are the public
   named theorems affineOpenSections_descent and affineOpenSections_zero_detection.
   There are no definitions, arbitrary witness constructions, or forbidden
   declarations in the delivery. The subtraction argument has the correct arrow
   direction k to j; op turns it into the filtered transition needed by
   Types.FilteredColimit.isColimitOf'. Verdict: pass as a decomposition.
3. Split statements: read both signatures, docstring arguments, new nodes, and
   Stacks Tags 03Q6, 0A35, and 0EYL. Affine stages are qcqs; transitions between
   them are affine. Passing to the initial slice over a fixed stage permits the
   continuity argument over that affine base. Restriction to the affine etale
   basis and the canonical base-change composition isomorphisms identify the
   site formula with the supplied adjunction unit. Uniqueness of left adjoints
   with their units handles the arbitrary supplied H and hH. A singleton gives
   an isomorphism on terminal sections; the zero sheaf gives zero representatives;
   an empty affine limit has an empty stage by finite-cover descent. Cofilteredness
   rules out the empty index category. Descent provides only surjectivity, and
   zero detection provides only eventual vanishing; neither restates the original
   universal property. Repeated LeanFinder with different wording, a Mathlib
   grep for etale limits and section existence, and upstream/project searches for
   inverse-image representatives and eventual equality. The closest Mathlib
   results are for the structure sheaf. The project's unit-eventual-equality
   theorem requires a directed system, a fixed stage sheaf and its specific
   units; section-description provides only local representatives of a set
   sheaf. Neither immediately closes either new hole. Loogle's query with Sheaf
   was rejected as an unknown identifier, so that search supplies no evidence.
   The two geometric claims cannot be closed by a short application of the
   declarations found. Verdict: true, needed, strictly smaller open claims.
4. Route and pruning: read the Mathlib type-colimit recognition criterion and
   additive-group filtered-colimit instances. The proof uses precisely the two
   subclaims, subtraction, the type criterion, and reflection. Its new imports
   are proof-only plain imports. The existing imports supply statement notions.
   The original node had no proof_deps, so no original dependency is omitted from
   No longer needed. Checked sk-thm-p1's realized statement and every realized
   step: the item is below these and none is removed or bypassed. Verdict: pass;
   no project node or module is pruned.
5. Metadata: checked the two new nodes' source, self-contained statement,
   statement dependencies, proof steps and their union of proof dependencies,
   search records, created/blueprint/chapter/unit fields, and Lean records against
   the modules. The item's two proof dependencies agree with its actual calls;
   the new nodes record the intended source arguments for their explicitly open
   proofs. Hole accounting names one closed hole and two added holes, net minus
   one, and correctly calls this a decomposition. Verdict: pass.

Second reading changed only this report by adding the independent review and its
verification evidence. No Lean signature, proof, import, or node needed repair.
