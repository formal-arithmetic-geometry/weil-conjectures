## What changed

Replaced the sole sorry in `AlgebraicGeometry.formalFunctions_local_dictionary` with a
compiling proof. The signature, universe, visibility and definitions used by that signature
are unchanged. Coherence of the pulled-back module is proved using existing declarations:
the locally Noetherian coherence characterization, finite-type pullback, and quasi-coherence
of Mathlib pullback transported through uniqueness of left adjoints.

Split the remaining geometric argument into two new modules: `FormalFunctionsLocalStalkComparison`
and `FormalFunctionsFiniteQuotientComparison`. The first states only the canonical uncompleted
stalk comparison, with its formula on germs. The second states the finite quotient system
comparison and pullback maps from local cohomology, plus conditional compatibility with any
map satisfying that germ formula. Neither is the original statement under another name.
The top proof composes the linear maps and applies the pointwise quotient identity.

New proof imports are private. All original statement imports remain. No existing interface
was changed and no forced adaptation is involved. All three modules compile together through
lcompile.py. Edge cases checked in the mathematical argument: degree zero, zero module and
empty fibre; no finite-level map is assumed surjective. The equivalence in the first new
statement includes its canonical germ formula; omitting that formula would make the second
part invalid for an arbitrary equivalence.

## Proved and sorry left

Closed: `AlgebraicGeometry.formalFunctions_local_dictionary`
(node `lem-weil-pbc-formal-functions-local-dictionary`). No sorry remains in the item's module.
This is a decomposition, not a completed proof of the geometric comparison: one upper hole
closed and two strictly smaller holes added. The coherence conjunct is proved from existing
library declarations without a new hole.

Added and left:
- `AlgebraicGeometry.formalFunctions_local_stalk_comparison`
  (`lem-weil-pbc-formal-functions-local-stalk-comparison`).
- `AlgebraicGeometry.formalFunctions_finite_quotient_comparison`
  (`lem-weil-pbc-formal-functions-finite-quotient-comparison`).

These are the only two sorry declarations in the delivery. The local cohomology abbreviation
and germ predicate are real definitions without sorry and do not choose any witness from an
unproved existence assertion. The equivalence, natural isomorphism and linear maps are
eliminated only inside a theorem proof.

## No longer needed

No original import was removed. No module is globally pruned: the original geometric
lemmas remain needed by the new intermediate nodes. In the top node, the following former
direct dependencies are now used below the split rather than in its Lean proof:
`def-nagata-extended-ideal`, `def-pc-fibre-product`,
`def-weil-pbc-coherent-formal-module`, `def-weil-pbc-module-cohomology-fmap`,
`def-weil-pbc-module-stalk`, `def-weil-proper-morphism`,
`lem-pc-flat-base-change-cohom`, `lem-weil-pbc-affine-morphism-cohomology-edge`,
`lem-weil-pbc-closed-immersion-unit-quotient`, `lem-weil-pbc-flat-base-change-map-sections`,
`lem-weil-pbc-higher-direct-image-presheaf`, `lem-weil-pbc-localization-noetherian`,
`lem-weil-pbc-module-cohomology-fmap-basic-properties`,
`lem-weil-pbc-module-cohomology-fmap-functorial`,
`lem-weil-pbc-quotient-base-change-closed-immersion-ideal`,
`lem-weil-pbc-spec-local-ring-canonical-morphism`,
`lem-weil-pbc-support-pullback-finite-type`, `pqf-def-affine-morphism`.
The top proof uses `lem-weil-pbc-module-pullback-finite-type` directly rather than the
larger support-pullback theorem. Its additional support conclusions are not needed.
No established blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The `lem-pc-flat-base-change-cohom` record points to
`Scheme.Modules.finrankH_pullback`, a field-extension finrank statement for the source
library's cohomology. It is not the canonical isomorphism of derived module direct images
required here. The new stalk comparison precisely states the missing geometric step with
its canonical germ formula; its proof plan cites Tag 02KH directly rather than treating
the mismatched field-extension finrank declaration as that isomorphism; it does not alter that existing node or weaken the target.

The local source file `literature/stacks-project/coherent.tex` is absent on this machine.
The cited human source was read directly at https://stacks.math.columbia.edu/tag/02OD and
https://stacks.math.columbia.edu/tag/02KH. Tag 02OD explicitly leaves the infinitesimal
identifications to verification; the new finite quotient docstring expands that verification
and the transition and germ compatibilities. LeanSearch returned Internal Server Error;
this unavailability is recorded, without claiming a successful no-match search. LeanFinder,
Loogle, source grep and blueprint searches produced no complete matching comparison.

`blueprint_refs.py ancestor` returned None for this module's node, despite its existing
explicit blueprint.from chain. The new nodes preserve that existing chain to
`thm-weil-pbc-henselian-idempotent-lifting`, adding this dictionary node to via.

## New nodes

`def-weil-pbc-formal-functions-local-comparison` records the concrete local cohomology
abbreviation and canonical germ formula, in `FormalFunctionsLocalStalkComparison`. This
predicate ties the comparison to pullback, rather than allowing an arbitrary equivalence.

`lem-weil-pbc-formal-functions-local-stalk-comparison` isolates steps 1 and 3 of the original
plan: flat local base change and the stalk-to-global-cohomology identification with its
section-class formula. It does not state a quotient system comparison.

`lem-weil-pbc-formal-functions-finite-quotient-comparison` isolates the infinitesimal quotient,
closed immersion, affine edge, transition and composite-pullback arguments. It starts from
local cohomology and only conditionally transports canonical germ formulas; it does not
assert the existence or invertibility of a stalk comparison.

No change record is required: no existing statement or definition changed.

## Second reading by M2

1. **Interfaces: PASS.** Diffed the delivered original module against the repository.
   Only five private proof imports and the theorem proof changed. The original theorem
   signature, universe, visibility, docstring and all existing definitions are byte for
   byte unchanged. There are no adapted existing modules and no change record is needed.
2. **Proof and axioms: PASS as a decomposition.** Compiled all three modules in import
   order with lcompile.py: no errors or warnings. Scanned the sources: precisely the
   two reported named theorem sorries, no forbidden declaration form and no definition
   containing sorry. In scratch copies, printed axioms of the original theorem, both
   new theorems and both new definitions. Only propext, Classical.choice, Quot.sound and
   inherited/open sorryAx occur; formalFunctionsLocalCohomology has no sorryAx. The germ
   predicate uses existing open infrastructure but is itself a concrete formula.
   No arbitrary witness of unproved mere existence is installed as definition data.
3. **Split statements: PASS.** Read both full statements and docstrings and checked
   against Stacks Tags 02OD and 02KH. The local comparison omits the quotient system;
   the finite-level comparison omits existence and invertibility of the stalk map.
   The latter uses only a conditional germ formula, so neither restates the item.
   For p=0 the maps are the section pullbacks; for F=0 or empty local base change all
   relevant modules are zero. At n=0 the quotient is by m, not by the zeroth power.
   No finite-level surjectivity or flatness of the infinitesimal closed immersion is
   assumed. Open-comparison choices pin the h-map by the unit square and the resolution
   identifications by their augmentations. Local-spectrum inverse-image neighbourhoods
   are the whole spectrum; composition therefore gives the conditional theta formula.
   Repeated LeanFinder search for localization of higher sheaf cohomology, Loogle search
   for cohomology/pullback, Mathlib grep for localization and closed-immersion cohomology,
   and rg on both library roots found no replacement for either full comparison. Hits
   for site cohomology and etale geometric stalks use different objects. Neither hole
   can be closed in a few minutes with those declarations.
4. **Route and pruning: PASS.** The top proof proves coherence from existing coherence,
   finite-type pullback and Mathlib quasi-coherent pullback results, then composes the
   two genuinely separate comparisons. All public imports are for statement/definition
   infrastructure; the five new top imports are private and used by the proof. Compared
   the old/new proof_deps sets with No longer needed: all eighteen removed direct
   dependencies are listed. No import or globally unreachable module was pruned.
   Read dag/units/sk-thm-p1.json, including realized: none of its realized statement or
   step nodes is bypassed. The formal-functions branch of henselian idempotent lifting
   remains intact. This delivery closes one upper hole and adds two lower holes, a
   decomposition with net minus one hole, not a completed geometric proof.
5. **Nodes: PASS after repair.** Only proof, proof_deps and proof_origin change on the
   existing node. All three new nodes have sources, creation and blueprint records,
   search records, status, chapter/unit and Lean records. Proof_deps agree with the
   union of step uses. Corrected the stalk plan's false citation of the finrank lemma
   as full flat base change: Tag 02KH now supplies the mathematical argument directly.
   Rewrote the finite-level plan with the actual n+1 indexing and self-contained steps,
   removing stale references to steps in the original unsplit plan. Replaced flattened
   new-node Lean signatures by verbatim multiline signatures from the delivered files.

Second reading changed metadata and this report only; the Lean proofs were right and
were retained. No additional hole was closed or added during the second reading.
Sources checked: https://stacks.math.columbia.edu/tag/02OD and
https://stacks.math.columbia.edu/tag/02KH.
