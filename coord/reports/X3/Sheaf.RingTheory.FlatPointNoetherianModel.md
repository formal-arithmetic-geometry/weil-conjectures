## What changed

Replaced the sorry in `Module.exists_noetherian_model_flat_at_prime` with a compiling
proof, keeping its signature and visibility unchanged. It lifts all inputs to the maximum
universe, applies `Algebra.limitModuleFinitePresentation`, selects a flat contracted-prime
stage, and constructs every algebra structure and scalar tower. It proves the ring pushout
from the final ring tensor equivalence and proves the S-linear module comparison by tensor
induction and lift transport.

Added `Sheaf.RingTheory.IntegerApproximationFlatPointStage`, which states the strictly
smaller stage-selection step for an arbitrary supplied approximation. Its assumptions stop
at transition base changes: it requires no finite presentation or final tensor comparisons
and concludes only flatness of one specified stage localization. The existing module proves
the remaining construction and all final model properties. Updated the item's DAG proof.

Both modules compile cleanly with lcompile.py in import order. The second reading moved
the localization and eventual-flatness proof imports into the new stage-selection module,
retaining their import closure while leaving the existing public interface unchanged. No definitions, existing
signatures, public imports, or target statements changed.

## Proved and sorry left

Closed: `Module.exists_noetherian_model_flat_at_prime`
(node `lem-weil-pbc-flat-point-noetherian-model`), 1 original hole.

Added and left: `Algebra.exists_flat_integer_approximation_stage_at_prime`
(node `lem-weil-pbc-integer-approximation-flat-point-stage`), exactly 1 whole public
theorem proof `:= by sorry` in its own new module. No sorry remains in the item's module.
This is a decomposition, not an unconditional proof: 1 hole closed, 1 hole added, net 0.
The new theorem covers localization of the supplied diagrams and the application of 00R6;
it does not construct a noetherian model under a renamed or repackaged target hypothesis.

## No longer needed

Removed the item's proof imports `Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`
and `Sheaf.RingTheory.ColimitEventuallyFlat`. Their corresponding nodes remain needed in
the new stage-selection theorem's proof plan; they are moved below that interface, rather
than mathematically pruned. The item directly needs only the approximation theorem,
the new stage-selection theorem, and Mathlib's finite-type/noetherian result.

The existing node's removed direct proof dependencies, exhaustively, are:
- `def-weil-pbc-noetherian-ring`: remains a statement dependency; its definition is supplied
  by the unchanged public Mathlib import, rather than a separate proof step.
- `lem-weil-pbc-filtered-colimit-localization-at-prime`
- `def-weil-directed-colimit-abelian-groups`
- `lem-weil-pbc-localization-tensor-product`
- `lem-weil-pbc-localization-tensor-over-base`
- `lem-weil-pbc-flat-over-localization`
- `lem-weil-pbc-colimit-eventually-flat`

The last six are retained in the new node's proof dependencies. The two Sheaf modules
are imported there as proof-only imports; thus they also remain in the import closure.

No whole module or node is claimed as pruned: all original substantive localization and
flat-stage inputs still occur in the new node's plan. The extra final A-module tensor
comparison supplied by 00R1 is unused. The new stage-selection theorem does not need
00R1's final ring/module tensor comparisons; those are used only by the item to build
the final model. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing finite-type-approximation flat-loci interface is unsuitable here: it assumes
the limit module is globally flat, while this item assumes flatness only after localization
at q. It also imports OpenFlatLocus, which imports this item, so importing it would form
a cycle. The source-library `Module.exists_fg_flat_localization_tensor` likewise assumes
a globally flat algebra tensor product, rather than the localized finitely presented module.

The approximation theorem requires its two input rings in the same universe. This is
handled explicitly by ULift; the output rings and module still have exactly the maximum
universe required by the original signature. The tensor comparisons are transported back,
including S-linearity and both ring scalar towers.

The local literature sources were not regenerated on this machine. I read the official
Stacks pages for Tags 00RC, 00R1, and 00R6 to check the localization and stage-selection
argument. Edge cases checked mathematically: a zero limit top ring has no q; a zero limit module need not have every stage zero, but finite
stage generators die at a common later stage, whose module is zero by transition base change; the directed index is explicitly nonempty; unequal universes are
handled in the compiled proof. No faithful-flatness or flat-neighborhood assumption is added.

## New nodes

`lem-weil-pbc-integer-approximation-flat-point-stage`, in
`dag/nodes/sec-proper-base-change/`, isolates steps 2-4 of the original proof. Its complete
statement, source, numbered proof, dependency union, searches, blueprint ancestry, and
verbatim Lean signature are recorded. It inherits the item's chapter and unit. No change
record is needed because no existing interface changes.

## Second reading by X3

1. Compared every delivered module against the repository. The existing theorem signature
   is byte-for-byte unchanged, as are its visibility, docstring and public imports. The only
   existing Lean edits are its proof and proof-only imports. The other module and node are
   new; there are no definition or target-statement changes and no forced adaptations.
2. Read the full proof and compiled both files in dependency order. The ring comparison
   preserves the canonical pure-tensor map and the module transport is S-linear. The only
   new hole is the named public stage-selection theorem, with source and complete proof
   docstring; the item has none. No forbidden declarations or hollow definitions occur.
   Scratch-copy `#print axioms` checks for both declarations returned only `propext`,
   `Classical.choice`, `Quot.sound`, and the permitted `sorryAx`. Witnesses are eliminated
   inside a theorem proof, never used to define an arbitrary data object.
3. Checked the new statement against Tags 00RC and 00R6 and the existing localized
   eventual-flatness interface. It isolates selection from supplied diagrams, without
   constructing the model or asserting the final pushout or tensor comparison. The
   Noetherian, local-map and transition hypotheses needed by 00R6 follow by the
   contractions and localization argument in its docstring. Constant diagrams reduce to
   the assumed flatness; the zero top limit has no prime; for a zero module limit, finitely
   many generators vanish at a common later stage and base change gives a zero stage
   module. Nonempty directedness and unequal universes are explicitly handled.
   Independent leanfinder, loogle and Mathlib grep searches, plus searches of both Lean
   roots, found no exact match. Loogle did not recognize `IsColimit`; leanfinder returned
   completion, smoothness and fixed-module localization results, and grep found only
   categorical flat functors. Existing approximation flat-loci results assume global
   flatness and import this item's downstream openness theorem, so cannot close this hole.
4. The proof first uses the existing simultaneous approximation and Mathlib's Noetherian
   result, then constructs the model and final comparisons explicitly. The residual
   localization/selection step is strictly part of the original argument, not a renamed
   model theorem. Checked `dag/units/sk-thm-p1.json` realized statement and steps: this
   node is below those steps and bypasses none. Reported every removed direct dependency;
   no mathematical module or node is pruned. Corrected the new module's missing imports
   of the two Sheaf dependencies retained in its proof plan, so their closure stays needed.
5. Checked the original node's revised steps and dependency union against the Lean proof,
   and the new node's complete statement, source, proof steps, dependency union, searches,
   ancestry, chapter/unit and Lean record. The stored new signature exactly matches its
   Lean declaration. Original node fields outside the allowed proof/Lean fields remain
   unchanged. Verdict: valid decomposition, one old hole closed and one new hole added,
   net zero; no unconditional target proof claimed.

Changed only the new module's proof imports and this report. No proof repair was needed;
closing the localized-diagram construction is not a few-minute lemma application.
