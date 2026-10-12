## What changed

Reduced `CategoryTheory.colimit_site_covering_continuity` to the purely categorical
`CategoryTheory.filteredColimit_preservesPullback`, in the new module
`Sheaf.CategoryTheory.FilteredColimitPreservesPullback`. Existing signatures and public imports
are unchanged; the new dependency is a proof-only import.

The original module contains two fully proved private helpers. `finite_pullback_cover`
indexes a covering by its finite set of distinct arrows and applies finite base change.
`continuous_of_finite_pullbacks` proves continuity by the generated-topology sheaf criterion
and Mathlib's pairwise-pullback sheaf comparison. Consequently continuity needs no target
precoverage axioms and no finite composition axiom. The new categorical statement concerns
one cospan and has no precoverage or sheaf assumptions or conclusion.

Both delivered Lean modules compile locally without warnings. The categorical lemma is
left for subsequent proof, with a complete sourced proof in its docstring and DAG node.
The source paragraphs were read at https://stacks.math.columbia.edu/tag/09YL and
https://stacks.math.columbia.edu/tag/0A35 because the cited local literature directory is
absent on this machine. No definitions, statements, or other existing modules were changed.

## Proved and sorry left

Closed: `CategoryTheory.colimit_site_covering_continuity`
(node `lem-weil-pbc-colimit-site-covering-continuity`), by a complete Lean proof from the new
categorical pullback-preservation theorem. This is a decomposition, not a proof free of sorry.

Untouched sorry: `CategoryTheory.colimit_site_covering_axioms`
(node `lem-weil-pbc-colimit-site-covering-axioms`).

Added sorry: `CategoryTheory.filteredColimit_preservesPullback`
(node `lem-weil-pbc-filtered-colimit-preserves-pullback`). Its proof is exactly `by sorry`.
One upper hole closed and one lower hole added: net hole change zero.
The two private helpers are completely proved and contain no sorry.

## No longer needed

No imports were removed: all existing public imports support the statements and stay visible
as before. The continuity proof does not use the node
`lem-weil-pbc-colimit-site-covering-construction` as a proof dependency; its backward edge
was removed from the continuity node. Its module is still the upper consumer of this module,
so no whole module becomes unreachable. Continuity does not need the finite composition or
isomorphism axioms, transition covering preservation, or axioms for Q. These hypotheses
remain in the unchanged signature. No unit statement or realized unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

Both component nodes pointed back to `lem-weil-pbc-colimit-site-covering-construction`,
whose Lean proof applies those components. That theorem cannot be imported to prove either
component without an import cycle. This delivery replaces the continuity node's circular
proof dependency with the actual categorical argument; the untouched axioms node still
has the circular plan and needs correction when its proof is written.

Mathlib's `Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy` requires unrestricted
base-change stability of both precoverages. Finite indexed base-change stability is weaker:
an infinite indexed family can contain infinitely many distinct arrows, even when its
image without repetitions was finite before base change, because different choices of
isomorphic pullback objects may give different arrows. The proof therefore uses canonical
pullbacks indexed by distinct arrows and the generated-topology sheaf criterion directly.

The generic categorical statement was checked on empty stage categories (no cospan exists),
empty covering families (the helper uses an empty index), and a singleton index category
(the cocone functor is an isomorphism on object and arrow sets, hence preserves the
specified pullback). No disputed statement or forced adaptation is included.

## New nodes

`lem-weil-pbc-filtered-colimit-preserves-pullback` records one stable stage pullback's
preservation in a fixed filtered category colimit. Its module is
`lean/Sheaf/CategoryTheory/FilteredColimitPreservesPullback.lean`. Its source is the pullback
paragraph of Stacks Tag 09YL; the proof uses object/arrow representatives, eventual equality,
and the stage pullback universal property. It is strictly the categorical preservation part
of the original continuity theorem. No change record is needed.

## Second reading by Y3

1. **Interfaces — PASS.** Compared the delivered item with the repository using
   `diff -u`: both existing theorem signatures and docstrings are byte for byte
   unchanged. The only existing-module changes are two private proved helpers,
   one proof-only import, and the continuity proof. No existing definition,
   visibility, target, or other module was changed. The additional module contains
   one new theorem and no definition; no change record is required.
2. **Proof and trust — PASS as a decomposition.** Compiled both delivered modules
   with `lcompile.py --all`, without errors or warnings. In scratch copies,
   `#print axioms` for both helpers reports exactly `propext`, `Classical.choice`,
   and `Quot.sound`. The two original public theorems and the new categorical
   theorem report only those axioms plus `sorryAx`. Source inspection finds
   exactly the two reported holes: `colimit_site_covering_axioms` and
   `filteredColimit_preservesPullback`, both whole named theorem proofs.
   There is no new data construction from unproved existence, no definition with
   a hole, and no forbidden trust mechanism.
3. **Split statement — PASS.** Read the generic pullback theorem, its sourced
   docstring proof, and its node. Independently consulted
   [Stacks Tag 09YL](https://stacks.math.columbia.edu/tag/09YL), the pullback
   paragraph and displayed Hom calculation, and
   [Tag 0A35](https://stacks.math.columbia.edu/tag/0A35), its first proof paragraph.
   Object and arrow joint surjectivity plus eventual equality suffice to lift a
   cone, impose its equation, and prove uniqueness after refinement. These use
   only finitely much data. The theorem is strictly the categorical part of the
   item, with no precoverage or continuity conclusion. Checked the singleton
   index case, empty stage categories (the cospan cannot exist), and the empty
   covering family used by the finite-cover helper. Additional LeanFinder,
   Loogle and grep queries used different terms; inspected the existing finite
   diagram lifting and equality modules and found no identical theorem or short
   replacement. Recorded the independent searches in the new node. Closing this
   categorical hole requires substantial endpoint transport work, beyond a
   short review repair; it remains explicitly open.
4. **Route and pruning — PASS.** Read the two private helper proofs against
   Mathlib's generated-topology sheaf criterion and its pairwise-pullback sheaf
   comparison. The finite subtype of distinct covering arrows is the correct
   index, including when empty. The unrestricted Mathlib continuity theorem
   requires stronger base-change assumptions, so it does not directly apply.
   Every existing public import supplies notation or declarations occurring in
   the public statements; the new categorical dependency is imported privately.
   The old continuity proof dependency on
   `lem-weil-pbc-colimit-site-covering-construction` is the sole retired edge and
   is recorded under No longer needed. No whole module is pruned. Read
   `dag/units/sk-thm-p1.json`: this reduction is below its realized statement and
   steps and bypasses none of them.
5. **DAG — PASS.** Compared the continuity node's proof, proof dependencies and
   origin with the actual reduction. Read the new node's statement, verbatim
   Lean signature, source, proof steps, dependencies, searches, creation record,
   blueprint origin, chapter and unit. Its set-colimit dependencies are Mathlib
   leaves and supply exactly the representative/equality facts the informal
   proof uses. No unreported statement or definition change was found.

Second reading changed only this report and the new node's independent search
evidence. The Lean proofs and signatures needed no repair. One of the item's
two holes is reduced to one strictly simpler new hole; the other is untouched.
This is a decomposition, with net holes closed minus added equal to zero.
