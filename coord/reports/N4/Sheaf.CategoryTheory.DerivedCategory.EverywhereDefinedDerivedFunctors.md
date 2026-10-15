## What changed

Proved `exists_everywhere_defined_derived_functors` in
`Sheaf.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors`, preserving its full
signature and every original public import. The right-derived side constructs a colimit of
costructured arrows directly from the essentially constant ind-diagram: fraction representatives
define the legs, common refinement proves independence, and the splitting witness gives the
universal property. Three private, fully proved helpers implement this construction.

The left-derived side uses the existing, proved
`CategoryTheory.leftDerived_defined_pointwiseKan_bridge`. Mathlib's pointwise derived existence
instances and `totalRightDerived`/`totalLeftDerived` then give both functors and comparison maps.
Added proof imports for DerivedCategory.Fractions, PointwiseLeftDerived, PointwiseRightDerived,
and LeftDerivedPointwiseKanBridge. The latter belongs to the smooth-purity unit but is
used here only as a general localization/limit tool, with no smooth-purity hypotheses;
this item's previous route supplied no such bridge. Updated the item's proof, proof_deps, and proof_origin.
No public interface, definition already in the library, or target statement changed.

The final file compiles cleanly with lcompile.py. A temporary `#print axioms` check of
`exists_everywhere_defined_derived_functors` reports exactly
`[propext, Classical.choice, Quot.sound]`.

## Proved and sorry left

Closed the sole original hole:
`exists_everywhere_defined_derived_functors` (node
`new-everywhere-defined-derived-functors`). Proved 1 of 1 original sorries; added 0 holes.
There are no sorries left in the delivered module and no split-off modules.
The three new private helpers, `denominatorToCostructuredArrow`, `leftFraction_leg_eq`,
and `rightDerived_defined_pointwiseKan`, are all fully defined/proved.
This is a complete proof, not a decomposition into unproved statements.

## No longer needed

Removed the proof import `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral` and the
proof dependency `lem-pc-pre-derived-adjoint-functors-general`. Constructing derived functors
does not require a pre-derived adjunction or any adjunction between F and G.

The complete set of project modules removed from this item's transitive import closure is:

- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
  (`lem-pc-pre-derived-adjoint-functors-general`).
- `Sheaf.CategoryTheory.DerivedAdjunctionHomDiagram`
  (`def-pc-derived-adjunction-hom-diagram`).
- `Sheaf.CategoryTheory.DerivedAdjunctionSourceColimit`
  (`lem-pc-derived-adjunction-source-colimit`).
- `Sheaf.CategoryTheory.DerivedAdjunctionTargetColimit`
  (`lem-pc-derived-adjunction-target-colimit`).

These are pruned from this construction's route; other modules may still need them.
No unit statement or realized unit proof step is bypassed: the item's unit
`sk-thm-picard-duality` records no realized statement or step at this level.
No original public import was removed or privatized.

## Where the brief, the DAG or earlier work was wrong

The old proof plan cited only the pre-derived adjunction, whose statement assumes an
adjunction and proves a Hom comparison. The present existence statement assumes no
adjunction and needs neither that comparison nor its source/target colimits. The updated
plan follows Definition 05S9 and Lemma 05SA using Mathlib's Kan-extension universal properties.
The old node's source also mentions Tag 09T5, which concerns adjunction after existence;
the existing Lean docstring correctly points to 05S9 and 05SA. The source field was preserved
because this delivery changes only the permitted proof fields.

Searches through msearch.py LeanFinder, Loogle, and grep, plus direct searches in Mathlib,
WeilConjectures, and Sheaf, found Mathlib's pointwise-derived APIs and the existing pro-diagram
bridge. LeanFinder returned the pointwise-derived classes and existence lemmas; the Loogle
query with the unqualified Functor name reported an unknown identifier, so the signatures
were read directly from Mathlib instead. No unproved existence statement was needed. The generic ind bridge does not use
abelian or triangulated structure; those hypotheses only supply the concrete localization
and fraction instances at the final application. The splitting clauses include a witness
stage, so an empty denominator diagram cannot satisfy the hypotheses. In the identity-
localization case the inverse-denominator and identity-numerator equations specialize to
the original cocone legs. Source tags 05S9, 05SA, and 09T5 were checked against Stacks online.

## Earlier second reading (a previous round; superseded)

1. **Interface and accidental changes.** Compared the delivered module and node with the
repository versions. The public theorem signature and all existing declarations are byte-for-byte
unchanged; only proof imports and the node's stage-3 proof metadata changed. No target statement,
definition, or other group's module was edited. Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py` and checked the complete theorem
with `#print axioms`. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or
`extern` declarations; the theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
The private helpers are fully proved. Verdict: pass.

3. **Statements and nodes.** The sole target node remains the same statement. Its proof steps,
dependencies, and origin now match the actual fraction construction, pointwise Kan bridge, and
Mathlib derived-functor assembly in the file. No split-off statement or new hole was added, and
searches found no duplicate library theorem. Verdict: pass.

4. **Route and pruning.** The proof follows the shortest available route below the unit: the
essentially constant ind witness gives the denominator colimit, fractions extend it to the
costructured-arrow colimit, and Mathlib's pointwise-derived APIs assemble the functors. The
pre-derived-adjunction import and its three downstream colimit modules are unused and are listed
under “No longer needed”. The unit's realized route is not bypassed. Verdict: pass.

5. **Review result and changes.** No repair was necessary after this reading. The only changes
made in this second reading were this report section and the delivery metadata; the Lean proof,
imports, node statements, and DAG route were retained. Verdict: pass.

## Second reading by N4

1. **Interface and accidental changes.** I compared the delivered module and node against
   the repository versions. The theorem signature and existing declarations are unchanged;
   the module changes only proof imports and the proof body, while the node changes only
   `proof`, `proof_deps`, and `proof_origin`. No target statement, definition, or other
   group's module was changed. Verdict: pass.

2. **Proof and axioms.** The delivered module compiles with `lcompile.py`. An appended
   axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound`; the module has
   no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or `sorryAx`.
   The private fraction and Kan-extension helpers are fully proved. Verdict: pass.

3. **Statements and nodes.** The target declaration has exactly its repository signature.
   The proof uses the existing Mathlib fraction and pointwise-derived APIs, the existing
   essential-constancy definition, and the existing pointwise Kan bridge; no new public
   statement or split-off hole was added. The node's proof steps, dependencies, and origin
   describe those constructions. Verdict: pass.

4. **Route and pruning.** The proof follows the stated route: the essentially constant
   ind witness is transferred to a pointwise left Kan extension by the fraction construction,
   the pro witness uses the proved left-derived bridge, and Mathlib assembles the total
   derived functors. The old pre-derived-adjunction route and its three downstream colimit
   modules are unused and are listed under “No longer needed”. The unit record has no
   realized statement or proof step for this node, so its route is preserved. Verdict: pass.

5. **Review result and changes.** No repair to the Lean proof or DAG was necessary. I
   added this second-reading section to record the five checks and their verdicts. Verdict:
   pass.
