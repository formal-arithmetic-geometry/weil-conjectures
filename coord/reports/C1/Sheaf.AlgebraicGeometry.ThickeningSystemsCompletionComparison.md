## What changed

Replaced the first worker's restatement with a constructive reduction of
`AlgebraicGeometry.thickeningSystems_completion_comparison`.
The existing signature, visibility, docstring, and public imports are unchanged.
The proof constructs the unit-normalized composition isomorphisms `c`, proves
coherence of the pullback terms, constructs the restriction functor `R` on objects
and arrows, and constructs `r` with identity components. Both required
compatibility equations are proved. Only the construction of the completion
isomorphism is delegated to the new module
`Sheaf.AlgebraicGeometry.CompletionFromRestriction`.

The auxiliary module and node supplied by the first worker were removed. They
repeated the entire original statement, adding only a `True` hypothesis, and
therefore did not constitute a reduction. The replacement theorem takes `c`,
`R`, `r`, and their proved equations as inputs and constructs only `ρ` and its
normalization equation. All new imports used only by proofs are plain `import`.

## Proved and sorry left

Hole closed in the item's source:
`AlgebraicGeometry.thickeningSystems_completion_comparison`
(node `lem-weil-pbc-thickening-systems-completion-comparison`).
Its proof still depends on open statements below it; it is not axiom-free.

Hole added, and the sole literal `sorry` in the delivered sources:
`AlgebraicGeometry.completion_from_restriction`
(node `lem-weil-pbc-completion-from-restriction`).
This is steps 4--5 of the previous plan, after steps 1--3 have been implemented.
One hole closed and one added: this delivery is a decomposition, with net zero
holes closed, not a completed proof of the item.

The first worker's `AlgebraicGeometry.thickeningSystems_completion_comparison_aux`
was never part of the baseline and is not delivered or counted as a closed hole.
Both delivered files compile locally. Scratch-copy `#print axioms` checks show
only `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx`.
There are no new definitions selecting data from existence statements. The
restriction functor is a concrete local construction; `ρ` is unpacked in a proof
of an existential proposition, rather than used to define public data.

## No longer needed

Removed the item's direct proof imports:

- `Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal`: `hgeom` already supplies the
  closed-immersion and ideal equations; no reconstruction by base change is used.
- `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback`: replaced with
  `Sheaf.AlgebraicGeometry.ModulePullbackFiniteType`; no support assertion is used.
- `Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`: needed only by the residual
  completion assembly, which imports it privately.

The old direct `proof_deps` no longer used directly by the item are
`lem-weil-pbc-quotient-base-change-closed-immersion-ideal`,
`lem-weil-pbc-support-pullback-finite-type`,
`lem-weil-pbc-closed-immersion-unit-quotient`, and
`def-sbc-ideal-sheaf-powers`. The last two remain dependencies of the residual node.
No claim is made that a module becomes unreachable from all targets: global module
pruning remains for the maintainer's import-closure calculation.

## Where the brief, the DAG or earlier work was wrong

The first worker merely relocated the entire goal behind a `True` parameter.
The auxiliary node's proof cited its parent, its recorded `lean.statement` still
named the original theorem, and its copied docstring lacked its own blueprint tag.
The parent's proof metadata had not been updated to reflect that implementation.
These defects are removed, rather than treating the wrapper as progress.

The original plan's suggestion to reconstruct closed-immersion geometry via
quotient base change is unnecessary because `hgeom` explicitly assumes it.
The finite-type support lemma is also stronger than the construction requires.

LeanSearch returned Internal Server Error. This is recorded as unavailable, not
as evidence of absence. LeanFinder returned restriction and pushforward comparison
lemmas but no completion assembly theorem. Loogle supplied the adjoint-uniqueness
and natural-isomorphism constructors used in the proof; local source searches
found no independent completion comparison with these normalization equations.

The local clone contains literature indexes but not `literature/stacks-project/coherent.tex`.
The cited source was checked on the authoritative Stacks pages:
[088F](https://stacks.math.columbia.edu/tag/088F),
[087T](https://stacks.math.columbia.edu/tag/087T), and
[0880](https://stacks.math.columbia.edu/tag/0880).
WANTED: local `literature/stacks-project/coherent.tex` for the completion assembly node.
The normalized categorical assembly details are marked agent-written.

## Second reading by C1

1. **Interface:** Compared the delivered item with the repository version.
   The existing theorem signature is byte-for-byte identical. Existing public
   imports and declaration visibility are unchanged. No definition or target
   statement is altered, so no change record is needed. The new theorem is in
   its own new module.
2. **Proof and trust:** Both files compile through `lcompile.py`, without errors
   or warnings. Only `completion_from_restriction` has a literal `sorry`, as its
   whole proof. Both axiom checks permit only the standard three axioms and the
   expected `sorryAx`; forbidden trust mechanisms and hollow definitions are absent.
3. **Residual statement:** The replacement is strictly the completion-isomorphism
   subargument: it assumes the explicitly constructed restriction data and both
   proved equations. Its docstring gives the quotient identification, adjunction
   transport, epi cancellation, naturality, and full-subcategory assembly argument.
   Checked the mathematical edge cases `I = 0`, `I = ⊤`, zero modules, the empty
   scheme, and level zero (which represents the first positive ideal power).
   There is no nonzero/proper-ideal assumption or illicit cancellation of a zero
   map: cancellation is of categorical quotient epimorphisms. Arbitrary supplied
   adjunctions are handled by unit-normalized uniqueness. Searches are recorded
   by `msearch.py`; the residual has no known duplicate in Mathlib or the library.
4. **Route and pruning:** Implemented the previous plan's restriction and
   adjunction steps directly, taking the finite-type pullback lemma instead of
   its support-enriched consequence. The residual retains the previous quotient
   and transition argument. Checked `dag/units/sk-thm-p1.json` and its `realized`
   fields: this helper is below the unit level, and no unit step is bypassed.
   All four old direct dependencies omitted by the new proof are listed above.
5. **Metadata:** Updated the parent's `proof`, `proof_deps`, and `proof_origin`
   to describe the actual construction and call to the residual. The new node's
   proof dependencies are exactly the union of its steps' uses, its Lean signature
   matches the new declaration, and it records its source, searches, provenance,
   chapter, unit, and blueprint ancestry. It has no dependency on its parent.

Second reading changed the entire restatement-only implementation into a genuine
restriction construction and completion-only decomposition, repaired all node
metadata, and removed unnecessary direct proof imports. The remaining completion
assembly is substantial and is left explicitly open.

## New nodes

`lem-weil-pbc-completion-from-restriction` records
`AlgebraicGeometry.completion_from_restriction` in
`lean/Sheaf/AlgebraicGeometry/CompletionFromRestriction.lean`. It constructs the
completion isomorphism from supplied restriction data and their compatibility
equations. It is the sole new hole, with a complete natural-language proof in its
docstring. No existing signature changes and no change records.
