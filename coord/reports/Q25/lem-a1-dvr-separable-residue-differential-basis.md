# Worker report

Item: lem-a1-dvr-separable-residue-differential-basis. Group Q25. Stage 1, direct delivery, 2026-10-24.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-a1-dvr-separable-residue-differential-basis.json: existing statement node, now split into five steps; Mathlib searches give no exact match or one-line specialization.
- citations.json: six entries, one for each cited node in each step, with verbatim statement quotations.
- report.md: this report.

Zero new nodes and zero new Mathlib leaves. The statement, stmt_deps, creation provenance and all inherited searches are retained. No Lean source was written and no compiler, Lake, build or local delivery-check script was run.

## Attachments

No attachment for the item. Searches of lean/WeilConjectures by its exact blueprint id and by uniformizer/differential/separable-residue/DVR terms found no declaration giving all its clauses. Algebra.separable_residue_cotangent_injective already belongs to lem-weil-pbc-separable-residue-cotangent-injective, lean/WeilConjectures/AlgebraicGeometry/SeparableResidueCotangentInjective.lean:63. I read this declaration and its proof; it is the existing input, not an attachment for the item.

## WANTED

None. The required Stacks sources are present locally.

## Source, blueprint and initial-node findings

I read GOAL.md, the worker brief, stage 1, SETUP.md (including its three blueprint levels), the chapter and unit records, worker role and delivery-errors.md B–E. There is no repair note for this item and the live item is unsplit. The sandbox initially contained only dispatcher marker files; there was no previous split or report to recover. coord/dag-sync.md referenced by the historical standing brief does not exist in this read clone; the current explicit brief supplies the read-only live-repository and delivery protocol.

The item is a valid algebraic extraction of Stacks curves.tex Tag 0C1E, lemma-uniformizer-works, proof lines 2421–2430, using algebra.tex Tag 00TU, lemma-computation-differential, lines 38687 onward. I verified both tags against tags/tags. The item assumes the DVR and rank-one differential assertions that the geometric source establishes separately; no finite type or smoothness assumption is needed for this extracted part. Its statement needs no correction.

The current blueprint place is literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-lem-wft-finite-map/lem-a1-finite-map-curve.proof.md, third paragraph. The current ancestor argument detects df by pole valuation over the perfect finite base field. This item remains the valid local-parameter input previously extracted under that ancestor; no chapter or unit route has been replaced or edited. The inherited item's unit is sk-thm-dl-a1-upper and is retained.

## Searches and reuse

I searched the whole DAG for 00TU, 0C1E, cotangent, separable residue and free rank-one modules, and ran tools/blueprint_refs.py ancestor for the item and search for cotangent, uniformizer differential, differential basis, unit coefficient differential, lemma-computation-differential and 0C1E. The existing 00TU node states the exact injection. The geometric parent lem-a1-uniformizer-differential-basis and sibling lem-a1-smooth-curve-closed-stalk-structure have stronger geometric hypotheses and are not exact attachments or replacement statements for this item. No new node is necessary.

All Mathlib calls were made with batch2/msearch.py and the actual log entries are appended to mathlib_searches. I used two phrasings, LeanFinder, Loogle, LeanSearch and grep. I read the returned signatures: DVR cotangent finrank one is not the universal differential injection; the standard-smooth bases depend on a presentation; the formal-smoothness criteria in Mathlib/RingTheory/Smooth/Local.lean assume a formally smooth presentation source. None gives the whole item by a one-line specialization. The inherited 2026-10-22 searches remain intact. Additional exploratory queries under candidate ids for a separability-convention conversion and a unit-coefficient fact were run, but no such nodes were created: the first is an elementary empty-transcendence-basis argument, and the second is a two-line tensor-balancing calculation, so creating them would violate the no-elementary-node rule.

## Tool uses

lem-weil-pbc-separable-residue-cotangent-injective is used as the generic commutative-algebra tool of Stacks 00TU, exactly as 0C1E uses it. It is recorded Lean-closed and does not replace a unit step. The declaration is included in split_report.tool_uses for clarity, not as a maintainer-owned top-level tool_uses edit.

## Not duplicates

No new nodes; no new/existing pairs require justification. Reusing the existing 00TU node avoids a duplicate.

## Review by Q25

I checked the unchanged item against curves.tex 0C1E and the actual hypothesis list of algebra.tex 00TU. In particular, the source injection assumes only Noetherian locality, a k-algebra, and finitely generated separable residue extension; it does not require A to be essentially of finite type, smooth, complete, or equicharacteristic beyond its k-algebra structure. The finite separable residue extension of this item satisfies those assumptions. I read each of the four distinct cited nodes' statements, rather than using their proofs.

Step 1 cites def-sc-discrete-valuation-ring for precisely its domain and nonzero maximal-ideal clauses. The calculation m²=t²A and cancellation t=t²b ⇒ 1=tb explicitly prove the nonzero cotangent class. The nonzero hypothesis for cancellation follows from m=tA and m≠0. This is elementary and invokes neither Nakayama nor a hidden cotangent-dimension theorem.

Step 2 cites def-weil-pbc-separable-algebraic-extension (every element has separable minimal polynomial) and def-weil-pbc-separable-field-extension (every finitely generated intermediate extension is separably generated). I checked the latter is the general, possibly transcendental convention. The argument explicitly matches them here: a finite vector-space basis generates κ as a field; for an intermediate F, the evaluation kernel in k[T] of an element is independent of the ambient field, so its minimal polynomial remains separable; the empty transcendence basis witnesses separable generation because F/k is algebraic. This is an unpacking of the definitions, not an invocation of an unstated general separability theorem.

Step 3 cites only lem-weil-pbc-separable-residue-cotangent-injective. Its statement includes the actual formula [a] ↦ da⊗1, not merely an abstract injective map or a dimension equality. All of its hypotheses are either given in the item or checked in Step 2. Thus Step 1's nonzero class has nonzero image. The node is independently recorded Lean-closed; I also read its project theorem and saw its tensor order is reversed only by the canonical symmetry, as its docstring explains.

Step 4 cites def-weil-pbc-free-module for unique coordinates in a basis. It works in any chosen one-element basis e of this rank-one module. If dt=ae and a∈m, the tensor relation dt⊗1=e⊗a-bar=0 contradicts Step 3. In a local ring nonunits constitute its maximal ideal, so a is a unit. This proves the clause for every rank-one basis and supplies the inverse coefficient; it does not hide a Nakayama application or a base-change freeness theorem.

Step 5 again uses only the unique-coordinate description in def-weil-pbc-free-module. I checked ψ(ce)=ca⁻¹ is well defined and A-linear, and both composites are computed in the text. The order is consistent with a commutative ring and gives precisely the inverse in the statement. The initial t is arbitrary, so no existential conclusion has replaced the universal uniformizer quantifier.

For edge cases I checked A=k[T]_(T) with t=T and t=uT for a unit u: d(uT) reduces to u-bar dT and has unit coefficient, as required. At a nonrational separable point given by an irreducible separable f, the residue derivative f' is nonzero, giving the same conclusion. The excluded inseparable example k=F_p(a), A=k[T]_(T^p-a), t=T^p-a has dt=0, which confirms separability is essential. A field is excluded by the DVR definition's m≠0 clause; otherwise t=0 would refute the first assertion. The ring k[[T]] was not used to infer rank-one ordinary Kähler differentials: those differ from continuous differentials, and the item explicitly assumes rank one.

Against delivery-errors B–E: there are no new statements or duplicate nodes; no clause is moved to a renamed copy; every non-elementary input is the existing cited injection; all citations have their literal statements in citations.json; all steps are below 2000 characters (the complete proof is about 2241 characters); no circular dependency is introduced and no SGA source appears. The report's initial review and source reads revealed no statement error. The significant improvement over the empty initial proof is making the separability convention, cancellation, tensor vanishing and inverse formulas explicit. The maintainer's required server dry run is the final structural verification before pushing.

## Unfinished work

None in the stage-1 split. The dry run and direct push are performed using the prescribed delivery tool.
