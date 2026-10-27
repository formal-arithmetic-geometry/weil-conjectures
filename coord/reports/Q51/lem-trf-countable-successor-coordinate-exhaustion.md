# Stage-1 report: lem-trf-countable-successor-coordinate-exhaustion

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-countable-successor-coordinate-exhaustion.json`: item, statement unchanged, split in six steps.
- `dag/nodes/sec-trace-formula/lem-trf-countable-unions.json`: statement, Mathlib leaf; `Set.Countable.biUnion`, `Set.countable_iUnion`, `Set.Countable.union`, Mathlib/Data/Set/Countable.lean:214–242, one declaration per clause.
- `citations.json`: four verbatim statement quotations for all four step/node citations.
- `searches.jsonl`: actual msearch log; item retains the inherited searches as well as this run's searches.
- `report.md`: this report.

## Attachments

None. Searched the project source under `lean/WeilConjectures/` for the exact blueprint tag and for countable successor closure, coordinate submodules, countable unions and exhaustion. No project declaration states the item. The related `DirectSum.exists_countable_coordinateSubmodule` in `lean/Sheaf/RingTheory/CountableCoordinateClosure.lean` is only the parent existence statement and its proof is `sorry`; it neither supplies the prescribed stages nor attaches this item. Mathlib's countable finite exhaustion chooses a different sequence; its stages must be finite, whereas the present stages may already be infinite at stage zero.

## WANTED

None. Read Stacks `literature/stacks-project/algebra.tex`, Tag 058X, `theorem-kaplansky-direct-sum`, particularly lines 20511–20552. Read the latest blueprint ancestor `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`, and its unit and chapter. The countable-union fact is implicit in the Stacks enumeration of countable rows; the new leaf records its explicit general form as proved in Mathlib. No SGA source is used.

## Corrections and scope

The item was unsplit and had no proof. Its statement is correct as written, including at-most-countable sets, the empty finite subset, and arbitrary modules and ring. The new proof makes the countability induction and finite-subset induction explicit. The set union of coordinate submodules is taken inside the same external direct sum; no identification with an abstract colimit or a submodule supremum is needed. The only new node is a general Mathlib theorem about unions, not a new node restating successor closure or coordinate exhaustion.

The current latest ancestor proof is the Varshavsky contracting-correspondence proof and no longer displays the old Kaplansky detour. I preserve the imported ancestry and explicitly describe the historical Tag 058X subargument in `split_report.blueprint`; the stage-1 item remains the assigned set-theoretic support lemma. The explicit recursive formulation and its proof are marked agent-written rather than misattributed as a verbatim theorem of Stacks. No chapter, unit, target, statement hypothesis or conclusion was changed.

## Not duplicates

lem-trf-countable-unions vs def-sfb-countable-set: the existing node defines countability by an injection into the natural numbers; the new leaf uses that definition and proves preservation under indexed and binary unions.

The whole DAG was searched by countable-union wording and by `countable_iUnion`, `Countable.biUnion`, `Countable.union`; the only existing use of those declarations is in this item's search history. Blueprint searches for `countable`, `countable union`, `countable unions`, and `countable successor` found no blueprint statement of the new leaf or item. All existing nodes mentioning the same Stacks tag were read for their statements:

lem-trf-countable-unions vs def-trf-coordinate-submodule: the new leaf proves countability of unions of sets; the existing definition specifies supported vectors in a module.

lem-trf-countable-unions vs lem-trf-split-transfinite-module-filtration: the existing theorem decomposes a module with split transfinite successor inclusions; it does not assert countability of arbitrary set unions.

lem-trf-countable-unions vs lem-trf-countable-coordinate-closure: the existing theorem constructs an invariant coordinate enlargement under an endomorphism of countably generated summands; the new leaf has no modules or endomorphism and proves only set-union countability.

lem-trf-countable-unions vs lem-trf-transfinite-successor-generators-surjective: the existing theorem proves surjectivity of a direct-sum map from transfinite successor generation, with no countable-union assertion.

lem-trf-countable-unions vs lem-trf-invariant-coordinate-transfinite-filtration: the existing theorem builds a transfinite filtration from specified invariant countable enlargements; its statement does not give the general set-union theorem used to establish countability of natural-number recursive stages.

lem-trf-countable-unions vs lem-trf-projective-countable-decomposition: the existing theorem decomposes projective modules into countably generated summands; it does not state union countability for sets.

lem-trf-countable-unions vs lem-trf-countable-successor-coordinate-exhaustion: the item proves properties of prescribed recursively enlarged stages and exhaustion of coordinate submodules; the new leaf has only arbitrary indexed set unions and no recursion or coordinate conclusion.

lem-trf-countable-unions vs lem-trf-idempotent-coordinate-filtration-quotients: the existing theorem describes retractions and quotient generators in an idempotent-invariant module filtration, rather than arbitrary set unions.

lem-trf-countable-unions vs lem-trf-countably-generated-image-support: the existing theorem constructs a generating sequence and bounds supports of images of a countably generated module; it does not state the general union theorem.

lem-trf-countable-unions vs lem-trf-filtration-successor-maps-independent: the existing theorem proves injectivity of a finite-support sum under independence assumptions in a transfinite filtration; it has no countability conclusion.

lem-trf-countable-unions vs lem-trf-projective-kaplansky-direct-summand: the existing theorem decomposes a summand of a sum of countably generated modules; it does not state a countable-union theorem about arbitrary sets.

## Review by Q51

I read Tag 058X's matrix construction, where countable rows enumerate generators and further rows include all summands reached by earlier projection images. The assigned lemma isolates the underlying successor enlargement; it does not use the countable-generation hypotheses of that larger algebraic theorem. I read the actual Mathlib proofs at Countable.lean:214–242: `countable_iUnion` accepts an arbitrary countable index, `Countable.biUnion` at line 233 is the reverse direction of the equivalence at 225–228 for a countable subset of an otherwise arbitrary index set, and `Countable.union` at 241–242 accepts two countable subsets. These are exactly the three clauses of the new leaf. The ambient sets need not be countable. This is the only non-elementary ingredient I added, with actual logged searches and exact source lines, and it is a Mathlib leaf with an empty proof.

Step 1 uses only the displayed recurrence and the definition of union. Its stage inclusions, their finite iteration, and inclusion of C do not require a separate lemma. Step 2 cites the new leaf: I checked its restricted-union clause with S=A_k, B_j=F_j and X=I=J. The induction hypothesis supplies countability of S, and the item's assumptions supply countability of every F_j. The binary-union clause then supplies the stated successor countability. Step 3 cites its sequence clause with T_k=A_k; the natural-number index and countability hypotheses are exactly those established in step 2. Neither step assumes the underlying modules are countable.

Step 4 uses membership witnesses for the union D and the very next successor stage, so it proves all successor sets are included without invoking a closure theorem. Step 5 proves finite-stage containment by an explicit induction adding one element. I checked the empty base separately and that the maximum of the old stage and the new element's stage works by step 1. The elementary finite-subset argument is retained inside the item's proof, rather than made into a node that merely restates a clause of the item.

For step 6 I opened both cited definition nodes. The direct-sum statement explicitly defines its elements as families with only finitely many nonzero coordinates. The coordinate-submodule statement explicitly says that membership means vanishing outside its subset. These statements alone give finite support contained in D, and step 5 gives one containing stage. The reverse inclusion uses A_k contained in D. The four citations in citations.json are verbatim substrings of those exact statements, including the leaf's two uses. No proof of a cited node was substituted for its statement.

I tested C empty (every stage and D empty), all F_j empty (every stage equals C, which may be infinite), a chain J=natural numbers, C={0}, F_j={j+1} (A_k={0,...,k}), the empty finite subset with k=0, J empty, and the zero vector. For the coordinate argument, modules over an uncountable ring and arbitrary non-countably-generated modules still have finite-support direct-sum elements, so all inclusions are unchanged. No statement dispute or added hypothesis is needed. The first server preflight requested an explicit notion citation on the new leaf and the separate numeric Mathlib line field. I read and reused `def-sfb-countable-set`, whose statement defines countability by injection into the natural numbers, and specified that set countability applies to the underlying subtype. I added `mathlib_match.line = 233`; the other two exact declaration lines remain in `how`. These repairs change no hypothesis or conclusion.

I checked B–E: every new object is introduced, the new leaf contains only a statement and no hidden proof, TeX has ordinary single escapes, sources name the Stacks tag and label, Mathlib matches have verified lines and clause correspondence, all searches were actually run, and duplicate checks cover every node sharing 058X. All non-elementary uses are cited nodes, each citation says what the step takes, and there is no circular dependency. All six steps are below 2000 characters; the proof contains no long hidden comparison or identification. No Lean was written, no compiler run, and no repository or launcher file modified.

## Unfinished work

None in the one-level split. Required server checks and delivery are run after this report is written.
