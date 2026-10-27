# Worker report: def-sfb-nonnegative-strict-graded-algebra

## Files written

- dag/nodes/sec-six-functors-basics/def-sfb-nonnegative-strict-graded-algebra.json: definition, split; no exact Mathlib match for strict graded commutativity. Existing underlying grading dependency remains the Mathlib leaf def-sfb-nonnegative-graded-algebra.
- citations.json: two verbatim excerpts, one for each proof step.
- searches.jsonl: actual msearch.py results, including both semantic phrasings.
- report.md: this report.

No new nodes and no new Mathlib leaves.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and for strictly graded, StrictGraded, GradedComm, and odd-square language. The SelfTorConormalComparisonTateConstruction, SelfTorConormalComparisonExistence, and KoszulIdealAlternatingProducts occurrences concern particular Tor comparison maps; their declarations do not define the general graded algebra and its parity parts. They do not attach this item.

## WANTED

None. The source is available locally.

## Findings and changes

The imported statement is faithful to Stacks dpa.tex, Tag 09PF (section-tate), introductory paragraphs at lines 951–962, and the observation after Tag 09PG (definition-divided-powers-graded), lines 985–990. Its statement and statement dependency were retained verbatim. The definition already names its underlying grading, which is a Mathlib leaf. Added two elementary proof steps for the finite-sum interpretation of the parity submodules and for the last sentence's subalgebra and ideal claims; these do not hide a non-elementary lemma and do not merit new nodes. No STATEMENT-DISPUTED or source error was found.

Read the chapter and unit records and the latest blueprint's sk-thm-sf-ctf-stability unit and direct-image proof. This auxiliary algebraic definition does not replace a unit proof step. blueprint_refs.py ancestor reports a null blueprint ancestor; the inherited detailed place and via chain are preserved. Whole-blueprint searches for strictly graded and graded commutative found no equivalent definition (the latter returned Proj and homogeneous-localization notions). DAG searches for 09PF, 09PG, and strict graded commutativity identify the existing grading, divided-power, and Tor nodes, not a second definition of the same notion. No new nodes were created.

Mathlib searches used the required msearch.py commands for leanfinder, loogle, grep, and leansearch, plus a second leanfinder phrasing. All ran successfully. Read GradedRing/GradedAlgebra in RingTheory/GradedAlgebra/Basic.lean, lines 48–67 and 163–172; ExteriorAlgebra/Grading.lean, lines 30–72; and the tensor-product comm braiding in TensorProduct/Graded/Internal.lean, lines 360–385. The general grading has no sign or square axiom. Exterior-algebra results concern a particular construction, and the tensor braiding does not assert commutativity of multiplication on a general algebra. Hence the strict structure is not a Mathlib leaf. Preserved the inherited earlier search records and appended only the searches actually run for this item.

## Unfinished work

None within stage 1. No Lean was written, compiled, or built. The repository and launcher were not modified. The brief's inherited reference to coord/dag-sync.md names a file absent from this read clone; the explicit current live-repository instructions govern this delivery.

## Review by Q43

I read dpa.tex from the start of section-tate through definition-divided-powers-graded and its following observation. The source assumes an arbitrary commutative base ring and a nonnegative graded algebra, then imposes both the signed product rule and the independent odd homogeneous square-zero condition. The item has precisely those assumptions. It does not require the ambient algebra to be ordinarily commutative, nor assume that 2 is invertible.

For step 1 I opened the statement of def-sfb-nonnegative-graded-algebra. It explicitly gives R-submodules, an isomorphic internal sum map, the unit in degree zero, multiplicative degrees, and the negative-degree convention. Finite sums supported on even, odd, or positive even indices therefore form the indicated submodules; the full sum's injectivity supplies the internal interpretation. Nothing is taken from the dependency's proof.

For step 2 I again use exactly that node's unit, scalar-image, and degree-addition clauses. The item's own defining sign axiom becomes +1 on even-even pairs. Finite distributivity then proves commutativity for arbitrary even sums and multiplicative closure. The inequality i+j>0 for i>=0 and j>0 proves the ideal assertion. Ring laws restrict from A. These are two short elementary calculations, so there is no uncited algebraic theorem or new clause-restatement node. Both citation excerpts are the exact dependency statement, checked against the live JSON. proof_deps is exactly the union of uses.

I checked B1–B10: no new nodes; all objects and conditions are introduced, single TeX escaping is preserved, the exact source tag and label are read, all logged new searches ran, and all plausible matches were inspected and rejected for their missing strict conditions. I checked C1–C8: the two steps use only the stated grading and elementary finite-sum arithmetic, with no hidden theorem, no proof-only citation, no new dependency cycle, and no off-unit theorem citation. I checked D1–D5: the actual closure and sign arguments are written, with nothing moved into another node. I checked E1–E7: no extra base-ring hypothesis is used, and the two parity parts are actual submodules inside A.

For edge cases, an algebra concentrated in degree zero has zero odd and positive-even parts; the ideal is then zero. The zero ring and zero algebra satisfy the same equations. In characteristic two, F_2[t] with t in degree one obeys the signed commutation rule but has t^2 nonzero: this confirms why the second strictness axiom must remain independent. An exterior algebra provides the expected strict example. Even-even commutativity uses no cancellation of 2. The positive-even submodule is claimed as an ideal only in the even algebra, exactly as the source says. Each proof step is below 2000 characters, and neither hides a separate non-elementary comparison or identification.
