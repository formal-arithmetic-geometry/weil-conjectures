## What changed

Audited the assigned repair against upstream review #1428. The repository already
contains E4's corrected and proved descent-and-openness statement, documented in
`coord/changes/stalk-normalization-depth-two-section-flat-core.md`. Preserved its
signature, visibility, imports and docstrings. Simplified the faithful-flatness
proof: pass the projection's flat stalk map and its local-ringed-space local-map
property directly to `Module.FaithfullyFlat.of_flat_of_isLocalHom`, rather than
registering and transporting two local instances. No consumers are adapted.

Read the core node, its two proof dependencies and their Lean proofs, and unit
`sk-prop-input-spreading`. The existing DAG describes the unchanged proof route:
lift each source point over x to the pullback, descend stalk flatness through its
flat local projection, then take the finite flat target locus. No node edits are
needed. This is a repair audit and proof simplification, not new proof progress.

## Proved and sorry left

`AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`
(node `lem-sbc-stalk-normalization-depth-two-section-flat-core`) was already
proved and remains proved. Starting holes: zero; holes closed: zero; holes
added: zero. No sorry remains in the module; no new modules or statements.
The original compiled without warnings in 3.8 seconds. The simplified proof compiled without warnings in 3.5 seconds. An independent
scratch copy of that exact proof with `#print axioms` compiled in 4.0 seconds
and reported exactly `propext`, `Classical.choice`, and `Quot.sound`. The
delivery dry run additionally probes all declarations for forbidden axioms.

## No longer needed

None. Both proof imports are needed: `FiniteFlatTargetLocus` supplies openness,
and `WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` supplies
algebra flatness descent. No node or module is pruned.

Repeated Loogle (`Module.Flat, Module.FaithfullyFlat`), Lean Finder (flatness
near a point from a flat test meeting it), and local library/Mathlib searches.
They find the stalk criterion already used and algebraic descent variants.
The source-library scheme descent theorem requires a globally surjective test,
which the present theorem does not assume. Its explicit local-map proof supplies
the simplification here. No shorter matching public scheme theorem was found.

## Where the brief, the DAG or earlier work was wrong

The repair queue still refers to the obsolete normalization-only statement.
It has already been replaced in the repository by the true general descent
lemma. Do not add redundant rational-point data to this general lemma: it
explicitly assumes `Flat (pullback.snd p t)` and does not infer that from depth.
The normalization caller `GaloisCover.stalk_normalization_depth_two_section_flat`
has the rational-point hypothesis `hZ` and passes it into
`GaloisCover.exists_stalk_normalization_split_formal_test`; its splitting
isomorphism establishes pullback flatness before calling the core. The second
caller, `PuncturedLocalPurityFiniteFlatFiber`, obtains pullback flatness by
identification with a finite etale extension. Neither caller needs changing.
The existing statement-change record and core node already record this repair.

Checked edge cases: an empty fibre makes membership in the flat target locus
vacuous; an empty test cannot supply b; the test need not be surjective away
from x because only pairs of points above x are lifted. The cone counterexample
cannot bypass the explicit flat-test hypothesis. The unit's formal completion,
splitting, descent and openness route is preserved, and no target changes.

The earlier sandbox report described a proof-local classical removal already
landed in the current repository. Replaced that stale report and its old second
reading with this account; the independent second reader supplies a new reading.

## Second reading by T4

1. Compared the sole delivered module with the repository using `diff -u`.
   PASS: only the body of the local faithful-flatness proof changes. The existing
   theorem signature, visibility, documentation, and all imports are byte-for-byte
   unchanged. No definitions or consumer modules are changed.
2. Compiled the delivered file locally using `lcompile.py`, with no errors or
   warnings. Regenerated the scratch axiom-check copy from the delivered file
   (the previous scratch copy contained the repository proof), then compiled it.
   PASS: the theorem uses exactly `propext`, `Classical.choice`, and `Quot.sound`;
   no `sorry` or prohibited declarations occur in the delivered file. The explicit
   arguments to the local-ring faithful-flatness theorem are the flat projection
   stalk map and the local-map property of that same morphism.
3. PASS: no statements are split off, no new nodes are introduced, and no holes
   remain or are added. Independently checked the empty-fibre case (vacuous),
   empty-test case (excluded by b), and a test meeting only x (the proof lifts only
   source points over x). No arbitrary data are chosen from unproved existence.
4. Read the proof from the conclusion down and checked both dependency proofs.
   PASS: the finite flat target locus gives the desired neighbourhood; every
   stalk above x is flat by faithful-flat descent from the pullback. The two
   proof-only imports are used explicitly and remain plain imports. The public
   imports supply the theorem's Noetherian, finite, and flat hypotheses. A local
   search for flat source descent and faithfully-flat algebra descent confirms
   that the existing scheme theorem requires global surjectivity, absent here.
   No old proof dependency is unused. Read `sk-prop-input-spreading`, including
   its `realized` field: no unit realization or formal-splitting route is removed.
5. Read the core node and the nodes for algebraic descent and the finite flat
   target locus, including their Lean attachments. PASS: `proof`, `proof_deps`,
   and `proof_origin` describe precisely the unchanged two-step argument. No DAG
   edit is needed for this proof-term simplification. The already landed statement
   repair is documented in its existing change record and is not redelivered.

Second reading changed only this report and regenerated the scratch axiom check;
no further Lean repair was necessary. This delivery is an audit and simplification
of an already proved repair item: zero holes closed, zero holes added, zero split
statements, and no pruning.
