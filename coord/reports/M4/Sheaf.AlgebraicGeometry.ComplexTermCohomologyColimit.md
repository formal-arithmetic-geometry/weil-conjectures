## What changed

Closed `AlgebraicGeometry.Etale.nonempty_isColimit_complex_term_cohomology` without
changing its signature. Evaluate the complex diagram, its object isomorphisms, its
transition equations and its colimit cocone at the chosen degree. Evaluation preserves
colimits. The evaluated coherence equations and the two prescribed cohomology equations
then give a complete Lean application of ordinary cofiltered continuity.

Added `Sheaf.AlgebraicGeometry.CofilteredEtaleCohomologyContinuity`, which isolates the
ordinary sheaf continuity argument for a small cofiltered category. This removes all
complexes, differentials, complex evaluation, and preservation of complex colimits from
the remaining task. Its documented argument is directed replacement by Tag 0032 followed
by the existing directed-order continuity theorem, so the unit's continuity route stays.

Private proved component-map equalities, local reducibility settings, and explicit
normalization of evaluation and constant-functor expressions avoid repeated expansion
of the underlying Ext constructions. Instance arguments must be normalized too. No
existing definition, statement, visibility, instance or target was changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.nonempty_isColimit_complex_term_cohomology`
(`lem-weil-pbc-complex-term-cohomology-colimit`). Its proof contains no `sorry`.

Added one strictly simpler named hole:
`AlgebraicGeometry.Etale.nonempty_isColimit_etale_cohomology_of_cofiltered_isLimit`
(`lem-weil-pbc-cofiltered-etale-cohomology-continuity`). Its proof is exactly `by sorry`.
This is ordinary sheaf continuity, without complexes or their evaluated-colimit step.
The source and complete directed-reindexing argument are in its docstring and node.

This delivery is a decomposition: one upper hole closed and one scalar hole added,
not a net reduction in holes or a claim of an axiom-free proof. The original module
compiled cleanly against the scalar intermediate theorem. The unfinished attempts at
proving the scalar reindexing argument are kept only in scratchpad, outside the delivery.

## No longer needed

The original module no longer directly imports
`Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes` or
`Mathlib.CategoryTheory.Presentable.Directed`; those remain in the scalar theorem's
planned directed-reindexing route. The old direct proof dependency
`lem-weil-pbc-etale-cohomology-limit-of-schemes` is now used transitively through
`lem-weil-pbc-cofiltered-etale-cohomology-continuity`. No live module or existing
proof-dependency node is transitively pruned.

Discarded the earlier sandbox-only module
`Sheaf.AlgebraicGeometry.ReindexedComplexTermCoherence` and its proposed node
`lem-weil-pbc-reindexed-complex-term-coherence`. They had not landed and are not part
of this delivery. Evaluation coherence is now proved directly, with no new hole.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt added a coherence hole without closing the original hole. The
present reduction proves all three evaluated coherence equations directly and closes
the original declaration. The original mathematical plan was sound; evaluating first
and performing directed replacement on scalar sheaves gives a clearer separation of
its two steps.

Lean's slow comparisons were not solely the `upperStarComp` transports. In particular,
cohomology maps with unreduced constant-functor or evaluated-cocone expressions caused
large Ext/derived-category computations. Explicit `dsimp` normalization, including
instance arguments, resolves the original theorem's comparisons. The scalar theorem's
full directed-reindexing attempts still exceeded the 60-second limit; no partial proof
or hidden definition data from them is delivered.

## New nodes

`lem-weil-pbc-cofiltered-etale-cohomology-continuity` records ordinary etale continuity
for small cofiltered categories. Its statement is the scalar continuity part of the
argument, with a directed-order reduction following Stacks Tags 0032 and 09YQ. The
original node now records direct evaluation followed by this scalar result; its
statement and statement dependencies are unchanged. The change record
`coord/changes/complex-term-cohomology-local-elaboration.md` documents the local
attribute commands required by the static checker; they change proof elaboration only.

## Second reading by M4

1. PASS: Diffed the existing module against the repository. The original theorem's
   signature is byte-for-byte unchanged and matches its node's `lean.statement`.
   No existing definition, visibility, instance, or target changed. The local
   reducibility attributes and declaration-scoped options affect elaboration only;
   the change record describes them. No other existing module is adapted.
2. PASS: Both delivered modules compile locally with `lcompile.py --all`, without
   errors or warnings (6.4 seconds for the scalar statement, 50.6 seconds for the
   complex proof). The only delivered `sorry` is the named scalar continuity theorem.
   No forbidden axiom command, unsafe/opaque declaration, external implementation,
   definition hole, or data chosen from an unproved existence theorem occurs.
   Scratch-copy `#print axioms` checks for both public theorems compiled
   successfully and showed exactly `propext`, `Classical.choice`, `Quot.sound`,
   and `sorryAx`, as expected from the documented open scalar dependency.
3. PASS: Read the scalar statement against directed continuity and Stacks Tags
   09YQ and 0032. Its docstring and new node give the full directed-reindexing proof.
   Cofilteredness excludes an empty index; a singleton index gives an isomorphism
   cocone; zero sheaves, degree zero, empty schemes, and nontrivial index morphisms
   require no added hypotheses. Finality preserves the sheaf colimit and reflects
   the cohomology cocone's colimit; initiality preserves the scheme limit. The
   arrow condition cancels the target isomorphism to recover the directed theorem's
   arrow formula. This scalar theorem omits complexes, differentials, degree
   evaluation, and evaluation's preservation/coherence work, all genuinely proved
   by the original module. It is a strictly smaller part of the argument, rather
   than the same complex statement under another name.
   Independently searched with LeanFinder (inverse-limit sheaf cohomology query),
   Loogle (`IsFiltered.exists_directed`, unavailable identifier in its index),
   launcher grep and `rg` over both library roots. No exact scalar theorem exists;
   fixed-base continuity requires one sheaf pulled back from a fixed base and does
   not cover arbitrary varying sheaves here. Mathlib's directed replacement and
   final/initial whiskering equivalences provide the categorical ingredients.
4. PASS: The proof first evaluates the complex colimit using Mathlib and proves
   all three scalar coherence equations by taking components; only scalar
   continuity remains open. The two replaced direct imports and the old direct
   node dependency are listed under No longer needed, with no transitive pruning
   claimed. The scalar module retains the directed-continuity and replacement
   proof imports for its documented remaining route. Read
   `dag/units/sk-prop-h2.json`; no realized statement or step is bypassed, and
   directed ordinary continuity remains in the dependency route.
5. PASS: Both Lean signatures match their node records exactly. The existing node
   changes only the owned proof fields and records evaluation followed by scalar
   continuity. Its statement, statement dependencies, and Lean record are unchanged.
   The new node has source, searches, creation, blueprint origin, chapter, unit,
   Lean record, and a proof whose uses union equals its proof dependencies.

Second reading changed the original theorem's stale proof docstring to describe
its actual evaluation-first proof, made the old direct node dependency explicit
in No longer needed, and added this review. No Lean proof or statement needed repair.
The result remains a decomposition: one original hole closed, one scalar hole
added, zero net holes removed; the remaining scalar theorem is not claimed proved.
