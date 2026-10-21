## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_bounded_continuity` in
`Sheaf.Paper.ClosedSupportBoundedContinuity`. Its statement is byte-identical to the original,
and all four public imports are unchanged. Updated the item's DAG proof, proof dependencies,
and proof origin to match the implementation. No other library module was changed.
`coord/changes/closed-support-continuity-local-proof-scopes.md` records the extra universe
names and the local irreducibility attributes, as required by the static command-scope check.

The shorter route uses the existing internal-module theorems
`condensed_closed_costalk_derived_continuity` and `condensed_qcqs_pushforward_continuity`.
For the former, the actual `closedSupportAdjunction` supplies the chosen right adjoint.
Thus the existing support-triangle argument applies to precisely the recorded kernel functor.
For the latter, the Noetherian topology makes the open immersion quasi-compact; its
monomorphism property supplies quasi-separatedness.

Six proved private helpers provide the comparison argument. Exact filtered colimits preserve
objectwise quasi-isomorphisms. Good truncation extends continuity from a strict lower bound
to the stated cohomological bound. Natural isomorphisms preserve the maps induced by the
original cocone. Finally, a natural isomorphism between the total right derived functor and
the prescribed functorial K-injective model identifies every homology comparison; exactness
of filtered colimits and `colimit.post_post` give the two required quasi-isomorphisms.
`exactDerivedAdjunction_isGE`, applied to the two actual exact-left-adjoint derived
adjunctions, proves both lower-bound assertions.

The source read was Hemo--Richarz--Scholbach, Lemma 5.3 and its proof, including the final
closed-support fibre-sequence paragraph, together with (3.3)--(3.4), Lemma 3.4, and Stacks
`proetale.tex`, `lemma-closed-immersion-complement-retrocompact-exact` (09BM).
The unit `sk-def-sfb-dc-restricted-functors` and its realized record were checked; its
statement and both steps are unchanged. The continuity results and the generic exact-derived
adjunction result are reused tools; their declarations and hypotheses were read, and neither
their imports nor their DAG dependencies reach this item.

The earlier delivery compiled cleanly in 37.0 seconds, with a temporary `#print axioms`;
that diagnostic is absent from the delivery. The repair compile against the current restored library passed cleanly in 12.3 seconds
(exit code 0). The first request received the documented busy-server response; the retry
succeeded without a code change or any limit adjustment. Earlier profiling isolated expensive instance inference: explicit functor arguments and comparison morphisms, a typed truncated
diagram, and local irreducibility of existing monoidal/coefficient constructions give the
compiling proof. No limit, shared definition, or launcher script was changed.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_bounded_continuity`
(node `lem-sfb-closed-support-bounded-continuity`). All four conjuncts are proved.

Zero holes remain in the item. Zero holes were added; zero statements were split off.
Every private helper is proved, and the private natural-isomorphism definition is an explicit
construction without postponed data. The axiom diagnostic still reports `sorryAx` through
existing library dependencies, in addition to `propext`, `Classical.choice`, and `Quot.sound`.
This delivery closes the item's proof hole from existing declarations; it does not claim
that their entire transitive proof closure is finished.

## No longer needed

Removed these seven proof-only imports:

- `Sheaf.Paper.CondensedOpenClosedRecollement`
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage`
- `WeilConjectures.Algebra.Homology.FilteredColimitsTensor`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`

The corresponding direct DAG dependencies are omitted:
`def-weil-pbc-internal-abelian-sheaf-module-equivalence`,
`det-pe-bounded-continuity-direct-image`, `lem-pc-module-filtered-colimits-tensor`,
`lem-sf-derived-homology-long-exact`, `lem-weil-pbc-condensed-open-closed-recollement`,
`lem-weil-pbc-five-lemma`, `lem-weil-pbc-module-sheaves-colimits-forgetful`,
and `sk-def-sfb-module-pushforward-pullback`.

The native condensed-module continuity theorem avoids the section-ring equivalence and
restriction-of-scalars bridge. The existing closed-costalk continuity theorem already
combines the support triangles and five lemma. The module categories' Grothendieck instance
supplies exact filtered colimits directly. The proof uses the recorded total right derived
functor. `Sheaf.Paper.CondensedModuleDerivedPushpull` and its DAG dependency are retained
because they belong to the unit route, as the delivery preflight requires.

Removed the six old `tool_uses` approvals, exactly
`det-pe-bounded-continuity-direct-image`, `lem-weil-pbc-condensed-open-closed-recollement`,
`lem-pc-module-filtered-colimits-tensor`, `lem-sf-derived-homology-long-exact`,
`lem-weil-pbc-five-lemma`, and `lem-weil-pbc-module-sheaves-colimits-forgetful`, because none
is a direct input of this proof. No new maintainer approval was inserted.

These removals concern this item's direct proof. Imported results keep their own required
imports and dependencies. No module or declaration is withdrawn, and no adopted source-library
file is edited. In particular this is not a claim that every listed module leaves the
whole target import closure.

## Where the brief, the DAG or earlier work was wrong

The planned support-triangle proof is mathematically sound, but it duplicates the existing
closed-costalk continuity theorem. That theorem accepts any additive right adjoint of the
same closed pushforward, so it can be specialized to the canonical `closedSupport` directly.
The native condensed qcqs continuity theorem similarly removes the coefficient-presentation
bridge. The remaining good-truncation and original-cocone comparisons are implemented in Lean,
including naturality of the K-injective resolution comparison.

Repair of return `60fcc15eb88` (2026-10-21 12:03 UTC): read the rework row and checked
U2's existing claim before using the archived source. The current shared tree has now
restored `lean/Sheaf/Paper/ClosedSupportBoundedContinuity.lean`; its content is
byte-identical to the quarantine archive and still has the original theorem hole.
The packet fills that hole with the retained complete proof. Its direct and transitive
proof imports are present in the restored tree, including
`Sheaf.Paper.CondensedClosedCostalkDerivedContinuity`. The public theorem statement is
byte-identical in the archive, current library and sandbox. The node retains its Lean
attachment and statement dependencies; only the proof route fields and obsolete tool-use
entries change. Neither the item nor any archive is deleted, and `deleted.txt` is absent.
This is a proof of the restored theorem, not an empty replacement or an unchanged re-push.

No statement or definition repair was needed. No extra finiteness, upper bound, or
constructibility hypothesis was introduced. The comparison helpers work for every integer
bound, and the argument also applies when either complementary subscheme is empty or the
coefficient ring is zero.

The first preflight returned the packet before pushing: its command-scope check required a
change record for the local attributes/universe names, and it identified the unit-route
`CondensedModuleDerivedPushpull` import. The record is now included, and that import and its
DAG dependency are restored. The record's downstream check found no current Lean importers;
the unfinished DAG parent is preserved and no withdrawal is proposed.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
