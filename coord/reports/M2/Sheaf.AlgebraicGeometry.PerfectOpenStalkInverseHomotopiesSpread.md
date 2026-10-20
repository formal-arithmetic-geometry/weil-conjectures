## What changed

Retire Sheaf.AlgebraicGeometry.PerfectOpenStalkInverseHomotopiesSpread as assigned
in coord/retire-items.tsv. Its node now names the already proved upstream theorem
in WeilConjectures.AlgebraicGeometry.PerfectOpenStalkInverseHomotopiesSpread.
That theorem has the same conclusion without the redundant hxU, hU and hV
hypotheses. The mathematical node, its two proof steps, proof dependency and
unit route stay intact.

Adapt its sole consumer, Sheaf.AlgebraicGeometry.PerfectStalkQuasiIsoDetection:
switch the private import to upstream, omit those three arguments, and rename
the now unused local hV to _hV. Its public signature and public imports stay
identical. No adopted-source file is edited.

Repair of returned head 550c309ef3: discard the stale sandbox version of
PerfectOpenStalkChainMapLift and use the current source verbatim. The current
file already lacks the unused StalkInternalHomFinitePresentation import that
the earlier delivery removed. Preserve M1's landed switch to the upstream
PerfectOpenStalkDegreewiseShrink API and its canonical-comparison proof.
There is consequently no chain-map module change to land in this repair.
The retained retirement, consumer adaptation and node reattachment are the
substantive changes relative to current sheaf-dag.

Server verification through lcompile.py compiled the current chain-map module
in 3.7 seconds and the adapted consumer in 6.8 seconds, without warnings or
errors. The unchanged chain-map copy was then omitted from the packet so a later
landing cannot overwrite M1's work. A fresh downstream.py --uses scan confirms
one consumer. The source-only closure scan finds no new twin pairs and no
remaining import of the retired module in the adapted consumer's closure.
The first repair dry run passed all preflight checks (8a8b6c0635a, CODEX).

Change record: coord/changes/M2-retire-perfect-open-stalk-inverse-homotopies-spread.md.

## Proved and sorry left

Actual original item hole count: zero. Holes closed: zero. Holes added: zero.
No new theorem or intermediate obligation is introduced. No sorry remains in
any submitted Lean file. This is retirement of a proved duplicate, not a new
proof claim.

The existing upstream declaration
AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_inverse_homotopies_spread
proves the old assertion by specialization. The existing consumer declaration
AlgebraicGeometry.Scheme.exists_affine_restriction_quasiIso_of_perfect_stalk_quasiIso
keeps its complete proof and exact public signature.

## No longer needed

Withdraw only Sheaf.AlgebraicGeometry.PerfectOpenStalkInverseHomotopiesSpread.
Its consumer imports the upstream twin directly. The duplicate's private
homotopy_of_natIso, restriction_comp_iso and inverse_homotopies_of_natIso
helpers disappear with it; upstream retains its complete proof and helpers.

The withdrawn module's imports of WeilConjectures.AlgebraicGeometry.PerfectComplex,
WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor and
WeilConjectures.AlgebraicGeometry.PerfectOpenStalkHomotopySpread are supplied by
upstream as appropriate. Its extra private import
Sheaf.AlgebraicGeometry.StalkInternalHomFinitePresentation and public re-export
Sheaf.Paper.DerivedHomMayerVietoris are not added to the consumer. These modules
are not declared globally unused. No mathematical proof dependency is pruned:
single-homotopy spreading remains in the retained upstream proof. No DAG node
is deleted and no unit step is bypassed.

The earlier chain-map import cleanup is already in current sheaf-dag; this
repair makes no additional import removal in PerfectOpenStalkChainMapLift.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a holed item, but the current source has zero
holes and coord/retire-items.tsv explicitly assigns retirement. The old node
attachment pointed to a duplicate despite the stronger existing source theorem.
Both full proofs and signatures, the single-homotopy dependency, consumer and
sk-prop-av-cube route were read in the original delivery. Specialization covers
all old hypotheses, including zero complexes and non-Noetherian schemes.

The original logged leanfinder search found ordinary scheme stalk lemmas;
loogle `Homotopy, "stalk"` and the logged Mathlib grep found no matches.
Local rg found the upstream theorem and sole Sheaf caller. No new mathematical
statement needs a source or node. No current rework row names the item.

The reviewer passed head 550c309ef3, but landing refused its stale chain-map
file after M1's a68ffff8db changed the shrink API and proof. This repair retains
the current source instead of restoring that older implementation. The consumer
adaptation and node reattachment remain applicable to current source.

## Forced adaptations

The sole adapted module is PerfectStalkQuasiIsoDetection. The retained original
delivery tested its original version against an empty retirement stub: original
line 109 failed with `Unknown identifier
exists_affine_perfect_open_stalk_inverse_homotopies_spread`, followed by the
rcases error at line 108. The adaptation replaces private import line 13,
removes hxU, hU and hV from the call at line 110, and renames the unused local
hV to _hV at line 85. Its public signature and visibility remain identical.

PerfectOpenStalkChainMapLift is now identical to current source. Neither it nor
its other consumers require an adaptation in this packet. The original delivery
also compiled PerfectOpenStalkDerivedHomDescent unchanged; the current repair
preserves the subsequently landed chain-map implementation.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
