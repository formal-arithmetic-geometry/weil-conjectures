## What changed

Retired Sheaf.AlgebraicGeometry.PerfectOpenStalkDerivedHomDescent, the zero-hole
DIFFERENT item explicitly listed in coord/retire-items.tsv, in favor of the existing
proved WeilConjectures.AlgebraicGeometry.PerfectOpenStalkDerivedHomDescent.
The source theorem supplies the canonical restriction comparisons and needs neither
hU nor hQ. Choosing its comparisons proves the unchanged mathematical node assertion.

Adapted its sole consumer, Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift
(unclaimed), preserving its entire public statement. The private import now names
the source module; the call omits hU and hQ and unpacks g and hg. The consumer
constructs c, cP and cQ explicitly and closes the final equality by unfolding those
lets after the existing associativity simplification. The original hU binder stays;
a theorem-local unused-variable linter setting handles its now-unused name.

Reattached lem-sc-perfect-open-stalk-derived-hom-descent to the exact existing source
signature. Its proof description records that the canonical comparisons witness the
existentials, and its parent's proof records their explicit construction. All node
statements, dependencies and unit realization records remain intact. No source file
is changed. Change record:
coord/changes/B5-retire-perfect-open-stalk-derived-hom-descent.md.

## Proved and sorry left

Holes closed: 0 of 0. Holes added: 0. Split off: 0. Sorries left: none in the
withdrawn module or adapted consumer. This is a completed retirement repair, not a
new hole-closing proof. The source declaration
AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_derived_hom_descent
already has a complete proof. The adapted
AlgebraicGeometry.Scheme.exists_affine_perfect_stalk_hom_lift remains completely proved.

Validation: the adapted consumer compiles through lcompile.py. Explicit #print axioms
probes show only propext, Classical.choice and Quot.sound for both declarations.
The probes were removed from the delivered file; delivery preflight checks the final packet.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.PerfectOpenStalkDerivedHomDescent, listed
in deleted.txt. Its duplicate private perfect_stalk_isKProjective proof is removed
with it; the source proof has its own complete helper. Removed its private import
from Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift and replaced it with the
proved source import. No remaining live or quarantined module imports the withdrawn
module after this adaptation.

The duplicate's imports disappear with it:
WeilConjectures.AlgebraicGeometry.PerfectComplex,
WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor,
WeilConjectures.AlgebraicGeometry.PerfectOpenStalkChainMapLift,
WeilConjectures.AlgebraicGeometry.OpenModuleStalkFreeProjective,
WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective,
and Sheaf.Paper.DerivedHomMayerVietoris. The source implementation still needs the
first five; no global pruning of those modules or their nodes is claimed.
The consumer no longer imports DerivedHomMayerVietoris indirectly through the
duplicate descent module. The DAG dependencies for the bounded-projective and
chain-map-lift argument remain needed and unchanged. No node is deleted or pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed item, but this item has zero holes and
is queued as a retirement. The DIFFERENT source signature is genuinely stronger:
it fixes cP and cQ to canonical comparisons rather than existentially choosing them,
and omits hU and hQ. Therefore merely replacing the import would fail. The packet
adapts the sole actual consumer and retains the node with a source attachment,
rather than treating zero importers as permission to discard the mathematics.

The sole DAG parent still cites this node. No quarantined parent imports its Sheaf
module. The unit sk-prop-av-cube and its route are unchanged. Edge cases remain
covered: zero complexes and zero ranks are allowed; x in U excludes an empty U.
The existing source proof uses the same K-projective chain-representative and local
chain-map descent argument described by the node, so there is no unit bypass.

Searches actually run with msearch.py: leanfinder on derived stalk morphism descent
(eight ordinary stalk/spreading-out hits, no exact match), loogle on "stalk"
(twelve ring-homomorphism surjectivity hits, no exact derived descent match), and
grep on perfect/stalk/derived combinations (one unrelated smoothness hit).
Local rg immediately found the exact stronger source theorem, which is used.
Read the local Stacks 09RE affine proof in perfect.tex and 0BC7(2) in more-algebra.tex:
bounded finite-projective sources give chain representatives, with finitely many
components descending to a stage. No new theorem or unsupported split is added.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
