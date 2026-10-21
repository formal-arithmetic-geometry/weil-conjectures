## What changed

Proved `WeilConjectures.realization_completed_pull` from the ordinary normalized pullback
system and explicit categorical constructions. The theorem's signature is unchanged.
`RealizationCompletedPullData.lean` holds the 32 original data declarations verbatim;
the original module publicly forwards them, preserving its existing interface.

In the item module, the completed compositor is constructed by conjugating ordinary
composition with the two specified completion units. Cancellation proves its normalization
and uniqueness. Naturality of ordinary comparison and cancellation of the completion units
prove alpha composition and identity.

`RealizationPullRationalDescent.lean` proves raw rational descent: tensor extension,
unchanged denominators, natural unit/composition/identity isomorphisms, and normalized
rational alpha. The comparison with triangulated rationalization makes restriction along
Q fully faithful; alpha is lifted through that restriction. Conjugation and naturality
prove both raw coherence equations on the unchanged integral objects.

`RealizationPullOrdinarySystem.lean` isolates the remaining ordinary coefficient,
constructibility, scalar comparison and ordinary coherence argument (original steps 1–5
and the ordinary equation used in step 7). Its source and complete proof in words are in
the theorem docstring and new node. The completed compositor, its uniqueness, raw
localization and raw coherence are all excluded from this residual statement.

Validation: all four delivered modules compile cleanly together. The unchanged existing
consumer `Sheaf.Paper.RealizationAdjointComparisons` also compiles against this set.
The original theorem signature and the entire original data-declaration section were
compared verbatim with the shared source and agree.

Change record: `coord/changes/P6-realization-pull-signature-module.md`.
The existing consumer `Sheaf.Paper.RealizationAdjointComparisons` keeps its unchanged
public import; forwarding preserves all its declaration names and types.

## Proved and sorry left

Original holes: 1, in `WeilConjectures.realization_completed_pull`.
Closed that syntactic hole with a complete Lean construction. Added 1 hole:
`WeilConjectures.realizationPullOrdinarySystem`, node
`lem-weil-pbc-realization-pull-ordinary-system`.
This is a decomposition with net zero holes closed, not a fully discharged mathematical
proof. The original module has zero holes. The data and rational descent modules have
zero holes; every private helper is proved. No definition contains a hole.

Proved `WeilConjectures.realizationPullRationalDescent`, including fraction preservation,
raw alpha normalization, and raw alpha composition/identity, together with the private
completion compositor normalization, uniqueness, alpha composition and identity helpers
in the original module. No other statement is left with `sorry` in this packet.

## No longer needed

The original proof-only imports of `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`,
`Sheaf.Paper.ReductionPullbackDerivedTower`, `Sheaf.Paper.PbcIntrinsicTowerComplete`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Mathlib.AlgebraicGeometry.Sites.Fpqc`, `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`,
and `Mathlib.Topology.Algebra.Valued.LocallyCompact` are removed from the top module.
Their mathematical roles remain in the residual ordinary-system node's proof plan;
none of those geometric nodes is claimed globally pruned.
`Sheaf.Paper.PbcRationalTransport` is used in the proved rational descent module.
All original public imports remain available through the shared data module.
The unused proof import `Sheaf.Paper.CompletedOpenExchangeTransport` explored for the
ordinary coefficient isomorphism is also absent from the final packet.
No existing node or module is withdrawn. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The categorical completion and localization parts can be proved independently of the
geometric ordinary comparison. The original single existence statement bundled these
parts together; sharing its unchanged signatures avoids an import cycle when making
that separation. The actual strict completion unit is retained in every normalization.
No statement is disputed or weakened. No adopted source-library declaration is changed.

## New nodes

`def-weil-pbc-realization-pull-data`: attaches the 32 unchanged data declarations to their
shared module, with the same scalar coefficient conventions and actual pullback functors.

`lem-weil-pbc-realization-pull-ordinary-system`: ordinary coefficient and scalar comparison
system, integral preservation and ordinary identity/composition equations; the sole
remaining hole. This is a strict part of the original argument, rather than its conclusion
under another name. Empty schemes, identities, zero and uniformizer-torsion objects need
no exceptions: ordinary pullback and localization preserve the specified units in all
these cases. Arbitrary morphisms are allowed, as in BS Remark 6.8.15.

`lem-weil-pbc-realization-pull-rational-descent`: proved descent of the integral system and
its equations to raw scalar localization. Objects are unchanged and no Karoubi envelope
or arbitrary lattice choices are introduced.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
