## What changed

Reconciled the reviewed delivery 44af9ae85f5 with current sheaf-dag after
return C-44af9. The landing conflict was caused by the earlier packet's
change to Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative.
Current main already contains that consolidation, landed by af62f65adee.
The sandbox now takes that file verbatim; the redundant replacement and
its stale base are removed from the proposed diff.

The substantive item repair remains: replace the restored duplicate in
Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalizationChain
with a public compatibility interface to its complete adopted implementation.
Both original public Sheaf imports remain. The same fully qualified chain
map, theorem and six local instance constructions are re-exported.

The current Sheaf and adopted chain declaration blocks agree textually
modulo comments, whitespace and expansion of the existing affineTildeFunctor
abbreviation. Current main already incorporates the explicit Abelian-universe
correction. Thus the adopted proof follows the same degreewise mate
calculation, cancellation and chain-map extensionality. The DAG statement,
Lean attachment, proof plan and dependencies stay unchanged. No adopted
source file or quarantine archive is modified.

Refreshed coord/changes/J1-affine-exchange-chain-rework.md against current
source, including its verbatim Old section, current consumers and holders.
The earlier C-ad096 request to account for the homology coordinates consumer
is retained and reconciled with its current adopted compatibility interface.

## Proved and sorry left

Zero-hole repair: 0 of 0 original sorries closed, 0 added, 0 split off.
No sorry remains in the delivered item or the unchanged representative
interface. The complete adopted proof of
AlgebraicGeometry.affineTildeTensorOrdinaryExchange_preNormalization_chain
and the concrete definition AlgebraicGeometry.affineTildePushforwardComplexMap
are retained. This is a compatibility repair, not a new hole closure.

The current representative interface retains the concrete definitions
AlgebraicGeometry.affineBaseChangeTildeComplexIso and
AlgebraicGeometry.affineBaseChangeTildeRepresentativeIso and the proved
formulas affineBaseChangeTildeComplexIso_hom_f,
affineBaseChangeTildeRepresentativeIso_counit and
affineBaseChangeTildeRepresentativeIso_identity_hom.

Both retained interfaces compile on the server through lcompile.py --all
and in the final combined check (0.2 seconds each).
The combined current-source set also compiles the full legacy chain-theorem
signature and proves the original pushforward chain-map construction equal
to the re-exported construction by rfl. The category, preadditive and abelian
instance constructions are checked by rfl. A separate scratch consumer imports
both the current parent interface and the repaired chain interface successfully.

Standalone probe runs initially loaded an older published representative and
reported duplicate auxiliary declarations. Including the byte-identical current
representative and the repaired item in the same lcompile.py set resolves that
version mismatch; no dependency source is changed to accommodate it.
The final combined server check passed all five files. Every printed axiom
list, including the seven primary declarations, all six named instance
constructions, the legacy-signature theorem, the construction equality and
the current parent theorem, contains only propext, Classical.choice and
Quot.sound. The three probe files compiled in 0.2, 0.2 and 3.9 seconds.
All scratch checks are excluded from delivery by their __probe.lean suffix.

## No longer needed

No mathematical node or module is pruned. The item is retained with its
original attachment because its DAG parent still cites it; the adopted
pre-normalization proof also continues to use this chain calculation.

The item no longer needs direct private imports of
Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization,
WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction or
WeilConjectures.AlgebraicGeometry.TensorPullbackTilde. The adopted chain
implementation retains those proof dependencies. Both original public Sheaf
imports remain. No unit statement or proof step is bypassed.

The earlier packet's representative replacement is redundant with current
main and is dropped from the diff. The representative module itself remains
unchanged, with both current public imports and all five public names.

## Where the brief, the DAG or earlier work was wrong

The prior packet used the representative file from before af62f65adee,
which overlapped the E3 landing even though both packets implemented the
same consolidation. The repair preserves current main's representative
file verbatim and applies the chain repair against current source.

The earlier report's five-consumer scan and holders were stale. Current
source has zero Lean importers of the item and four downstream modules of
the representative interface. The DAG dependency and adopted parent's use
remain; neither fact is treated as permission to withdraw the item.

The original quarantine assignment has zero holes. Its substantive defect
is duplicate source/Sheaf declarations, repaired by restoring the original
import path as a compatibility interface to the existing complete proof.
The DAG's mathematical statement and proof remain accurate.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
