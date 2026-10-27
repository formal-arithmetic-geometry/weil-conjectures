## What changed

Repair of returned head `830d61ae2fd`: W6 took the explicitly requested rework
claim for `Sheaf.Paper.DlLocallyConstructibleAdicHeart` and preserved its complete
quarantine source. The root repairs have now restored this importer and its
prerequisites on main. This packet retains the full importer and repairs its
proof elaboration. Declaration signatures, public imports, node attachment, and
dependencies are preserved; the quarantine archive is retained. The private proof
import exposes the already proved coefficient-stage zero lemma. Small categorical
helpers handle the dependent zero-map calculation without expanding coefficient
constructions. Elaboration respects transparency and uses the default heartbeat limit.

Replaced `WeilConjectures.normalizedDVR_flat_cokernel`'s sorry by an assembly proof.
The proof constructs finite semilinear composites, transports the successor normalization
bijections through the representative isomorphisms, composes those universal arrows using
the derived comparison induced directly by its chain-level restriction comparison, and
identifies their completed restrictions with the strict tower maps. Exponent zero and
equal-index cases are proved directly. Public definitions and the theorem statement stay
unchanged. Added proof imports `Sheaf.Paper.NormalizedDVRScalarCokernelComparison` and
`Sheaf.Paper.StrictRestrictionTower`.
A generic structure stores coefficient maps, their composition equations, and the
completed restriction comparisons certified equal to the canonical ones, with the
coefficient sheaves as parameters. The DVR data stores the existing public comparison
itself, so tower-map comparisons share that term without transporting it repeatedly. The finite-composite recursion is carried out
over abstract functors and then specialized to complexes of sheaves. The derived
universality induction is also proved with abstract coefficient maps in the item file
and only then specialized to DVR coefficients. This proved
strict-tower API avoids repeated expansion of the recursive coefficient quotient maps.
The private DVR composite uses this construction. Completed objects and successor maps
are defined directly and verified by the generic API, keeping the coherence record out
of their evaluation. Public definitions retain their original bodies.
Both mathematical modules and the repaired heart importer have been checked through
`lcompile.py`; the importer compiles in about 20 seconds on the current base. Development profiling
options and diagnostic commands have been removed. `deliver3.py` performs the final
compile and packet checks. Local opacity settings keep the completed limit, coefficient
system, quotient maps, and shared comparison out of repeated elaboration.

## Proved and sorry left

Closed the original body of `WeilConjectures.normalizedDVR_flat_cokernel` (one hole).
Added zero holes. The existing theorem
`WeilConjectures.normalizedDVR_scalar_cokernel_comparison`, node
`lem-coef-normalized-dvr-scalar-cokernel-comparison`, has now been completely proved
on main by V8. This repair uses that proof unchanged and removes the stale holed
sandbox copy and node copy from the packet. The original item has zero remaining
holes, as do the strict-tower API and restored heart importer. No sorry is left in
a definition or private helper. The tower composition, normalization transport,
strict-composite identification, exponent-zero case, and equal-index case are proved.
Net holes closed in this packet: one; split off in this packet: zero.

## No longer needed

No original public import is removed. The item no longer directly uses
`lem-coef-normalized-dvr-kflat-transition` / `Sheaf.Paper.NormalizedDVRKFlatTransition`:
the represented normalization bijections compose directly, without a separate transition
lemma. The existing proved coefficient comparison uses completed-projection
divisibility, `SystemScalarModel`, K-flat computation, and exact restriction. The old
direct dependency `lem-sp-completed-integral-finite-quotient-hom-ext` /
`Sheaf.Paper.CompletedIntegralFiniteQuotientHomExt` now occurs below that comparison;
it remains needed there and is not a pruned module.
`lem-cbc-extension-tensor-comparison-independent` and `lem-cbc-cochain-derived-adjunction`
move below the existing coefficient comparison through `lem-pur-system-scalar-model`; this
is not a claim that their theory is unused. Exact restriction remains provided by the
existing normalized-tower API. No module is withdrawn, and no unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The coefficient argument only needs a right exact quotient presentation. Multiplication
by the uniformizer power on a finite quotient need not be injective, so a short exact
sequence with that multiplication as its first map would be wrong. The coefficient comparison
uses its cokernel presentation; K-flatness then supplies the derived computation. The
termwise flat hypothesis of the original theorem is retained verbatim, though this route
uses K-flatness instead. The coefficient statement was checked at equal indices, zero complexes,
and the empty scheme.

## New nodes

The scalar comparison node is already present and proved on main. This packet adds
neither its source nor its node and preserves its proof and private constructions.
The restoration change record is
`coord/changes/W6-dl-adic-heart-quarantine-restoration.md`.

`lem-coef-strict-restriction-tower-composites` records the completely proved generic
coefficient-data structure, finite-composite construction, and identification with the
actual strict sequence maps. It adds no holes.

## Forced adaptations

The returned `DlLocallyConstructibleAdicHeart` failure was the `whnf` timeout at
line 163, followed by the missing theorem at line 221. The earlier heartbeat-only
repair was insufficient on the current base (the importer reached the compile-time
limit). This repair instead respects transparency, makes the category-law rewrites
explicit, reuses the proved stage-zero lemma, and performs zero-map transport over
abstract categories. It changes theorem proofs and adds proved private helpers and
a private proof import; all public signatures and definition bodies are preserved.
The adapted lines are the private import (line 13), elaboration options (lines 28–33),
the multiplicativity proof (lines 146–154), and the zero-compatibility section
(lines 168–251). These changes avoid unfolding the dependent coefficient models
while proving exactly the existing zero-compatibility statement.
This module was claimed for rework by W6 while quarantined and has now returned on main;
the change record is
`coord/changes/W6-dl-adic-heart-quarantine-restoration.md`.

The current library has independently repaired `ScalarSixDerivedPullbackNormalization`
by removing the now-redundant mate tactic. The old packet's `all_goals` wrapper now
produces unused-tactic warnings, so its sandbox copy is removed from this packet.
The current library version is retained without modification.

The item's two original completed-restriction local instances (zero preservation and
additivity) retain their original signatures and bodies. The preflight's textual
instance-user advisories therefore require no consumer changes.

The returned `IsomorphismComparisonScalarExtension` error is independent of this item:
that module does not import any of the three changed modules (directly or transitively
through the repository's source import graph), and this packet leaves it unchanged.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
