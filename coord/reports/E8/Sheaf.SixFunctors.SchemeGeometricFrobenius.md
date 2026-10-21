## What changed

Proved `WeilConjectures.PurityFiniteSetting.schemeGeometricFrobenius_naturality`
for the existing, specified comparison and square isomorphisms. The complete
original theorem header is identical. The factorization and square statements
retain their signatures and meanings.

The proof uses the ordinary composition family and Frobenius trivializations
selected jointly by `absoluteFrobenius_proEtale_trivialization_pullback`. The new
proved theorem `AlgebraicGeometry.Scheme.proEtaleNormalizedDerivedComp_coherence`
establishes associativity for exactly such a section-normalized family: site
pullback associativity gives direct-image associativity; adjunction mates give
ordinary pullback associativity; exact descent gives derived associativity.
This does not substitute another chosen composition family.

The item transports coherence across the named equal composite scheme maps and
applies it to `(f,F_Y,g_Y)`, `(F_X,f,g_Y)`, and `(F_X,g_X,f)`. The arbitrary-pullback
identity for tau, its naturality, and cancellation of invertible comparisons
finish the equality. Private generic component interfaces expose composite
functors with the literal nested object type. Generic extensionality and
component equations perform the unitor and square normalizations before the
actual derived functors are specialized. This avoids unfolding their chosen site
pullbacks and localization data in the kernel. All these interfaces are ordinary
constructed definitions or proved theorems, with no diagnostic metaprogramming.

The five public selected-data/finite-ring helpers simply name the data and proof
already used by the definitions. A public fibre-characteristic lemma supplies
one proof to the absolute map and selected trivialization. Unfolding the helpers
and proof irrelevance recover the original formulas. Four scheme-map/fibre
abbreviations become definitions with verbatim types and bodies; four existing
factorization rewrites use `erw` to see through these definitions.

The final packet retains the original global abbreviation
`proEtaleConstantRingDerivedPullback`. Its expansion ends at
`Functor.mapDerivedCategory`, which is kept irreducible locally in the item.
The redundant attempt to mark the abbreviation itself irreducible has been
removed. Consequently no operations interface or consumer adaptation is needed;
the six external edits from the returned packet are omitted from this packet.
No existing library module is withdrawn, and no source-library file is changed.

The final two-module packet compiles together without warnings against the
published library and a clean sandbox artifact directory: normalized coherence
30.4 seconds, item 21.6 seconds. The global operations abbreviation and every
external consumer are the current published originals. A fresh downstream query
finds zero external Lean users of the item or its changed definitions. Both
retained Lean files have zero holes and satisfy the 100-character line limit.
No profiling, heartbeat or file-time-limit changes are retained.
The item has zero current Lean importers; its DAG parents and unit route remain.

## Proved and sorry left

Closed the single original hole:
`WeilConjectures.PurityFiniteSetting.schemeGeometricFrobenius_naturality`
(node `def-pur-scheme-geometric-frobenius`).

Added zero holes. No `sorry` remains in any delivered module. The new coherence
result, generic interfaces, selection bridges and pasting calculation are fully
proved or explicitly constructed. No unfinished statement is
split off; this is a proof, not a decomposition into new holes.

## No longer needed

Removed the item's private imports
`Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition`,
`Sheaf.Paper.IntegralFinitePullbackComposition`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
`WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`, and
`WeilConjectures.AlgebraicGeometry.BaseChangeConventions`.
The operations, Frobenius and base-change declarations actually used remain
public dependencies of the retained imports. The scheme-pullback import remains
to supply the site pullback instances. The finite-coefficient import is private
because it is now needed only by the finite-ring theorem's proof. The new
coherence module does not import the unused
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`.

The naturality proof does not use
`lem-weil-pbc-proetale-derived-pullback-composition` or its general K-flat
composition construction: it descends the ordinary family selected by
`lem-pur-frobenius-trivialization-pullback`. The obsolete proof dependency and
its top-level tool-use entry are removed. Existing statement dependencies and
unit steps are preserved. No module or source-library declaration is withdrawn;
no global module pruning is claimed.

The two statement-only nodes of the 2026-10-21 stage-1 re-split are not used by
the Lean proof: `lem-pur-unrestricted-frobenius-factorization`
(`Sheaf.AlgebraicGeometry.UnrestrictedFrobeniusFactorization`) is bypassed because
the item module already proves `schemeGeometricFrobenius_factorization` itself, and
`lem-pur-factorized-pullback-square-pasting`
(`Sheaf.AlgebraicGeometry.FactorizedProEtalePullbackPasting`) is replaced by
`lem-pur-normalized-derived-pullback-coherence`, since the item's comparisons are
exact descents of the selected ordinary family, not the K-flat-normalized family.
Neither node is in the unit's `realized` list; both modules have no importers and
are candidates for pruning. (Added by the reviewer.)

## Where the brief, the DAG or earlier work was wrong

The return at `23dd5937b` reported a passed review followed by a landing failure
for `E8-scheme-geometric-frobenius-proof-scopes.md`. The record exists in the
sandbox at its full `coord/changes/` path and is included directly in this
delivery. Inspection of `tools/batch_land.py` shows that reviewer fix overlays
name change records with the alias `<stem>.change.md`; the failed landing used
`<stem>.md`. The record now documents its exact path and accepted fix alias, so
the resubmitted packet does not depend on that rejected overlay. The delivery
tool rebases the retained Lean and DAG changes onto the freshly fetched
`sheaf-dag` state before preflight and push.
On this repair retry, `lcompile.py --all` compiled both delivered modules
successfully on the server with no diagnostics. The first request returned no
answer from the busy server; the required retry succeeded. The item node was
also reconciled with current review metadata, preserving this packet's proof,
proof dependencies, Lean attachments and tool-use pruning. A fresh downstream
query again found zero external Lean importers or textual users requiring edits.

The returned packet changed the global derived-pullback abbreviation to a
definition. Its user table omitted the six textual users named by the landing
gate. We first repaired the table using the current downstream inventory and a
whole-library textual search, which found all six. Further compilation showed
that the global change was unnecessary: local irreducibility of
`Functor.mapDerivedCategory` suffices. The final packet therefore preserves the
global abbreviation and all its consumers. Each of the six named users keeps
exactly its existing definitions, statements, imports and proofs; they are also
listed in the item proof-scope change record for an explicit return audit.

The old plan invoked coherence of a general derived composition comparison,
whereas the definitions use exact descent of the ordinary family selected by
the Frobenius trivialization theorem. The new proof proves coherence of that
precise family from its existing section normalization.

Applying the categorical calculation directly to derived objects repeatedly
forced conversion between a composite functor's object and nested pullback
objects. The generic component/extensionality interfaces retain their exact
nested types and let the kernel check the generic conversions before
specialization. This changes no mathematical definition or assumption.

Empty and nonreduced schemes, identity morphisms and exponent zero require no
exceptions: the arbitrary-pullback theorem and site associativity apply directly.
No Cartesian hypothesis is added for the scheme-Frobenius square. The existing
finite-type, quasi-compactness, separatedness and smoothness binders stay verbatim.

## New nodes

`lem-pur-normalized-derived-pullback-coherence`, implemented and proved in
`lean/Sheaf/AlgebraicGeometry/NormalizedProEtalePullbackCoherence.lean`, is strictly
the composition-coherence step. It involves no Frobenius map, selected tau,
Galois square, or target naturality equation and contains no unfinished proof.
Its node records the sectionwise, mate and descent argument, the literal theorem
signature and the Mathlib searches. Its second public declaration names the existing
standard category instance, which the item's public definitions use.

Change records:
`coord/changes/E8-frobenius-fiber-transparency.md`,
`coord/changes/E8-frobenius-characteristic-api.md`,
`coord/changes/E8-frobenius-selected-comparison-api.md`, and
`coord/changes/E8-scheme-geometric-frobenius-proof-scopes.md`.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
