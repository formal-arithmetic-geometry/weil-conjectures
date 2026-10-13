## What changed

Replaced the proof of AlgebraicGeometry.affinePullbackSections_unit_uncancelled,
with its signature and public imports unchanged. Private, proved helpers evaluate
the pinned Hom equivalence at the identity, paste the normalized right-derived
units, and transport the resulting equation from homotopy objects to complexes.
The composition-unit and exact-postcomposition calculations follow the existing
proved private helpers in AffineSectionsSquareMatePathUnit. The final proof uses
the chosen counit from exists_derivedPullbackComposition and the normalized
exists_schemeDerivedAdjunction; it does not assume either comparison invertible.

## Proved and sorry left

Closed: AlgebraicGeometry.affinePullbackSections_unit_uncancelled
(node new-affine-pullback-sections-unit-uncancelled), the module's one original hole.
Added: none. No sorry remains in the delivered module or its private helpers.
This is a proof from existing declarations, rather than a decomposition into new
holed statements. Existing dependencies can still depend on sorry.

## No longer needed

None. The sole public import supplies the comparison definitions used by the
unchanged statement. No proof-only imports were added or removed, and all three
existing proof-dependency nodes remain used. No new modules or nodes are needed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt was blocked by a missing compiled
AffinePullbackModelComparisonsIsIso dependency. The published build now provides
it and the retained original module compiles. The DAG's two-step argument applies
unchanged: pinned unit/counit factorization followed by sections naturality, hr,
exact restriction compatibility, and Q/Qh transport. The unit's route is preserved.
The proof uses no K-flatness or boundedness, including for the zero complex or zero
rings, and requires exactly the stated normalization hr for v and r.

Searches rerun through msearch.py: Loogle found
CategoryTheory.Adjunction.derivedη_fac_app; LeanFinder found the same factorization
and its reassociation; grep located its Mathlib source. The existing normalized
Hom-equivalence specification gives the required equation directly.

## Second reading by C1

1. Compared the delivered module with the repository version. The public theorem
   signature, definitions, and public import are unchanged; only the proof body and
   private proof helpers were added.
2. Compiled the module with `lcompile.py`; it succeeds with no errors. The delivered
   module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. The proof uses only existing declarations and introduces no
   split-off statements.
3. Read the target node and its proof dependencies. The theorem proves the node's
   unchanged statement, and the private helpers are strictly intermediate identities,
   not restatements of the target. The zero-complex and arbitrary-comparison cases
   remain covered because no comparison is cancelled.
4. Checked the proof route against the unit record and node proof steps. It retains
   the pinned unit/counit factorization, sections naturality, exact restriction
   compatibility, and Q/Qh transport; the route therefore preserves the unit's
   realized argument. The existing public import remains necessary.
5. Searched the repository and Mathlib-facing declarations for duplicate statements
   and checked the node metadata. No new statement or node was needed, and the
   proof dependencies remain those recorded by the node.

Changed: no mathematical or interface changes. Added this second-reading report only.
