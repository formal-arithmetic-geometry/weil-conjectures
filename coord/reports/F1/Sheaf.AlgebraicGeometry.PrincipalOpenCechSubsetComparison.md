## What changed

Replaced the unfinished parent proof with a complete Lean reduction, preserving its signature.
Added `Sheaf.AlgebraicGeometry.PrincipalOpenSectionTransport`: its section isomorphism is an
explicit composition of Mathlib's open-image equality, `restrictAppIso`, and the inverse of
`overFunctorEquiv`. Proved `AlgebraicGeometry.principalOpenSectionTransport_natural` directly
from the two coefficient naturality equations.

Added `Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetCoordinates`, containing the remaining
finite tuple/subset calculation. It gives target degree isomorphisms, consecutive differential
compatibility, and the singleton restriction equation. It does not assume a source complex K,
source coordinates sigma, or an augmentation alpha.

The parent constructs its source chain isomorphism from sigma and the proved naturality lemma.
It constructs the target chain isomorphism from the coordinate lemma, using the complex shape
to handle every differential relation. Injectivity of tau identifies alpha with the singleton
restriction function. The singleton equation then supplies the commuting square for `Arrow.isoMk'`.
The two new modules are proof-only imports of the parent (the source is transitively imported).
The parent's DAG proof now records this route. No existing signature or public import changed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.principalOpenCech_subset_comparison`.
Also proved `AlgebraicGeometry.principalOpenSectionTransport_natural`
(node `lem-sc-principal-open-cech-section-transport`).

Added one hole: `AlgebraicGeometry.principalOpenCech_subset_coordinates`
(node `lem-sc-principal-open-cech-subset-coordinates`). This is the only delivered declaration
with `sorry`. Its entire proof is `:= by sorry`; its docstring and node give the finite indexing,
section transport, differential, and singleton-column argument.

This is a decomposition: one original hole closed and one lower hole added, with no claimed
net reduction in the sorry ledger. The remaining statement is strictly part of the argument;
the parent independently constructs the source chain isomorphism and the commuting arrow square.
The source isomorphism data are explicitly constructed, never chosen from unproved existence.

## No longer needed

No original library imports, nodes, or modules are pruned. The alternating total definitions
are still needed in the statements and coordinate calculation. Discarded the earlier sandbox's
reflexive `K ≅ K`, reflexive `T ≅ T`, and `True` subclaims and their two incomplete node copies;
they were not library dependencies and supplied no part of the comparison.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox did not contain a usable reduction. Its purported source and target
subclaims proved only reflexive isomorphisms, and its parent still contained `sorry`.
The old report incorrectly described those reflexive declarations as remaining holes.
There was also an adjacent-docstring syntax error. These have all been removed.
The delivery tool's rejection was correct; this was a proof failure, not a tool failure.

No error in the original mathematical statement or its unit route was found. The new coordinate
statement includes r=0: the tuple and subset families are empty, so the target is zero and the
singleton function has no coordinates. Repeated opens retain distinct indices. Empty
intersections have zero sections by the sheaf axiom. Arbitrary unbounded coefficient complexes
are allowed because only finitely many Cech columns occur in each total degree.

LeanSearch returned an internal server error; this is recorded as unavailable, without a
mathematical verdict. LeanFinder and direct Mathlib searches were completed. Mathlib's explicit
restriction equivalences supplied the proved source transport, but no existing subset-total
coordinate theorem was found.

## New nodes

`lem-sc-principal-open-cech-section-transport` records the explicit section transport and its
proved naturality theorem in `Sheaf.AlgebraicGeometry.PrincipalOpenSectionTransport`.
It is used to construct the parent's source chain isomorphism.

`lem-sc-principal-open-cech-subset-coordinates` records the degreewise tuple/subset comparison,
its differential compatibility, and its singleton restriction equation in
`Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetCoordinates`. This is the sole new proof item.
No change record is needed: every existing signature and visibility is preserved.

## Second reading by F1

1. I compared all three delivered Lean modules with the repository versions. The existing
comparison theorem has byte-for-byte identical binders and conclusion; only its proof and
proof-only imports changed. The two added modules contain the new transport and coordinate
declarations recorded by their nodes. No target statement or definition was changed.

2. I compiled the complete sandbox import order with `lcompile.py --all`; all three modules
compiled without errors or warnings. The coordinate theorem is the only delivered declaration
left with `sorry`, and it is named in its node and has a source and proof docstring. The
transport theorem and the parent theorem are sorry-free. The source transport is an explicit
composition of `mapIso`, `restrictAppIso`, and `overFunctorEquiv`; no data is chosen from an
unproved existence theorem. The coordinate statement covers r=0, singleton and repeated opens,
and empty deleted subsets. The source and parent proof use only ordinary category and
homological-complex constructions; no prohibited declaration or axiom was added.

3. The transport naturality proof follows presheaf naturality and `overFunctorEquiv` naturality.
The parent uses its source differential hypothesis, the coordinate theorem's target differential
and augmentation equations, injectivity of tau, and `Arrow.isoMk'`. The coordinate theorem's
node is a strict lower-level reindexing statement: it omits K, sigma, alpha, and the source
chain-isomorphism argument. I searched existing Sheaf modules for subset/coordinate/Cech
reindexing results and searched Mathlib with LeanFinder and Loogle; no existing declaration
matches this finite subset-to-increasing-tuple comparison. LeanSearch was unavailable, as
recorded in the node searches. The Stacks sources checked were Tags 08C1 and 01FM.

4. I checked the edge cases explicitly in the statement and proof plan: r=0 gives empty
products and zero Cech terms; r=1 has only the singleton column; repeated principal opens
remain distinct because coordinates are indexed by Fin r; and an erased empty subset contributes
zero. The signs agree with the alternating total definition: deletion position is the number of
smaller indices and the vertical sign is (-1)^(card S-1). No K-injectivity or boundedness is
introduced. The unit route remains the principal-open comparison followed by the alternating
Cech total; the coordinate theorem realizes its reindexing step.

5. I changed only the coordinate node's prose statement to make A, X, r, f, V, D, J, J', U,
T, tau, and the transported differential self-contained, rather than referring to “the principal-
open comparison”. I also added this second-reading report. No imports or proof dependencies
were pruned beyond the proof-only imports already present; the comparison node now records both
new proof dependencies, and the coordinate node records the transport and alternating-total
nodes it uses.
