## What changed

Proved `AlgebraicGeometry.exists_etale_finite_unramified_neighbourhoods` without changing
its signature. Added three proved private helpers in its module: source-locality for a
union of unramified opens, transport of a finite marked open along an open immersion,
and reindexing a finite family into a sigma family over a nonempty `Fin`.
Added the private proof import `Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`.
Updated the existing node's proof, proof dependencies and proof origin to match the Lean.

The proof uses the existing finite-multiple-points theorem on the distinct finite range
of the original list in the source open. It proves open-image transport, residue-field
compatibility, injectivity and exhaustion explicitly. No new public theorem or module
is added. The source construction is Stacks 04HH, first finite-neighbourhood step via
02LM; open-image transport uses 01HH and source restriction uses 02G6.

## Proved and sorry left

Proved `AlgebraicGeometry.exists_etale_finite_unramified_neighbourhoods`
(node `lem-weil-pbc-unramified-etale-finite-neighbourhoods`). All three private helpers
are proved. No `sorry` remains in the delivered module and none is added elsewhere.
The existing dependency `exists_etale_local_finite_multiple_points` continues to depend
on its existing lower proof obligations; this delivery does not claim to close them.
The module compiles cleanly with the prescribed local compiler.

## No longer needed

No existing import, node or module is pruned. All three original proof imports are used.
Representative-index bookkeeping is unnecessary: the target imposes no equation
connecting a piece's first index to its image under the first pullback projection.
The proof therefore packs all pieces into the first row for a nonempty input list,
using an explicit finite equivalence. Repeated input entries are covered by the same
finite-range representative. The empty-list branch has an empty sigma family.
No separate residue-field-isomorphism transport obligation or new node is needed:
`Scheme.residueFieldMap_comp` and `IsPurelyInseparable.tower_bot` close it directly.

## Where the brief, the DAG or earlier work was wrong

No false statement or tool failure was found. The earlier natural-language proof asks
for retaining original representative indices, which is stronger bookkeeping than the
Lean conclusion needs. The revised node records the simpler indexing actually proved.
Unlike the original docstring's suggested identity neighbourhood in the empty case,
the implementation uses the neighbourhood returned by the existing theorem and an
empty family; this satisfies precisely the unchanged statement. The unit's realized
steps are not bypassed: this node is a lower geometric input and still uses 02LM and
the original isolation and base-change dependencies.

## Second reading by P2

1. PASS: compared the delivered module against the repository with `diff` and compared
   the existing theorem signature byte for byte. Its signature and all public imports
   are unchanged. No definition, target statement, or additional module changes. The
   existing node changes only `proof`, `proof_deps`, and `proof_origin`.
2. PASS: the prescribed local compiler accepts the file. There is no `sorry` or
   forbidden declaration in it. A scratch-copy `#print axioms` probe of all four
   declarations shows only `propext`, `Classical.choice`, and `Quot.sound` for the
   private helpers. The main theorem additionally shows `sorryAx` from its existing
   imported obligations; no new hole is introduced. Closed one original hole:
   `AlgebraicGeometry.exists_etale_finite_unramified_neighbourhoods`; added zero.
3. PASS: no statement is split off, and no new node is added. Read the three private
   helper proofs: the union cover remains valid for an empty index type, transport
   uses an actual open-image isomorphism, and the residue field algebra maps form
   the required scalar tower. Reindexing permits zero pieces and packs an arbitrary
   finite family into row zero only when the original list is nonempty. Repeated
   original points are handled by the finite range and exhaustion.
4. PASS: read all three Sheaf proof dependencies and searched the library with
   alternative finite/isolated/unramified keywords, plus the prescribed Mathlib grep
   search for finite isolated neighbourhoods, open-image isomorphisms and tower
   descent. No shorter exact theorem was found. The proof uses the existing
   simultaneous-neighbourhood result and Mathlib for transport. All original
   `proof_deps` are used; no import, node or module is pruned. The three Sheaf
   imports and the added formally-unramified import are proof-only. The unit
   `sk-thm-p1` realized route is unchanged and this lower input bypasses no step.
5. PASS: the node's steps follow the Lean construction, with `proof_deps` equal to
   their uses and the added transport dependencies matched to Mathlib. Its statement
   and Lean record are unchanged; there are no new-node fields to validate.

Second reading changed the theorem's proof docstring to describe the actual arbitrary
finite reindexing and retained neighbourhood in the empty case, and wrapped the
transport application and projection-identity proof for readability. The mathematical
proof was retained.
