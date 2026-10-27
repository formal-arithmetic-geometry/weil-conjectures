## What changed

Replaced the hole in `AlgebraicGeometry.WeilSheaf.exists_geometric_power_orbit`
by a proof from geometric multiplicity one. The original theorem signature,
including the embedded original-return equation, is unchanged.

Three proved private helpers carry the rest of the argument. `monomial_return`
finds a nonzero matrix component of each Frobenius-translated simple summand,
uses Schur for local systems, kills all other components using multiplicity one,
and constructs the finite permutation. `transitive_return` constructs an orbit
projector, proves that it commutes with Frobenius, and uses the lisse image and
arithmetic simplicity to prove that this idempotent is the identity.
`iterated_return` follows the actual geometric pushforward coherence maps in
`frobeniusPowIso`, proving the required embedding equation by induction.

The final proof takes the order of the permutation, equips each original
geometric factor with the restricted power return, and lifts its inclusion to
an algebra morphism. Their biproduct desc is an isomorphism because its
forgetful image, composed with the biproduct comparison, is exactly the supplied
geometric decomposition inverse. Transitivity and the iterated embedding
formula give the final pairwise transport.

Added `Sheaf.DeligneLaumon.GeometricMultiplicityOne` for the remaining
multiplicity-eigenline step and updated both DAG proof records. All source-library
files and public interfaces are preserved. The private proof imports use
`GeometricConstituent` for Frobenius preservation and Schur for local systems,
`LisseFiltration` for the exact `carrierFunctor`, the generic image-preservation
isomorphism, and the finite-permutation cycle API.

## Proved and sorry left

Closed the original syntactic hole:
`AlgebraicGeometry.WeilSheaf.exists_geometric_power_orbit`
(`lem-zl-geometric-power-orbit`). The item module has zero remaining holes.

Added one hole:
`AlgebraicGeometry.WeilSheaf.geometric_factors_pairwise_nonisomorphic`
(`lem-zl-geometric-multiplicity-one`). This states only that distinct factors
in the supplied finite geometric decomposition cannot be isomorphic. It asserts
no orbit, no power structure, and no equivariant biproduct isomorphism.

This is a reduction with one hole closed and one hole added, not a net reduction
in the hole count. The permutation, transitivity, geometric power coherence and
algebra-lifting proofs are complete Lean proofs.

Edge cases checked: an empty decomposition requires no inhabited index set and
the empty permutation has positive order; the one-factor case permits a fixed
point; the new multiplicity-one statement is vacuous for zero factors and
reflexive for one factor. The algebraically closed coefficient field is
essential to its eigenline argument.

Validation: the new statement module compiled cleanly in 4.4 seconds. The final
item module compiled cleanly through `lcompile.py` in 44.1 seconds, with no
errors or warnings. The original theorem signature was compared verbatim with
the shared source and is unchanged; every Lean line is at most 100 characters.
The added source import passes `import_direction.py may`.

## No longer needed

No existing import, node, or module is withdrawn. The original public transport
import is needed by the unchanged signature. Schur's scalar lemma is no longer
a direct proof dependency of the item: its use is confined to the strictly
smaller multiplicity-one node. It remains needed there, so it is not globally
pruned. No constant-field model, local stalk comparison, curve theorem, or
parent module is imported into this proof.

## Where the brief, the DAG or earlier work was wrong

The listed Schur dependency is a scalar-endomorphism theorem for group
representations. It does not itself construct the geometric isotypic blocks or
the multiplicity eigenline in the source sheaf category. Existing source
geometric-constituent proofs supply Frobenius preservation of irreducible local
systems and Schur for their nonzero morphisms; neither states multiplicity one.
The new node isolates just that missing assertion instead of restating the
assigned power-orbit theorem. The original unit route is retained. The new node inherits the original
node's explicitly recorded blueprint ancestor; the ancestor query cannot
resolve the module-valued `created.item` chain.

## New nodes

`lem-zl-geometric-multiplicity-one`, in
`dag/nodes/sec-deligne-laumon-general/lem-zl-geometric-multiplicity-one.json`,
records the pairwise nonisomorphism of the given simple geometric factors.
Its module is `Sheaf.DeligneLaumon.GeometricMultiplicityOne`. Its source is the
first two proof paragraphs of the current blueprint's geometric-constituents
lemma, with the isotypic-block and eigenline argument written in full in the
docstring. LeanSearch, LeanFinder, Loogle, Mathlib grep, source-library searches,
and whole-blueprint searches found no matching sheaf statement. No change
record is required because no existing statement or definition changes.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
