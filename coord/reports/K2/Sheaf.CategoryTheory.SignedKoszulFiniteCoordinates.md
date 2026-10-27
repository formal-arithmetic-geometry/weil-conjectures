## What changed

Replaced the proof of `CategoryTheory.exists_ringedSignedKoszulFiniteCoordinates`
without changing its statement or public imports. The proof imports the new
`Sheaf.CategoryTheory.SignedKoszulTensorCoordinates` privately, together with the
proved source K-flat and flatness APIs. All additional helpers in the item are
private and proved.

From the normalized subset coordinates and differential matrix, construct the
transition by conjugating the diagonal whose I-entry is multiplication by the
product of the a_i for i in I. Prove its chain equation using the finite-product
identity and commutativity, then prove naturality and its matrix formula.
Construct the inclusion from the empty subset and prove its chain equation,
naturality, matrix formula and compatibility with transitions. Derive the
coefficient-map matrix from naturality of the actual tensor summands rather than
including it in the remaining obligation.

Prove quasi-isomorphism preservation independently: each two-term negative factor
is bounded and termwise flat, hence K-flat by the existing proved source theorem
`CochainComplex.kFlat_of_bounded_of_flat`. Tensor closure gives K-flatness of the
ordered tensor, including the empty tensor; its right-whiskering property applies
to arbitrary unbounded coefficient complexes.

The remaining finite tensor decomposition is stated in its own module with its
source, full proof in words, edge cases and DAG node. Its normalization fixes every
inverse coordinate injection, so the witness is determined, rather than an
arbitrary object chosen from an existence statement. No definition is added or
changed. The unit route is preserved.

## Proved and sorry left

Closed the original proof hole in
`CategoryTheory.exists_ringedSignedKoszulFiniteCoordinates`
(node `lem-cbc-signed-koszul-finite-coordinates`) by a complete proof from the
strictly smaller tensor-coordinate statement. The item has zero remaining holes.

Added one named hole:
`CategoryTheory.exists_ringedSignedKoszulTensorCoordinates`, in
`Sheaf.CategoryTheory.SignedKoszulTensorCoordinates`, node
`lem-cbc-signed-koszul-tensor-coordinates`. It asserts only the normalized subset
coordinate isomorphisms and their differential matrix. It does not assert the
coefficient-map matrix, transitions, inclusions, compatibility or
quasi-isomorphism preservation; those parts are proved in the item.

Counts: one original hole closed, one new hole added, net zero. This is a
decomposition, not a complete proof of the tensor-coordinate calculation.
The scalar identity, tensor-summand naturality, and K-flatness argument have no
new holes. There are no other sorries in this delivery.

## No longer needed

No existing import, node or module is removed. The old plan's finite filtration,
shift sign twists and long exact homology induction are unnecessary for the
quasi-isomorphism clause: the existing bounded-flat K-flat theorem proves it
directly. There was no separate declared filtration dependency to withdraw.
All original statement dependencies remain needed by the coordinate calculation.
No source-library declaration is changed or withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or incorrect target was found. The old filtration argument is
valid but longer than using the already proved source K-flat criterion. The
remaining coordinate theorem is strictly smaller than this assigned theorem;
the construction and verification of both natural transformations and the
quasi-isomorphism argument are actual Lean proofs, rather than renamed holes.

## New nodes

`lem-cbc-signed-koszul-tensor-coordinates` records the normalized subset expansion
of the actual ordered tensor and its signed differential. Its proof is induction
on the number of factors, splitting subsets by the first index and distributing
tensor over the two supported degrees and the finite biproduct. Normalization
identifies the inverse injections with the existing pure-tensor summands. The
statement is tested in words at zero and one factors and allows zero scalars and
zero rings. Its source is the finite negative Koszul calculation in Stacks
Tag 0A0E and step 1 of the assigned node. The assigned node's proof, proof_deps and
proof_origin now describe the implemented route. No change records are needed:
no existing statement, definition or public interface changes.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
