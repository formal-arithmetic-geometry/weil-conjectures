## What changed

Proved `Algebra.differentials_injective_of_h1Cotangent_injective_charP` in
`Sheaf.RingTheory.DifferentialsInjectiveOfH1CotangentInjectiveCharP`, preserving its original
signature verbatim, including its `letI` binders, universes, and visibility.

The proof first cancels the conormal equivalence from the injectivity hypothesis. Vanishing
of prime-field H1 and Mathlib's middle exactness make the upper connecting map injective.
The existing connecting-map naturality theorem gives the left square after identifying its
comparison map with the target's precise tensor lift. The universal derivation and tensor
extensionality prove the right square. A complete kernel chase proves injectivity.

Removed the proof-only import `Sheaf.RingTheory.JacobiZariskiHomologySequence`; added the
proof-only import `Mathlib.Algebra.CharP.Algebra` for characteristic transfer to the residue
field. All public imports remain unchanged. Updated the item's proof, proof dependencies,
and proof origin to match the Lean argument. Added a Mathlib leaf for the two middle
exactness statements, using the existing Mathlib declarations without duplicating them in
Lean. No definition or other module was changed.

Validation: the module compiles locally with no errors or warnings through `lcompile.py`.
Both retained Sheaf proof imports pass `import_direction.py may`. No lines exceed 100
characters. The dry-run delivery check includes the axiom probe.

## Proved and sorry left

Closed the single original hole:
`Algebra.differentials_injective_of_h1Cotangent_injective_charP`
(node `lem-weil-pbc-h1-injective-differentials-injective-char-p`).

There are no remaining `sorry`s in the item's module and no added holes or split-off
statements. This is a proof, not a decomposition. The proof uses the existing named
vanishing and naturality theorems and the already-proved Mathlib exactness theorems.

## No longer needed

Removed import and direct proof dependency:

- `Sheaf.RingTheory.JacobiZariskiHomologySequence`, node
  `lem-weil-pbc-jacobi-zariski-homology-sequence`.

The proof needs only its two middle exactness assertions, which Mathlib already proves;
it does not use the left term, Tor criterion, polynomial comparison, or coefficient formula
from that large theorem. These parts and that module's proof dependencies are unnecessary
on this item's route. This does not claim that other users of the module are pruned.

Also removed the item's direct proof dependency
`lem-weil-pbc-nl-presentation-h1-functoriality`: the existing naturality theorem already
supplies the needed identity, so there is no separate functoriality argument in this proof.
The node remains a statement dependency and is used by the middle-exactness leaf to specify
the coefficient-change map; it is not globally discarded.

The characteristic, prime-field vanishing, conormal equivalence, naturality, and universal
differential nodes remain needed. No other import was removed. The unit's realized
statement and steps are untouched, and no realizing module is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false or unusable statement was found. The planned diagram chase is valid. Its full
homology-sequence dependency is larger than necessary: Mathlib
`Algebra.H1Cotangent.exact_map_δ` and
`Algebra.H1Cotangent.exact_δ_mapBaseChange` provide exactly what this argument uses.
The proof cancels the conormal equivalence immediately and works with H1 connecting maps,
which also avoids comparing conormal equivalences constructed over different base rings.

The residue field has both inherited and field-derived ring/algebra instances. The proof
explicitly converts the prime-characteristic vanishing theorem to the inherited algebra
using uniqueness of `Algebra (ZMod p) K`; this is an instance identification, not a statement
change.

The local checkout lacks the source `.tex` files. The cited source was checked directly at
[Stacks 00S2](https://stacks.math.columbia.edu/tag/00S2) and
[Stacks 07E5](https://stacks.math.columbia.edu/tag/07E5). LeanSearch was attempted through
`msearch.py` and returned an unavailable-service error. LeanFinder, Loogle, source grep,
and direct signature inspection supplied the successful searches; no LeanSearch result
is invented.

## New nodes

`lem-weil-pbc-jacobi-zariski-middle-exactness` records the two adjacent middle exactness
assertions for an arbitrary compatible commutative-ring tower. It is a Mathlib leaf:
`Algebra.H1Cotangent.exact_map_δ` and
`Algebra.H1Cotangent.exact_δ_mapBaseChange` in
`Mathlib.RingTheory.Kaehler.JacobiZariski`, lines 548 and 556. It introduces no Lean module
and no hole. The node was checked against the general tower signatures, including zero
rings and identity maps; there are no field, finiteness, smoothness, flatness, or Tor
hypotheses. Searches of the DAG and imported blueprint found no node with exactly this
smaller statement. The existing full homology-sequence node has additional left-term and
Tor conclusions, and the quotient-smooth and field-tower nodes have extra hypotheses.
There are no change records because no existing interface changed.

## Second reading by G1

1. **Interfaces: PASS.** Read the module and diffed it against the repository.
   The sole existing theorem signature is byte-for-byte identical, including the
   instance binders, universes, local lets, conclusion and visibility. Public imports
   are unchanged. There are no new declarations, definitions or change records.
2. **Proof and axioms: PASS.** Independently compiled the delivered module through
   `lcompile.py`, cleanly in 9.0 seconds. A scratch copy with `#print axioms` for
   `Algebra.differentials_injective_of_h1Cotangent_injective_charP` and both Mathlib
   exactness lemmas compiled cleanly; all three list exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Read the conormal
   cancellation, characteristic transfer, algebra-instance identification, two
   commuting squares, and final kernel chase. No sorry, forbidden declaration,
   hollow definition, or arbitrary data choice is introduced. The existential
   comparison map from naturality is uniquely determined by its generator formula;
   it is used only inside the proof and identified with the explicitly constructed
   tensor lift. The original hole is closed and zero holes are added.
3. **Split statements and Mathlib leaf: PASS.** No statement is split off. Read
   Mathlib's general ring-tower signatures and coefficient-derivative formula for
   the new middle-exactness node. Identity towers and zero-ring towers satisfy
   those signatures; there is no hidden flatness or Tor assumption at these middle
   terms. For the item, the case `A = k` gives the identity tensor map, and a prime
   base field gives zero source differentials, consistent with the claim. The leaf
   cites the existing Mathlib declarations rather than introducing duplicate Lean
   statements. Rechecked its source at [Stacks 00S2](https://stacks.math.columbia.edu/tag/00S2)
   and the diagram argument at [Stacks 07E5](https://stacks.math.columbia.edu/tag/07E5).
4. **Route and pruning: PASS.** Read both retained Sheaf dependencies and searched
   the library, upstream ring-theory/algebraic-geometry sources, and Mathlib using
   different queries. Additional `msearch.py` Loogle search for
   `Function.Exact, Function.Injective` and grep for differential composition and
   exactness/injectivity found general exactness helpers, not an existing theorem
   replacing this comparison argument. The proof already uses Mathlib exactness
   directly. All remaining proof imports supply used declarations; the statement
   imports supply its algebra, extension, residue-field and Noetherian structures.
   Compared the old and new proof dependencies: both removed nodes are explicitly
   listed under `## No longer needed`. Read `dag/units/sk-thm-p1.json`: neither
   removed dependency realizes a unit statement or step. No unit route is bypassed.
5. **DAG agreement: PASS.** The existing node changes only `proof`, `proof_deps`,
   and `proof_origin`; its mathematical statement and Lean record are unchanged.
   Its proof steps follow the actual Lean proof and their uses union equals
   `proof_deps`. The new node has its source, complete proof, dependency records,
   Mathlib match, searches (including the honestly recorded unavailable service),
   creation record, blueprint ancestry, chapter, unit, and existing Mathlib Lean
   declarations. It adds neither a Lean module nor a hole.

Second-reading changes: corrected the theorem's natural-language proof outline to
follow the implemented H1 connecting-map chase and cite the middle-exactness leaf,
removing stale citations to the pruned full sequence and separate functoriality
argument. The proof term, imports, theorem signature, and node records needed no
repair. Added this independent review; scratch compilation and search artifacts
are outside the delivered Lean modules.
