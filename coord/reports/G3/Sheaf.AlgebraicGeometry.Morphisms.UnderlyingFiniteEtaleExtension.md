## What changed

Replaced the single sorry in
`Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension` with a complete Lean
assembly of the Noetherian case and the limit reduction of Stacks Tags 0EYJ and 0EZJ.
Added two proof-only imports, `NoetherianFiniteEtaleExtension` and
`NoetherianSpreadingData`, each with one named theorem and a matching new node.
The original declaration, universe, hypotheses, conclusion and public imports are unchanged.
Updated the original node's proof, proof dependencies and proof origin to match the Lean proof.

The approximation theorem supplies descended objects and comparison maps, without any
extension. The Noetherian theorem constructs an underlying finite etale extension only for
a Noetherian base. The parent applies the latter to the former, takes the pullback along
the family comparison, constructs the map from the original torsor, and proves the desired
cartesian square by pasting and cancellation. It proves surjectivity directly: the family
is connected, the rational point makes the extension nonempty, and a finite etale map has
nonempty clopen image. Thus neither new statement is the original theorem renamed or its
hypotheses repackaged. The unit's Noetherian/limit route remains in place.

Compiled all three modules together and the parent separately without errors or warnings.
LeanSearch was attempted for each new node but returned Internal Server Error; this is
recorded as unavailable. LeanFinder, Loogle and grep searches ran and found no matching
scheme extension or approximation theorem.

## Proved and sorry left

Decomposition (one upper hole closed, two lower holes added; net -1 hole closed):
`AlgebraicGeometry.Scheme.GaloisCover.exists_finiteEtale_extension`, node
`lem-sbc-underlying-finite-etale-extension`. No sorry remains in the assigned module.

Every sorry added by this delivery:

- `AlgebraicGeometry.Scheme.GaloisCover.exists_finiteEtale_extension_noetherian`, node
  `lem-sbc-noetherian-finite-etale-extension`, in
  `Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension`.
- `AlgebraicGeometry.Scheme.GaloisCover.exists_noetherian_spreading_data`, node
  `lem-sbc-noetherian-spreading-data`, in
  `Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData`.

Each is a public named theorem with its entire proof `by sorry`, a source, a full proof
sketch and a blueprint tag. There are no new definitions or axioms. The parent still
transitively depends on these two sorries; this is a stage-3 reduction, not an axiom-free
proof of the entire spreading theorem.

## No longer needed

None of the original imports, nodes or modules was pruned. All original imports support
the unchanged statement and its public interface. Extra direct imports of
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` and
`Mathlib.Topology.Connected.Clopen` were tested and removed from the final proof because
the required declarations are already available. The assigned node had no proof
dependencies to remove. No separate surjectivity lemma or action-extension theorem is
needed for this proof.

## Where the brief, the DAG or earlier work was wrong

The node's four-step narrative had an empty proof_deps list and supplied no Lean
declarations for the trait, maximal-open or limit steps. The delivery therefore states
the Noetherian construction and the approximation data as two strict parts of that
argument. The classical tame, purity and depth-two inputs remain grouped in the
Noetherian statement's proof sketch for its future worker.

The mathematical statements were checked against the official Stacks pages for Tags
0EYJ and 0EZJ. Their printed Galois cover convention is connected; the project explicitly
allows disconnected torsors. The existing component/stabilizer reduction is retained
and explained in the Noetherian theorem's docstring and node: the split section meets
every component, stabilizer orders divide the group order, and induction and disjoint
union recover the original torsor.

Edge cases: an integral base is nonempty; geometrically connected fibres and the section
make the total family connected and nonempty. An empty extended cover is ruled out by
the rational point composed with its comparison map. The trivial group is allowed, and
no connectedness of the original torsor is assumed. The approximation lemma deliberately
requires only the commuting family maps and the generic-cover pullback needed for
assembly; it does not falsely claim that the square of generic fibres and whole families
is cartesian.

## New nodes

`lem-sbc-noetherian-finite-etale-extension` isolates the Noetherian trait/maximal-open
construction in Tag 0EYJ. Its conclusion is an underlying finite etale morphism with a
cartesian generic comparison; surjectivity is proved in the parent.

`lem-sbc-noetherian-spreading-data` isolates the limit descent before application of the
Noetherian case in Tag 0EZJ. It constructs normal integral Noetherian data, a generically
split torsor at that stage and the comparison maps. It asserts no extension. Both nodes
inherit chapter `sec-smooth-base-change` and unit `sk-prop-input-spreading` and record the
actual Mathlib searches. No change record is needed because no existing statement or
definition changes.

## Second reading by G3

1. **Unchanged interface: pass.** Compared the parent module with the repository using
   `diff -u` and separately compared the declaration header through `:= by` byte for byte.
   The existing signature, universe, hypotheses, conclusion, docstring and public imports
   are identical. The only Lean differences are two plain proof-only imports and the proof
   body. Both other modules are new; no existing definition or statement changes and no
   change record is required. The existing node changes only `proof`, `proof_deps` and
   `proof_origin`.
2. **Lean proof and axioms: pass as a decomposition.** Independently compiled all three
   modules in import order with lcompile.py, with no errors or warnings. Inspected all
   bodies: the parent has no sorry; each new module has exactly one public named theorem
   whose entire proof is `by sorry`. No definitions or forbidden trust mechanisms are
   added. A scratch copy compiled with `#print axioms` for all three declarations reports
   precisely `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The parent is not
   an axiom-free proof while these two lower statements remain open.
3. **Split statements: pass.** Read both statements, docstring arguments and node records
   against [Stacks 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ) and
   [Stacks 0EZJ](https://stacks.math.columbia.edu/tag/0EZJ). The first restricts the argument
   to Noetherian bases; the second constructs descent data and asserts no extension.
   Neither merely renames the parent. Checked the trivial group, a field base, the
   impossibility of empty generic family/cover under the section and rational-point
   hypotheses, and disconnected torsors. Smooth connected fibres are regular and hence
   integral, so the component/stabilizer reduction applies; each component surjects onto
   the connected generic family and meets the split section fibre. Stabilizer orders
   divide the invertible group order. The generic-cover comparison square is cartesian;
   the comparison between the generic fibres and the entire families is only required
   to commute, as it should be. Neither hole can be closed in a few minutes from the
   available library. Independent LeanFinder searches for unramified covering extension
   and descent to normal Noetherian stages, Loogle search for `"Smooth", "IsIntegral"`,
   Mathlib grep for tame/purity/Noetherian approximation, and local rg searches for
   spreading, approximation, generic-fibre extension and torsors found no replacement.
   The upstream `GaloisCover.exists_isPullback_of_genericFibre` already depends on this
   parent, so using it here would introduce a cycle.
4. **Route and pruning: pass.** Read the assembly top down. Pullback pasting, the universal
   property and right cancellation produce exactly the required generic comparison.
   Finiteness and etaleness follow by base change. Smooth geometric connectedness gives
   connectedness of C; composing the rational point with psi gives a point of P; the
   nonempty clopen image of its finite etale projection is all of C. Both new imports
   are needed and are plain imports. The original proof_deps list is empty, so its
   complement in the new dependency list is empty and the pruning report is complete.
   Read `dag/units/sk-prop-input-spreading.json`: its realized slots are already empty,
   and remain unchanged; its Noetherian/trait/maximal-open and limit route is retained
   in the two lower arguments, not bypassed.
5. **DAG correspondence: pass.** Compared each node's Lean signature to its module
   modulo whitespace and checked that the union of proof-step uses equals proof_deps.
   The parent's steps describe the actual applications and direct Mathlib assembly.
   Each new node has source, complete argument, search records, split status, created
   record, blueprint provenance, chapter, unit and Lean record required by the brief.

Changes by the second reader: corrected the progress wording under
`## Proved and sorry left` to call this a decomposition explicitly and give its hole
accounting (one closed, two added, net -1). Added this independent review. No Lean proof,
statement, import or node needed repair.
