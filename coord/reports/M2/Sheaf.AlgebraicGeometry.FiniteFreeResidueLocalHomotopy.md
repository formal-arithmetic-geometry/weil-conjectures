## What changed

The assigned module now proves
`AlgebraicGeometry.Scheme.Modules.exists_restrict_homotopyEquiv_single_of_residue`
with its original signature and visibility. Its proof imports two new modules:
`Sheaf.AlgebraicGeometry.FiniteFreeResidueStalkHomotopy` and
`Sheaf.AlgebraicGeometry.FiniteFreeStalkHomotopySpread`.

The first supplies the homotopy normal form over Spec of the local ring. The second
extends a given local-ring homotopy equivalence to an open neighbourhood on Y.
The assigned module proves the remaining base-change argument: take the inverse
image open, pull back the equivalence, identify restriction with pullback and use
composition/congruence isomorphisms; finally identify pullback of the single free
complex with the single free complex on the inverse image open. The proof includes
the actual composition of homotopy equivalences for both comparisons.

The original node's proof and proof dependencies now describe this decomposition.
All three sandbox modules compile with lcompile.py. No existing statement,
definition, visibility or public import was changed. No other existing module was
adapted.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_restrict_homotopyEquiv_single_of_residue`
(node `lem-pc-finite-free-residue-local-homotopy`). No sorry remains in the assigned
module.

Added two holes, each the whole proof of a named public theorem in its own module:

- `AlgebraicGeometry.Scheme.Modules.nonempty_stalk_homotopyEquiv_single_of_residue`
  (node `lem-pc-finite-free-residue-stalk-homotopy`, module
  `Sheaf.AlgebraicGeometry.FiniteFreeResidueStalkHomotopy`). This is only the
  local-ring algebra: no neighbourhood or arbitrary morphism g occurs.
- `AlgebraicGeometry.Scheme.Modules.exists_restrict_homotopyEquiv_single_of_stalk`
  (node `lem-pc-finite-free-stalk-homotopy-spread`, module
  `Sheaf.AlgebraicGeometry.FiniteFreeStalkHomotopySpread`). This starts with an
  actual homotopy equivalence over Spec of a stalk and spreads it; it makes no
  residue cohomology hypothesis and asserts no arbitrary base change.

This is a decomposition, not a net proof gain: one hole closed, two added, net -1.
Neither lower theorem repeats the original theorem: the algebraic normal form and
the finite matrix extension are separate original proof steps, and the pullback
and restriction step is now proved in Lean. No definitions contain sorry, and no
data is defined by selecting a witness of an unproved mere existence theorem.

Edge cases checked mathematically: rank zero permits the zero complex; if i > d,
the residue assumption forces r = 0; i = 0 needs no negative residue hypothesis
because of the support bound; empty schemes supply no y or z to check; the
spreading statement allows arbitrary integer i, including i < 0, because its
hypothesis is already an actual local-ring homotopy equivalence. No reducedness or
Noetherian hypothesis is needed. All matrices and equations are finite by bounded
support and finite free terms.

## No longer needed

None. Every original public import is retained for the unchanged statement.
No planned mathematical dependency is discarded. The original direct dependency
`lem-weil-pbc-free-complex-unit-entry-splits` (module
`Sheaf.Algebra.Homology.UnitEntrySplits`) is now a proof dependency of the new
local-ring node rather than the assigned node: cancellation remains needed, so
this is relocation of that dependency, not pruning. The parent now has the two
new proof dependencies named above. No modules are claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan's third step contained a substantial finite-matrix spreading
argument with no corresponding declared node. It is now a separate, precisely
stated item. Its first two steps also require termination of cancellation, residue
rank comparison and conversion between modules and quasicoherent sheaves beyond
what the single unit-entry splitting theorem states; those are recorded in the
local-ring item's proof and docstring. The original theorem is mathematically
consistent and its signature was kept.

The literature files are absent in this clone. Their read-only copies were found
under /home/ubuntu/work-bp/sheaf/literature/: the blueprint's original perfect-locus
proof and Stacks algebra.tex, Tag 00MT, lines 24608--24655, were read. These agree
with the cancellation and finite extension argument. The new proof_origin records
are marked agent, because the bridge to the precise sheaf and homotopy interfaces
is written out here from those steps. The unit remains sk-thm-picard-perfect, and
its local finite-free reduction and base-change route are retained.

Mathlib search used the logged msearch.py LeanFinder, Loogle and source grep
queries. LeanSearch returned Internal Server Error and is recorded unavailable,
not a successful negative search. The hits give general homotopy and single
complex tools but no residue local-ring normal form or spreading theorem. The
existing minimal-free-model statement is about a pseudo-coherent derived object
and does not supply the required sheaf-level homotopy equivalence directly.

## New nodes

`lem-pc-finite-free-residue-stalk-homotopy` is in
`dag/nodes/sec-picard-framework/lem-pc-finite-free-residue-stalk-homotopy.json`,
with its theorem in `lean/Sheaf/AlgebraicGeometry/FiniteFreeResidueStalkHomotopy.lean`.
Its proof retains the existing unit-entry splitting node, explains termination
and the residue-dimension calculation, and ends over the local-ring spectrum.

`lem-pc-finite-free-stalk-homotopy-spread` is in
`dag/nodes/sec-picard-framework/lem-pc-finite-free-stalk-homotopy-spread.json`,
with its theorem in `lean/Sheaf/AlgebraicGeometry/FiniteFreeStalkHomotopySpread.lean`.
Its proof records extension of finitely many entries, shrinking for finitely many
chain and homotopy equations, and the automatic zero components outside support.

No change records are required: existing public interfaces are unchanged.

## Second reading by M2

1. Interface preservation: PASS. Read the complete diff against the repository.
   The original declaration signature, docstring, visibility and all public imports
   are byte-for-byte unchanged. Only its proof and two private proof imports differ.
   The other two modules and their nodes are new. No definition or target changed;
   no change record or forced adaptation is needed.
2. Proof and trust: PASS as a decomposition. Compiled all three modules in import
   order with lcompile.py, without errors or warnings. Scratch copies with
   `#print axioms` for each of the three declarations show exactly propext,
   Classical.choice, Quot.sound and sorryAx. The only direct holes are the two
   reported named lower theorems. No forbidden declarations or hollow definitions
   occur. The upper proof constructs the pullback/restriction and single/free
   comparisons and composes their actual homotopy equivalences. No data definition
   chooses an arbitrary witness from an open existence statement.
3. Split statements: PASS. Read each complete signature, docstring and node, the
   unit-entry splitting declaration, Stacks algebra.tex Tag 00MT, and the blueprint
   perfect-locus proof. Cancellation is valid over the nonzero local ring of a
   scheme point; finite total rank ensures termination, and reduction determines
   each remaining rank. Spreading involves finitely many matrix entries and
   equations, including homotopies in the adjacent degrees; zero terms outside
   support make the remaining equations automatic. Checked d = 0, r = 0, i = 0,
   i > d, negative i in the spreading theorem, and empty schemes. The two statements
   are separate strict parts of the original argument, not a restatement. Fresh
   LeanFinder searches used minimal complexes/contractible summands and extension
   of chain maps from germs; fresh Loogle searches used HomotopyEquiv with
   IsLocalRing and fromSpecStalk. Source searches covered local-ring and algebraic
   geometry Mathlib, lean/Sheaf and lean/WeilConjectures. The hits
   CochainComplex.exists_iso_single and TopCat.Presheaf.germ_eq are constituent
   tools, not either new theorem. Read MinimalFreeModel and
   PerfectFiniteFreeResidueModel: their derived statements do not directly give
   the sheaf-level homotopy equivalence required here. Neither lower hole can be
   closed by a short application of these results.
4. Route and pruning: PASS. All public imports supply notions in the signatures;
   the two added imports are proof-only and both are used. The old proof dependency
   lem-weil-pbc-free-complex-unit-entry-splits is no longer direct at the parent,
   and is explicitly reported as relocated to the local-ring node, not pruned.
   No old proof dependency is omitted from that accounting. Read
   dag/units/sk-thm-picard-perfect.json: its pre-existing realized fields are empty;
   this item does not modify them or bypass a recorded realization. The finite-free
   cancellation, neighbourhood extension and arbitrary base-change route remains.
5. Node agreement: PASS. The parent's three steps match the two theorem applications
   followed by the proved natural-isomorphism comparison. Its proof_deps is the
   union of their uses. Both new nodes have source, full proof, proof_origin,
   statement dependencies, search records, creation and blueprint records, inherited
   chapter/unit, and Lean records matching the new statements. Neither new node
   occurs in the repository baseline.

Second-reading changes: added the successful independent Loogle searches to both
new nodes and this review to the report. No Lean repair was necessary. Confirmed
one original hole closed and two lower holes added (net -1); no modules pruned.
