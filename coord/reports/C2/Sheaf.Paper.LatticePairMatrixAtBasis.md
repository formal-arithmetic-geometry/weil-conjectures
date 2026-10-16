## What changed

Proved `AlgebraicGeometry.ProEtale.integralLatticePair_matrixAtBasis` in
`Sheaf.Paper.LatticePairMatrixAtBasis` with its original statement unchanged.
The proof transports the finite integral section basis through the tensor unit,
rationalization and rational frame. Invariant basis number over the nontrivial
continuous-section ring reindexes the resulting basis, and its coordinate equivalence
constructs the invertible matrix. Naturality and the integral basis expansion give the
image equality on every further slice. The empty-object case is handled separately
by subsingleton coefficients and free sections; rank zero needs no exception.

Added the fully proved helper `AlgebraicGeometry.ProEtale.localFreeTensorUnit_isIso`
in `Sheaf.Paper.LocalFreeTensorUnit`. Finite tensor coordinates identify the restricted
additive tensor presheaf with a free sheaf. Restriction preserves local bijectivity of
the sheafification unit, making its section map an isomorphism on the specified free
neighborhood. This helper allows arbitrary finite basis-index universes and includes
empty bases, zero rings and empty objects.

The existing public import is unchanged. Added proof-only imports for the helper,
invariant basis number, tensor-product bases, and the existing free-sheaf section API.
The helper imports the existing lattice definitions publicly and the free-sheaf,
tensor-product and local-bijectivity API for its proof. Updated both DAG proof routes.
No existing public definition or signature changed. No consumer adaptation is needed.
The static checker requires the proof-context change record
`coord/changes/lattice-pair-matrix-proof-context.md`; it lists all downstream users.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.integralLatticePair_matrixAtBasis`
(node `lem-weil-pbc-lattice-pair-matrix-at-basis`).

Added zero holes. The new theorem
`AlgebraicGeometry.ProEtale.localFreeTensorUnit_isIso`
(node `lem-weil-pbc-local-free-tensor-unit`) and every private helper are proved.
No `sorry` remains in either delivered Lean module. This is a proof, not a decomposition.

Both modules compile cleanly in import order through `lcompile.py` (45.6 and
40.7 seconds). The delivery dry run also completed both axiom probes without finding
any disallowed axiom; its initial preflight requested the additional LeanSearch
record and the proof-context change record, which are included here.

## No longer needed

The proof does not use `AlgebraicGeometry.ProEtale.exists_latticeFreeScalarExtensionIso`, corresponding to planned
proof dependency `lem-weil-pbc-lattice-free-scalar-extension`. Removed that proof edge
from the assigned node. Its module `Sheaf.Paper.LatticeSheafBasic` remains necessary
for the coefficient sheaves, lattice-pair definitions and scalar-extension interface;
this delivery claims no whole-module pruning.

No existing import was removed. The localized-site and sheaf-module category API remain
used. The old direct edge `def-pur-sheaf-tensor-product` is no longer in the assigned
node: that dependency is now recorded in `lem-weil-pbc-local-free-tensor-unit`, so it
remains a transitive dependency. The presheaf-module sheafification dependency is also
explicit in the new helper node. No unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned argument can use invariant basis number directly over the ring of
continuous K-valued sections once a point makes that ring nontrivial. It need not
evaluate the two coordinate matrices to compare their ranks over K.

The free-sheaf scalar-extension theorem alone does not provide the sectionwise
comparison on a neighborhood of an arbitrary locally free module. The new proved
helper supplies this slice-local tensor-unit comparison, including its restriction
compatibility and the sheafification argument. No statement was false or weakened.

The blueprint ancestor utility returned `None` for the previously created assigned
node. The new node therefore inherits its recorded blueprint ancestor and extends
its recorded `via` chain with the assigned node.

## New nodes

`lem-weil-pbc-local-free-tensor-unit`, module `Sheaf.Paper.LocalFreeTensorUnit`,
declaration `AlgebraicGeometry.ProEtale.localFreeTensorUnit_isIso`: the tensor unit
is an isomorphism on sections of any object factoring through a finite free basis
neighborhood. The node records the explicit finite tensor-coordinate construction,
naturality, sheaf condition and local-bijectivity proof. It has no remaining hole.
Four logged queries cover the three required search categories and found general
sheafification API but no exact comparison. The change record is
`coord/changes/lattice-pair-matrix-proof-context.md`.


## Second reading by C2

1. **Unchanged interface: pass.** Compared the delivered existing module against
   the read-only repository with `diff`, then extracted the entire
   `integralLatticePair_matrixAtBasis` declaration header through `:= by` and
   checked byte equality. It is identical. The only existing declaration is that
   theorem; all added definitions and lemmas in its module are private proof
   helpers. The public import remains `Sheaf.Paper.LatticeSectionMatrix`; added
   imports are proof-only. The context-only change is accurately recorded in
   `coord/changes/lattice-pair-matrix-proof-context.md`; there are no forced
   adaptations or changed target definitions.

2. **Proof and axioms: pass.** Read both modules in full, including the local
   tensor-coordinate isomorphism, its pure-tensor naturality argument, the
   restricted sheafification-unit proof, basis transport, matrix orientation,
   and both inclusions of the lattice-image equality. Both files compile without
   warnings through `lcompile.py` in import order. Scratch copies appended
   `#print axioms` to each public theorem: both print exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Neither delivered file
   contains `sorry`, forbidden declaration forms, or hollow definitions.
   The inverse maps used in coordinates are inverses of supplied isomorphisms;
   `Classical.choose_spec` is used only for the existing tensor restriction-map
   characterization, not to introduce an arbitrary object from a holed existence.

3. **New statements and edge cases: pass.** There are zero split-off holes. The
   new proved theorem `localFreeTensorUnit_isIso` is strictly the local comparison
   needed before transporting the basis; it does not restate the matrix target.
   Finite tensor products of coordinates work for the empty basis and zero rings.
   For the main theorem, nonempty W supplies nontriviality of the continuous
   coefficient ring, enabling invariant basis number; empty W makes every
   further test object empty, and both image sets are nonempty subsets of a
   subsingleton. Rank zero uses the same empty finite sums. Read the source
   Proposition 6.8.4(6), pp. 59–60, and its local lattice argument. The tensor
   comparison is the explicit auxiliary construction needed for its basis step.
   Independently searched Mathlib with `msearch.py` using the new phrases
   "Restrict a scalar extension tensor presheaf to a slice where the module is
   finite free" (LeanFinder), `CategoryTheory.Presheaf.isLocallyInjective_whisker`
   (Loogle), and a sheafification/free/over-category grep. Read the returned
   free-sheaf and sheafification API and searched `lean/Sheaf`, the upstream
   module-category files, and the existing scalar-extension theorem. The hits
   provide the general tools used here, not the exact slice-local sectionwise
   tensor-unit assertion. The new statement has its source, proof docstring,
   searches, and node.

4. **Top-down route, imports, and pruning: pass.** The main proof uses standard
   basis/scalar-extension tools directly after its local tensor-unit comparison.
   The existing `exists_latticeFreeScalarExtensionIso` compares globally free
   sheaves but does not alone give the needed restriction compatibility for an
   arbitrary module on its specified basis neighborhood. No shorter exact
   library theorem was found. The helper needs the free-section, finite tensor
   product, and local-bijectivity APIs; the main module needs its helper, tensor
   basis, rank-comparison, and free-section APIs. Proof-only dependencies remain
   plain imports. Compared every old proof dependency: the scalar-extension edge
   is removed, and the old direct tensor-product edge is now a dependency of the
   helper. `LatticeSheafBasic` still supplies the actual definitions and stays
   imported through `LatticeSectionMatrix`, so no whole module is pruned.
   Read `dag/units/sk-thm-properbasechange.json` and its `_section.md`: all realized
   statement/step nodes and the projective-line, reduction, and torsion-assembly
   route are preserved; this change is below that level.

5. **DAG agreement: pass.** The existing node changes only `proof`, `proof_deps`,
   and `proof_origin`. Its first step now calls the new local tensor-unit theorem;
   its second step describes the actual nonempty/empty split, basis reindexing,
   natural columns, and image expansion. In both nodes `proof_deps` is exactly
   the union of the proof steps' `uses`. The new node's Lean signature matches
   its module verbatim, and it has the required source, blueprint ancestor,
   chapter/unit, creation record, searches, and Lean attachment. There are no
   added unproved statements to record.

**Changes made in this second reading:** clarified under `## No longer needed`
that `def-pur-sheaf-tensor-product` moved from a direct dependency of the assigned
node to a transitive dependency through the helper, and added this review.
No Lean proof or signature needed repair. The result closes one original hole
and adds zero holes; no whole-module pruning is claimed.
