## What changed

Proved `DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude` directly in
`Sheaf.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect`, preserving its
signature byte for byte. Unfold pseudo-coherence to obtain its actual bounded-above finite-free
model, use the closed upstream K-flat and tensor-comparison lemmas, and take good truncation
at the lower Tor bound. Prove the bottom cokernel finitely presented by its finite-free
presentation and flat by `ObjectProperty.flat_opcycles_of_exactAt`; apply
`Module.Flat.projective_of_finitePresentation`. The remaining terms are zero or finite free.
The canonical truncation map supplies the derived isomorphism.

Removed the first worker's false new finite-free-model theorem, its module and its node.
No new module or node is delivered. The source is [Stacks Tag 0658](https://stacks.math.columbia.edu/tag/0658),
read in full, with the cokernel flatness argument implemented using the existing closed
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` interfaces.

Added explicit public imports of `Mathlib.Algebra.Module.Projective` and
`WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude` for the unchanged signature.
Kept `FlatResolution` public because it supplies the ModuleCat instances used by that
signature; made `FlatModel` a plain proof import. Added plain proof imports of
`WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat` and
`Mathlib.RingTheory.Flat.EquationalCriterion`. The import interface change is recorded in
`coord/changes/RingPseudoCoherentFiniteTorPerfect-imports.md`. No target or definition changes.

## Proved and sorry left

Hole closed: `DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude`
(node `lem-pc-ring-pseudo-coherent-finite-tor-perfect`). One of one original holes closed.
Holes added: none. Sorries left in the delivered module: none. Split off: none.
This is a proof, not a decomposition. The rejected sandbox hole
`DerivedCategory.exists_bounded_finiteFree_model_of_pseudoCoherent_finiteTorAmplitude`
is removed rather than delivered. No proof depends on that declaration.

A scratch copy with `#print axioms` reports exactly `propext`, `Classical.choice`,
`Quot.sound`, with no `sorryAx`. The final module compiles cleanly via lcompile.py.
Original sources of the two direct importers, `PerfectAffineBoundedProjective` and
`PerfectOfPseudoCoherentFiniteTorDimension`, also compile against the revised module in
an isolated scratch overlay. They are not adapted or delivered.

## No longer needed

Removed direct imports:

- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`: the proved upstream
  `CochainComplex.kFlat_of_isStrictlyLE_of_flat` applies directly to ModuleCat.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: the conclusion is the inline bounded-projective
  existential and does not use scheme perfectness.
- `Sheaf.RingTheory.PseudoCoherentBoundedFiniteFreeModel`: the definition of pseudo-coherence
  already supplies a model with some upper bound; the statement does not require the upper
  bound to equal the supplied Tor bound.
- `Mathlib.RingTheory.Flat.CategoryTheory`: redundant for this proof after using the explicit
  module/categorical flatness bridge and EquationalCriterion.

Every old proof dependency no longer used is recorded here:
`lem-pc-pseudo-coherent-bounded-finite-free-model`, `lem-pc-bounded-above-flat-kflat`,
`def-pc-perfect-complex`. The old Mathlib leaf
`lem-weil-pbc-finitely-presented-flat-module-projective` remains used. The new proof also
unfolds `def-pc-ring-pseudo-coherent-complex`, which is recorded in proof_deps.
These are removed dependencies of this proof, not a claim that their modules are globally
unreachable; the maintainer's ledger determines global pruning.

The discarded new module `Sheaf.CategoryTheory.DerivedCategory.BoundedFiniteFreeModelOfFiniteTor`
and node `lem-pc-ring-pseudo-coherent-finite-tor-perfect-free-model` are absent from the delivery.

## Where the brief, the DAG or earlier work was wrong

The first worker's split-off theorem is false. For `R = k × k`, the finite projective module
`M = (k, 0)` in degree zero is pseudo-coherent and has Tor amplitude `[0,0]`. A bounded
complex of finite free R-modules has the same alternating sum of term ranks after base
change to either factor k. Its two fibre Euler characteristics therefore agree. For M they
are 1 and 0, a contradiction. Splitting a projective bottom cokernel off a free module does
not make it free. The source Tag 0658 concludes finite projective, not finite free.

The old DAG route also performed an unnecessary adjustment of the free model's upper bound
to the Tor bound b and used a ringed-space K-flat theorem on a one-point space. The actual
statement only needs some upper bound c, so the definition and the proved generic ModuleCat
K-flat theorem suffice. The truncation/flatness/projectivity route itself is preserved.
The earlier report's claimed proof was only an application of the false stronger assertion;
its earlier second-reading section is superseded by the independent reading below.

## Second reading by U3

1. **Visible statements and definitions.** Compared the whole delivered module with the
   repository using diff. The sole existing declaration's complete signature, including
   universes, CommRing, HasDerivedCategory, both hypotheses, termwise finite/projective
   requirements and orientation of Q(P) ≅ C, is byte for byte unchanged. No definition,
   additional hypothesis or weakened conclusion is delivered. The documented import-only
   interface adjustment has its change record and downstream table.
2. **Proof and axioms.** Compiled the final file via lcompile.py, then a scratch set containing
   the final source and both unchanged direct importers. All compile with no warnings or
   errors. Read the termwise truncation isomorphisms, finite-presentation argument, flat
   cokernel criterion and orientation of the inverse Q-image of the truncation map.
   #print axioms shows only propext, Classical.choice and Quot.sound. No sorry, axiom,
   unsafe, opaque, implemented_by, extern or data construction from an unproved existence
   assertion appears in the delivered file.
3. **Split statements and edge cases.** Rejected and deleted the finite-free-model split:
   the product-of-fields example above disproves it. There is no remaining split-off statement.
   Checked zero modules/zero ring, degenerate Tor intervals, n<a, n=a, n>a, and c<a.
   In the last case the bottom opcycles vanish by their epimorphism from zero. The actual
   truncation is a real existing construction and the final proof has no additional gap.
   Independently searched with msearch.py Loogle for
   `Module.FinitePresentation, Module.Flat, Module.Projective` (one exact leaf), and grep for
   `pseudo.?coherent|flat_opcycles|projective_of_finitePresentation` (the Mathlib leaf).
   Searched lean/ and the upstream DerivedCategory files for pseudo-coherence, finite Tor
   amplitude, truncation and cokernel flatness. The upstream Perfect theorem requires a
   Noetherian ring and cannot replace this arbitrary-commutative-ring criterion; the
   closed upstream FlatModel truncation tools can and are used directly.
4. **Shortest route, imports and unit.** The direct use of hPC removes the unnecessary
   prescribed-upper-bound hole; the direct generic K-flat lemma removes the ringed-space
   dependency. All remaining imports supply signature names/instances or actual proof tools.
   Listed every removed original proof_deps node above. Read dag/units/sk-thm-picard-duality.json:
   none of the pruned nodes realizes its statement or steps. The ancestor route through
   pseudo-coherence, Tor amplitude, good truncation and projectivity is retained. No
   unit-level step is replaced. Both original direct importers compile unchanged.
5. **DAG agreement.** Rewrote only proof, proof_deps and proof_origin of the existing item's
   node. Its four steps now describe the actual hPC model, closed upstream tensor/exactness
   tools, finitely presented flat bottom cokernel and termwise truncation transport.
   proof_deps is exactly the union of the cited definition node and projectivity leaf;
   closed upstream generic tools are named in the corresponding step text. The existing
   Lean record and all node statements are unchanged. No new node remains.

Second-reading changes: removed the false helper/module/node; wrote the complete valid
truncation proof; pruned unused imports and corrected import visibility; updated the
proof docstring, DAG proof fields and report; added the required import change record.
