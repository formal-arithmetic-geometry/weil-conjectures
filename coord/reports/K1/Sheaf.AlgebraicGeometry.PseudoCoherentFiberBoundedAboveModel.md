## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.exists_pseudoCoherent_fiber_boundedAbove_model` by a compiling
reduction. Its signature and every pre-existing public import are unchanged.

The proof unpacks pseudo-coherence, shrinks to an affine open containing the given point,
restricts the complex, preserves its free ranks and upper bound, and composes the exact
restriction comparisons in the derived category. It constructs a module complex through
full faithfulness of affinePerfectSheafification: finite free terms are actual Finsupp
modules, the differentials are preimages of the conjugated sheaf differentials, and
faithfulness proves square-zero and the upper bound. The resulting complex isomorphism
supplies the local derived model required by the fibre comparison.

The proved private helpers `affine_free_iso` and `affine_local_finiteFree_model` reproduce
the existing private construction in PerfectOfPseudoCoherentFiniteTorDimension. Those
private declarations cannot be applied from this module. Attempting instead to transport
through the spectrum-only AffineFiniteFreeSheafComplexLift and its sheaf equivalence
exceeded the 60-second limit during elaboration of the composite comparison. The direct
localized-site construction compiles in approximately 13 seconds without changing a
definition or increasing the compile timeout.

Added `Sheaf.AlgebraicGeometry.AffineBoundedAboveFiberBettiComparison`, whose one theorem
assumes an already supplied bounded-above free affine model and identifies its fibre
Betti numbers. It does not assume pseudo-coherence and does not choose a neighbourhood,
ring, chart or representative. The main proof supplies these objects independently,
then applies the comparison degree by degree. This is strictly the second part of the
original argument, rather than the existence conclusion under a different name.

Updated the parent node's proof, proof_deps and proof_origin to match this reduction.
No existing statement, definition, target, visibility or external module was adapted.
The second reader added proof-only imports for the new comparison's planned
localized-site transport, affine derived-pullback formula and bounded-flat K-flatness,
and corrected its K-flat source citation to Tag 064K.

Source reading: Stacks Project Tags 0BDI, 08DW and 08E7, read online at
https://stacks.math.columbia.edu/tag/0BDI,
https://stacks.math.columbia.edu/tag/08DW and
https://stacks.math.columbia.edu/tag/08E7.
The unit `sk-prop-av-cube` and its realization records are unchanged; only the local
model computation below that unit is decomposed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_pseudoCoherent_fiber_boundedAbove_model`
(node `lem-sc-pseudo-coherent-fiber-bounded-above-model`). The local affine finite-free
model construction, restriction of its derived comparison, and assembly of the
existential conclusion are proved. The two added private helpers have complete proofs.
There are no sorries in the item's module.

Added exactly one hole:
`AlgebraicGeometry.Scheme.affine_boundedAbove_fiberBetti_eq`
(node `lem-sc-affine-bounded-above-fiber-betti-comparison`). Its entire proof is
`:= by sorry`, in its own public statement module, with source and proof in words.
This is a decomposition: one upper hole closed and one strictly smaller comparison
hole added, not a sorry-free proof of the full mathematical theorem. The net textual
hole change in the delivery is zero. No arbitrary data is selected from this new
unproved theorem: it returns an equality of natural numbers for supplied data.

Both delivered modules compile locally, in dependency order, without warnings.

## No longer needed

Removed these proof-only imports from the item:

- `Sheaf.AlgebraicGeometry.AffineFiniteFreeSheafComplexLift`:
  `lem-pc-affine-finite-free-sheaf-complex-lift` is not needed by this route. The actual
  localized-site module model is constructed and proved directly in the item using
  full faithfulness, without the intermediate spectrum sheaf-complex transport.
- `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`:
  `lem-pc-flat-complex-derived-pullback` is not needed by the item's proof or by the new
  comparison's stated route. The latter uses the more directly applicable affine
  pullback formula and module bounded-above K-flatness instead of the general
  sheaf-flat-complex pullback statement.

The parent proof_deps no longer contains those two nodes. The second reader retained
`def-sc-derived-fiber-betti`: its definition is still used by the conclusion and comparison.
Other modules may still
need them; this report makes no assertion about pruning them from the whole library.
All original public imports remain, to preserve the item's exported interface.
The new proof imports are AffineBoundedAboveFiberBettiComparison and the existing
WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf API.

## Where the brief, the DAG or earlier work was wrong

The original node accurately identified the outstanding localized-site and residue-field
scalar transport. The existing affine lift supplies no fibre computation, and the
sheaf-flat pullback theorem alone does not identify its cohomology with the coordinate
ring residue-field tensor complex. That missing comparison is now explicit and can be
worked on without also reconstructing pseudo-coherent neighbourhoods.

No statement dispute was found. The new comparison was checked on empty affine opens
(no point z), the zero complex, rank-zero terms, bounds below the requested degree,
unbounded-below free complexes, and free terms of possibly infinite rank. The latter
are permitted because bounded-above flat complexes are K-flat and an isomorphism of
scalar fields preserves rank, hence finrank even in infinite dimension. Finiteness is
not needed for this comparison; the original proof still supplies finite free terms.

Searches: LeanFinder returned derived-category support and factorization results but
no local affine fibre comparison. Loogle for finrank and restrictScalars returned zero
hits. LeanSearch was unavailable (Internal Server Error). msearch grep returned no
hits; repository rg found the global K-flat stalk comparison, stalk-free residue
comparison and private affine module-model constructions. None has the supplied
localized affine representative and canonical spectrum-residue field of this theorem.
Whole-DAG title searches found the parent, its bounded one-degree caller and perfect
residue models, not a duplicate comparison node.

## New nodes

`lem-sc-affine-bounded-above-fiber-betti-comparison`, in
`dag/nodes/sec-abelian-varieties/lem-sc-affine-bounded-above-fiber-betti-comparison.json`,
is the fibre calculation for a supplied affine model. Its source is the affine
computation in Stacks Tags 0BDI and 08DW, and its proof separates exact localized-site
transport, bounded-above K-flat affine pullback, and cohomology/scalar-field dimension
transport. Its module is AffineBoundedAboveFiberBettiComparison and its declaration is
AlgebraicGeometry.Scheme.affine_boundedAbove_fiberBetti_eq. It inherits the parent chapter
and unit. No change record is needed because no existing public interface changed.

## Second reading by K1

1. **Unchanged public contract — pass.** Read the repository module and the complete
   sandbox diff. The sole existing declaration,
   `AlgebraicGeometry.Scheme.exists_pseudoCoherent_fiber_boundedAbove_model`, has a
   byte-identical signature: all three derived-category instance families, E, hE, x,
   the neighbourhood condition, existential ring and chart, upper bound, termwise
   free-and-finite assertions, and every i/z Betti equality are preserved. Only proved
   private helpers were added. No definition or target changed; no change record is
   necessary. Existing public imports and visibility are preserved.

2. **Proof and axioms — pass as a decomposition.** Recompiled both delivered modules
   in dependency order after the repairs, without warnings (5.7 and 15.9 seconds).
   Read the explicit Finsupp construction, conjugated differential preimages, faithful
   square-zero proof, zero-term reflection, restriction comparisons, and final
   existential assembly. The modules contain no forbidden declarations or attributes;
   their only textual sorry is the named public comparison theorem. Scratch copies
   with `#print axioms` show only propext, Classical.choice and Quot.sound for each
   private helper, and those three plus sorryAx for the main theorem and the split
   comparison. No object is chosen from the split theorem: it supplies an equality
   for the already constructed M. Choices of ranks and term isomorphisms come from
   the pseudo-coherence hypothesis and proved finite-free sheafification, and M itself
   is explicitly constructed.

3. **Split statement, sources, and search — pass.** Read Stacks
   [0BDI](https://stacks.math.columbia.edu/tag/0BDI),
   [08DW](https://stacks.math.columbia.edu/tag/08DW), and
   [08E7](https://stacks.math.columbia.edu/tag/08E7), together with the statements of
   affine_localized_site_derived_transport, derivedPullback_openRestriction_iso,
   derivedPullback_tilde_iso, acyclic_mapBifunctor_of_boundedAbove_flat, and the
   tilde/sections Mathlib leaf records. The comparison fixes U, its canonical section
   ring and chart, F, b, and the derived representing isomorphism. It neither assumes
   pseudo-coherence nor proves neighbourhood/model existence, so it is strictly the
   fibre-calculation part of the original argument. The upper bound plus free terms
   gives K-flatness without a finite-rank or lower-bound assumption. Open restriction
   and affine pullback compute the same residue fibre; the composite residue-field
   isomorphism respects the section-to-germ-to-residue map. Exact tilde and evaluation
   over a field then compute homology, and a semilinear bijection preserves finrank.
   The docstring records these maps and all three parts of the argument.
   Checked empty U (no z), a rank-zero complex, a single nonzero free term, i>b,
   arbitrary negative b, an unbounded-below complex, and an infinite-rank free term:
   infinite dimensions give finrank zero on both sides, with no false finiteness claim.
   Independently searched LeanFinder for dimension after residue tensor of a
   bounded-above flat complex (eight ordinary rank/base-change hits), Loogle for
   homology plus tilde (zero hits), and rg on affine/fibre/stalk declarations and DAG
   records. Read KFlatStalkResidueCohomology, StalkFreeResidueCohomologyComparison and
   AffineFibreSectionsTensor: these require a global sheaf/stalk representative or
   compute section rings, and do not state this supplied localized affine comparison.
   The remaining scalar and local-category identifications are substantial; this hole
   cannot be closed by applying those statements in a few lines.

4. **Top-down route and pruning — pass after repair.** The main proof starts from hE,
   shrinks once to an affine neighbourhood and proves its algebraic-model construction.
   The existing private construction in PerfectOfPseudoCoherentFiniteTorDimension is
   inaccessible; reproducing its proved argument introduces no new public duplicate.
   The spectrum-only affine lift requires extra complex transport; the direct localized
   construction is already correct and quick, so I did not rewrite it. The two removed
   proof dependencies/imports are exactly AffineFiniteFreeSheafComplexLift and
   FlatComplexDerivedPullback. Restored def-sc-derived-fiber-betti in the parent's
   dependency list because its definition remains used. Added the new comparison's
   planned proof-dependency imports as plain import, not public import. Read
   dag/units/sk-prop-av-cube.json: the general-cube application and its realized records
   are untouched; this local affine computation is below that unit's route.

5. **DAG agreement — pass after repair.** Compared the existing node JSON: only proof,
   proof_deps and proof_origin differ from the repository. Its first step matches the
   affine shrinking/free-complex construction and full faithfulness of the tilde leaf;
   its second applies the split comparison and the Betti definition. proof_deps is
   exactly the union of step uses. The new node has its supplied-model statement,
   verbatim Lean signature, source, three search methods, explicit proof steps and their
   dependency union, split status, K1 worker/item/date attribution, inherited chapter
   and unit, blueprint origin, and new-module Lean record. Its dependencies give the
   localized-site interpretation, affine pullback, K-flatness and sections computation;
   the elementary scalar-field finrank invariance is spelled out in the final step.

Changes by this second reading: three missing proof-only dependency imports in
AffineBoundedAboveFiberBettiComparison; corrected its K-flat source citation to 064K;
restored def-sc-derived-fiber-betti in the parent's proof step and proof_deps; expanded
this report. No Lean proof body or existing signature needed repair. One original hole
is closed and one comparison hole remains split off: a decomposition with net zero
textual holes, not a complete axiom-free proof of the mathematical item.
