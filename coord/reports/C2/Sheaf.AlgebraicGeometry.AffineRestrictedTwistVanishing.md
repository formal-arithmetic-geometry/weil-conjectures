## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_isZero_restricted_twist_moduleCohomology_degree` in its module. Added the strictly smaller helper module `Sheaf.AlgebraicGeometry.ClosedImmersionFixedDegreeVanishing`, whose theorem is used by the residue-class projective immersion argument. The proof imports only the modules used by these arguments.

## Proved and sorry left

Closed the one item hole in `AlgebraicGeometry.Scheme.Modules.exists_isZero_restricted_twist_moduleCohomology_degree`. Added one hole: `AlgebraicGeometry.Scheme.Modules.exists_isZero_closedImmersion_twist_degree` (node `lem-pc-c2-closed-immersion-fixed-degree-vanishing`). This is a decomposition, with net zero holes closed; the affine restriction and residue-class combination are complete. No sorry remains in the item module.

## No longer needed

No existing Lean import was removed; no module is claimed pruned. All seven added
proof imports are plain imports and supply declarations used in the proof.
Of the old node's proof dependencies, only
`lem-weil-pbc-closed-immersion-serre-vanishing` is no longer used directly. It is
replaced by the fixed-degree projective closed-immersion helper. The twist tensor
node remains needed and has been restored in `proof_deps`. Broad
`Sheaf.AlgebraicGeometry.CoherentSerreVanishing` and
`Sheaf.AlgebraicGeometry.ClosedImmersionSerreVanishing` were considered but are
not imported, because both routes are cyclic. Relative higher direct images and
an affine-cover maximum do not occur in this item's fixed-affine-open conclusion.

## Where the brief, the DAG or earlier work was wrong

The planned dependency `Sheaf.AlgebraicGeometry.ClosedImmersionSerreVanishing` is cyclic: it reaches this item through the projective graph and affine-open modules. The closed-immersion argument therefore had to be split into a local helper with no cohomology-edge dependency cycle. The stated mathematical route and target signature are unchanged.

## New nodes

`lem-pc-c2-closed-immersion-fixed-degree-vanishing` is the fixed-degree projective closed-immersion vanishing theorem used in the residue-class argument. No new change record is required.

The full projective argument was experimentally compiled, including ring-valued monomial Cech comparison, descending Serre induction and affine pushforward comparison. Delivery import checking then found that `WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion` itself now reaches the item through `Cohomology.DirectImage`. The final helper therefore leaves this projective step as its whole named sorry, avoiding that cycle. No other modules were adapted.

Searches: Lean Finder returned derived-category degree-bound lemmas but no ample twisting result; Loogle returned only ell-adic empty-scheme vanishing; Mathlib grep found no Serre twisting theorem. LeanSearch was unavailable (Internal Server Error). The source arguments were checked at https://stacks.math.columbia.edu/tag/01YS and https://stacks.math.columbia.edu/tag/0B5T. Edge cases: q is required positive; empty X, N=0, zero F and zero base ring are permitted and give zero positive cohomology. No instance is selected from mere existence to define an arbitrary object.

## Second reading by C2

1. Compared both delivered modules against the repository. The existing item's
   complete signature is byte-for-byte identical. Its existing docstring, public
   imports, namespace and visibility are unchanged. The other module is new;
   no definition, target or existing interface changes. Verdict: pass.
2. Both modules compiled with `lcompile.py --all`. Scratch copies with explicit
   `#print axioms` showed only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx` in the two public theorems. The item has no textual sorry; the helper's
   sole hole is its named public theorem, listed above. No forbidden declarations
   or hollow definitions occur. Chosen isomorphisms come from uniqueness or the
   stated isomorphism class; no arbitrary geometric object is defined from an
   unproved existence statement. Verdict: pass as a decomposition, not a completed
   axiom-free target proof.
3. Read the helper against [Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
   and [Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T). It is strictly smaller
   than the item: a specified projective closed immersion and a specified twist,
   without open restriction, ampleness, immersion construction or residue classes.
   Checked q>0 (essential), N=0, zero F, empty X and the zero base ring; these
   degenerate cases have zero positive cohomology. Independent Lean Finder,
   qualified Loogle and Mathlib grep searches found no usable theorem. The library
   does contain a stronger closed-immersion theorem, but its import path reaches
   this item through AffineMorphismCohomologyEdge, source DirectImage modules,
   IntegralIdealProperCohomology, the Chow and projective-graph modules, and
   AffineOpenTwistVanishingIndependent. Thus it cannot be applied here. The
   source Serre theorem also has cyclic imports and its projective-ring variant
   is private in that same closed-immersion module. The new specialized helper
   exposes the remaining projective step without asserting net progress.
   Expanded its docstring to give the complete descending-induction proof.
   Verdict: true and correctly sourced; left open because available proofs cannot
   be imported without a cycle.
4. Read the full affine reduction, finite-presentation descent, positive-power
   comparison and residue-class argument. The bound uses a finite sum rather
   than a maximum: each threshold is at most the sum, and n>=d*sum implies
   n/d>=sum since d>0. All transport is by module isomorphisms. No shorter usable
   import was found. The seven new imports are proof-only. The original public
   imports are retained for the signature. The unit record is unchanged (its
   `realized` lists were already empty); the proper/ample/projective route remains
   intact and no unit step is bypassed. Corrected the pruning report to list the
   exact old dependency replaced, and to claim no module pruning. Verdict: pass.
5. Compared the node proof steps, dependencies and origin with Lean. Restored
   `lem-pc-twist-tensor`, added the actually used coherent-affine-sections and
   quasi-coherent affine finite-presentation nodes, and corrected the affine-base
   reduction description. Added twist-cohomology, twist-tensor and cohomology
   dependencies to the helper's natural-language induction plan. Its node has
   the required source, searches, creation, blueprint, unit/chapter and verbatim
   Lean statement records. Verdict: pass after these metadata repairs.

Second reading changed the helper's proof docstring, both DAG proof descriptions
and dependency lists, and this report. No Lean statement or proof term changed.
