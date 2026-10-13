## What changed

Proved `AlgebraicGeometry.Scheme.residueRankModel_differential_eval_eq_zero` without changing
its signature or existing docstring. The residue complex is explicitly evaluation at
`Over.mk (𝟙 U)` followed by extension along `(W.evaluation U w hwU).hom`.
Two proved private helpers establish scalar-extension finiteness/rank and differential
vanishing from equal term/homology dimensions. Coordinate vanishing uses the
scalar-extension adjunction, so no frame extension or coordinate compatibility hole remains.
Added proof imports for finite free sections, finite tensor products, dimension base change,
and finite-dimensional linear algebra. Added the proof-only import of
`Sheaf.AlgebraicGeometry.AffineFreeResidueSectionsCohomology`.
Both delivered modules compile cleanly through lcompile.py.
An initially added explicit Dimension.Constructions import was removed because the
finite-dimensional lemma import already provides finrank_baseChange. No definitions or existing
interfaces were changed and no forced adaptations are needed.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.residueRankModel_differential_eval_eq_zero`
(node `lem-sc-residue-rank-model-differential`), the only original hole (1 of 1).
No sorry remains in the assigned module.

Added and left: `AlgebraicGeometry.Scheme.affineFree_residueSections_cohomologyLinearEquiv`
(node `lem-sc-affine-free-residue-sections-cohomology`), in its own new module.
This is a decomposition, not a net hole reduction: one upper hole closed, one geometric
comparison hole added. The new lemma allows arbitrary finite free ranks, makes no
minimal-rank assumption, and has no zero-differential or coordinate conclusion.
Its output is used only in proofs of finiteness and dimensions; no object is defined by
choosing an arbitrary witness of a sorry-backed existence statement.

## No longer needed

No original import removed; both original public imports are required by the unchanged
statement. The second reader removed the redundant added proof import
`Mathlib.LinearAlgebra.FreeModule.StrongRankCondition`; compilation confirms its
instances are already available through the retained imports. No whole module is claimed globally pruned.
The direct proof-dependency edges to `def-pc-perfect-complex`, `def-pc-module-pullback`,
and `lem-sc-stalk-free-residue-cohomology-comparison` are replaced by the explicit affine
section comparison. The perfect-complex notion stays a statement dependency. Pullback
and residue-cohomology theory remain needed inside the geometric comparison, rather than
being proved or imported speculatively into the assigned module.
The adjacent-differential rank-sum formula and explicit base change of the entire frame
are unnecessary: cycles/homology dimension inequalities and one coordinate map suffice.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original plan's first cited theorem accepts a global sheaf
representative and a free stalk complex, not the localized-open complex K or its evaluated
section complex. Thus the canonical localized-open/residue comparison is substantial glue
not present in that signature. It is isolated as the new comparison node; the rest of the
original plan is proved with no new holes. The unit `sk-prop-av-cube` and its route are unchanged.

Checked edge cases: empty free bases give zero finite-dimensional modules; m=0 is covered
by the unrestricted `intro i`; arbitrary degrees are retained; no negative-vanishing or
rank-one hypothesis is introduced. An empty U cannot satisfy hwU. The generic scalar
extension helper derives nontriviality of its source ring from its map to a field rather
than silently assuming it. For nonzero differentials with nonminimal free ranks, the new
comparison still holds and does not falsely force vanishing.

Searches: LeanSearch was tried and returned Internal Server Error; LeanFinder returned
scheme residue tensor/pullback geometry but no comparison theorem; Mathlib grep had no
residue-cohomology match. Source searches found the proved private dimension argument in
MinimalFreeComparison and the proved sectionsLinearEquivOfIsoFree, which are used/adapted.
Blueprint searches found no duplicate affine residue section comparison.
Source pages read: https://stacks.math.columbia.edu/tag/064K,
https://stacks.math.columbia.edu/tag/06YB, https://stacks.math.columbia.edu/tag/0098,
https://stacks.math.columbia.edu/tag/0BCD, https://stacks.math.columbia.edu/tag/06YI,
and https://stacks.math.columbia.edu/tag/06YJ. Source pages are saved under the sandbox
`scratchpad/sources/`; they are not delivery files. Tag 06YB is stalkwise K-flatness,
not itself the derived-pullback comparison; the new docstring names 06YI/06YJ separately.

## New nodes

`lem-sc-affine-free-residue-sections-cohomology`, in
`dag/nodes/sec-abelian-varieties/lem-sc-affine-free-residue-sections-cohomology.json`,
states the missing linear cohomology comparison for the explicitly constructed residue
section complex. Its proof describes the natural affine counit chain comparison, bounded
free K-flatness, derived residue pullback through U, and exact residue-spectrum sections.
It inherits the original chapter/unit/blueprint ancestor and has the three search records.
No change record is needed: the new theorem has a separate module and the assigned module
imports it only for its proof.


## Second reading by X3

1. **Interfaces: pass.** Read the full diff against the repository module and checked
   the existing theorem signature byte for byte, including all derived-category
   instances, hfin, hb, hrank, he, the arbitrary frame and coordinate conclusion.
   Only proof imports, two private proved helpers and the proof body changed.
   The new comparison is in its own module. No definition or existing public
   signature changed; no change record or forced adaptation is required.
2. **Proof and axioms: pass with the reported comparison hole.** Both delivered
   modules compile using lcompile.py in import order. The only delivered sorry is
   `AlgebraicGeometry.Scheme.affineFree_residueSections_cohomologyLinearEquiv`.
   No forbidden declaration, external implementation, hidden axiom or holed
   definition occurs. A scratch copy with #print axioms for the item and the new
   comparison reported only propext, Classical.choice, Quot.sound and sorryAx.
   Read the scalar-extension rank argument, the cycles/homology dimension
   inequalities and epi cancellation, and the adjunction naturality calculation.
   In particular no faithfulness of scalar extension is assumed: the adjunction
   transfers the zero map into each residue coordinate directly.
3. **Split statement: pass.** The new statement computes the homology of an
   explicitly constructed complex, without a Betti-rank condition, any frame or
   differential-vanishing conclusion. It is a strictly geometric part of the
   argument, rather than the original theorem renamed. The docstring and node
   explain affine sheafification/sections, naturality of the chain comparison,
   bounded free K-flatness, restriction and residue pullback, and exact sections
   on the one-point spectrum. Read the saved Stacks sources 064K, 06YB, 06YI,
   06YJ, 0098 and 0BCD. Rank zero, the zero complex, arbitrary integer degrees,
   and a two-term free complex with a nonzero differential cause no exception:
   the comparison does not assert that this differential vanishes. Empty U is
   excluded by hwU. The given free isomorphisms and comparison equivalences are
   used only inside proofs; no arbitrary sorry-backed witness defines data.
   Independent LeanFinder search for “global sections finite free complex tensor
   residue field homology derived pullback affine scheme” returned scheme
   pullback/tensor constructions, not this comparison. Loogle confirmed
   Module.finrank_baseChange; Mathlib grep for homology/finrank found only Euler
   characteristic results. Repository searches with residue/linearEquiv and
   section/cohomology found the stalk comparison and affine chart tools, whose
   signatures do not accept this localized-site section complex. Its remaining
   geometric glue is not a proof that can be closed by directly applying them.
4. **Route and pruning: pass.** The upper hole is opened and all algebraic and
   coordinate arguments are proved; only the geometric identification remains.
   This is one hole closed and one added, hence a decomposition with no claimed
   net hole reduction. The No longer needed section lists every removed old
   proof-dependency edge: def-pc-perfect-complex, def-pc-module-pullback and
   lem-sc-stalk-free-residue-cohomology-comparison. No whole module is claimed
   pruned. Read dag/units/sk-prop-av-cube.json: its unit statement, step and
   realized fields are untouched; this item is internal glue below that route.
   Retained proof imports provide the finite-dimensional inequalities, tensor
   finiteness and finite free section equivalence. The comparison module's
   additive-adjunction import is needed in its statement's let-instance.
5. **DAG: pass.** Checked both node Lean statements against their files, all
   referenced node identifiers, and proof_deps against the union of proof-step
   uses. The existing node changes only proof, proof_deps and proof_origin;
   the new node has source, full proof, three search records, status, creation
   record, blueprint ancestor, chapter/unit and verbatim Lean statement.
   The item node now records the actual dimension/adjunction reduction.

Changed in this second reading: removed the redundant StrongRankCondition proof
import and documented this independent review. The theorem proof and all
statements were otherwise retained.
