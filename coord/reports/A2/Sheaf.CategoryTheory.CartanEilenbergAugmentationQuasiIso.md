## What changed

Replaced the sole sorry in
`CategoryTheory.Functor.cartanEilenberg_augmentation_quasiIso` with a complete
compiled reduction, keeping its signature and public imports unchanged.
The proof first derives the lower bound for K from the column quasi-isomorphisms
and the degree-zero homology computation for a single complex. It extends each
column augmentation, applies the acyclic-cone criterion, transports its vanishing
homology to the graded complexes of the actual augmentation cone, and applies
the degreewise finite filtered acyclicity criterion.

Added two modules, with one theorem per module:

- `Sheaf.CategoryTheory.DegreewiseFilteredAcyclic`: proves
  `CategoryTheory.degreewiseFiltered_acyclic` from the existing filtered spectral
  sequence and stationary-quotient declarations. The page-zero short-complex
  comparison, induction proving every positive page zero, transport to stationary
  graded pieces, and finite-filtration induction are all written and compiled.
  The finite-filtration induction itself is proved locally, without importing
  the holed `FiniteFiltrationInduction` module.
- `Sheaf.CategoryTheory.CartanEilenbergConeFiltration`: states the remaining
  geometric construction, with its full proof in words. Its statement specifies
  the degreewise image-sum formula on the actual cone, the bounds b and n+2,
  and graded homology isomorphisms with the extended column cones. It does not
  assume that a column augmentation is a quasi-isomorphism. Thus it does not
  assert the item's conclusion, even implicitly.

Updated the item's proof, proof_deps and proof_origin; added the two matching DAG
nodes. There are no changed existing statements, definitions, public imports,
or forced adaptations. The source read was Stacks Tags 0133, 012W and 015J at
https://stacks.math.columbia.edu/tag/0133,
https://stacks.math.columbia.edu/tag/012W and
https://stacks.math.columbia.edu/tag/015J.

All three modules compile together through lcompile.py --all, with no errors or
warnings. New declarations have explicit binders, module headers, proof sources,
and lines of at most 100 characters. The delivery dry run is the final check.

## Proved and sorry left

Closed the original hole:
`CategoryTheory.Functor.cartanEilenberg_augmentation_quasiIso`
(node `lem-sp-cartan-eilenberg-augmentation-quasi-iso`). No sorry remains in the
item's module.

Added and proved:
`CategoryTheory.degreewiseFiltered_acyclic`
(node `lem-sp-degreewise-filtered-acyclic`). Its three private helpers/main
subarguments contain no sorry. This theorem still depends on the existing
holed stationary-quotient theorem, and on the existing filtered spectral
sequence construction; their proofs are other items, not part of this delivery.

The only new sorry is:
`CategoryTheory.Functor.cartanEilenberg_cone_filtration`
(node `lem-sp-cartan-eilenberg-cone-filtration`). Its proof is exactly `by sorry`
in its own new module, with the source and full natural-language construction.

Accounting: one original hole closed, one lower hole added. This is a
**decomposition**, not a net hole reduction or a proof independent of remaining
sorries. The real proof now includes the full spectral-page vanishing and
finite-filtration induction, and all glue from column quasi-isomorphisms to the
original augmentation's quasi-isomorphism.

No data is extracted from an unproved existence theorem into a definition.
The existence of the pinned cone filtration is eliminated only inside a proof
of a proposition. Its degreewise subobjects are specified by an explicit
image-sum formula, and its subcomplex lifts are unique through monic arrows.

## No longer needed

Removed the following direct proof imports from the item:

- `Sheaf.Algebra.Homology.FilteredComplexSubquotients`;
- `Sheaf.CategoryTheory.FilteredComplexSpectralSequence`;
- `Sheaf.CategoryTheory.Filtration`;
- `Sheaf.CategoryTheory.DoubleComplexTotal`.

These are still reached through the presentation and the two new modules.
Consequently no whole module is claimed pruned from the target import closure.
The spectral-sequence import now belongs privately to the generic acyclicity
proof, which uses it. Filtration and subquotient definitions are public imports
where the new statements need them. DoubleComplexTotal remains a transitive
public import of the unchanged presentation interface.

The item's direct proof_deps no longer includes
`def-sp-double-complex-total`, `def-sp-filtered-complex-subquotients`,
`def-sp-filtration`, or
`lem-sp-filtered-complex-associated-spectral-sequence-construction`:
these appear in the two lower nodes where they are actually used.
`def-sp-injective-resolutions` is also removed from the direct proof route:
no injectivity or injective-resolution theorem is needed; the column hypothesis
is used directly as a QuasiIso. Existing statement dependencies are unchanged.
None of these nodes is claimed globally unreachable.

The proof does not use `Sheaf.CategoryTheory.FiniteFiltrationInduction` or its
holed graded-map and isomorphism theorems; the needed zero-graded-piece induction
is proved in 26 lines in DegreewiseFilteredAcyclic.

## Where the brief, the DAG or earlier work was wrong

The original plan described construction of the augmented cone and its finite
filtration but cited mainly definition nodes. Those signatures alone did not
provide the required bounded-below cone filtration with its pinned augmentation
and column-cone comparisons. The new construction node isolates exactly that
gap. The first-quadrant filtration definitions in DoubleComplexTotal have upper
bounds n rather than the cone's n+1 and assume both indices nonnegative; they
cannot directly be applied to an arbitrary lower bound b and the resolution
term at -1.

The existing `degreewiseFiltered_stable_quotient` supplies the needed convergence
interface. The bounded-filtered-complex page construction requires a globally
finite filtration, which is stronger than the degreewise finiteness here; it
was not imported. The existing source-library totalization comparison in
FromJoel/Algebra/Homology/BicomplexColumns assumes upper bounds in both directions;
this item has lower bounds and it was not imported either.

No statement was found false. Edge cases checked against the new formula:
empty diagonals; n+1<b (the whole cone object is zero); negative b; p<b
(the corresponding column and K^p are zero); p=n+1 (the remaining term is K^p
in column-cone resolution degree -1); the zero bicomplex; and zero augmentation
with a nonzero bounded-below K. In the last case the construction lemma does
not imply acyclicity: its graded cohomology contains K^p, as it should. This
checks that the new statement has genuinely removed the hrows hypothesis and
is only a geometric part of the original argument.

All three search kinds were run for each new node through msearch.py and are
recorded in searches.jsonl and the node records. LeanSearch returned HTTP
Internal Server Error and is recorded as unavailable, not as evidence of
absence. LeanFinder returned ordinary acyclicity, K-injectivity and mapping-cone
APIs, not either new comparison. The Mathlib grep searches returned zero hits.
DAG and blueprint searches for degreewise finite, mapping cone, 012W and 0133
found no existing node stating either new result. The existing stationary
quotient node was reused.

The blueprint ancestor command cannot follow the original node's created.item
because that field is a module name. Both new nodes use the original node's
explicit blueprint.from.node, thm-sp-if-e1, and extend its recorded via chain.
Its unit has no realized statement or proof-step nodes, so this work does not
bypass any unit realization.

## New nodes

`lem-sp-degreewise-filtered-acyclic` in
`dag/nodes/sec-abelian-varieties/lem-sp-degreewise-filtered-acyclic.json`
records the proved general acyclicity criterion, with only degreewise finite
bounds. Its proof dependencies are the existing filtered spectral sequence,
the existing stationary-quotient comparison, and the filtration definition.
Its Lean module is `Sheaf.CategoryTheory.DegreewiseFilteredAcyclic`.

`lem-sp-cartan-eilenberg-cone-filtration` in
`dag/nodes/sec-abelian-varieties/lem-sp-cartan-eilenberg-cone-filtration.json`
records the remaining construction from steps 2--4 of the original plan. It
specifies the actual cone's image-sum filtration, exact finite bounds and
graded homology comparisons. It has no quasi-isomorphism or injectivity
hypothesis and is strictly the geometric part of the proof. Its Lean module
is `Sheaf.CategoryTheory.CartanEilenbergConeFiltration`.

No change record is needed: no existing interface was changed.

## Second reading by A2

1. **Signatures and visibility.** I compared the delivered item module with the repository
version. The target declaration `CategoryTheory.Functor.cartanEilenberg_augmentation_quasiIso`
has the same signature byte for byte. The two added modules contain new declarations only;
no existing declaration or definition was altered, and proof-only imports remain private.
Verdict: pass.

2. **Compilation and axioms.** I compiled all three delivered modules with
`lcompile.py --all`; they compile without errors or warnings. The item has no `sorry`.
The only remaining `sorry` is the explicitly split theorem
`CategoryTheory.Functor.cartanEilenberg_cone_filtration`, whose proof is exactly `by sorry`
and whose source, proof, and node are recorded above. No axiom, unsafe, opaque,
implemented_by, extern, or hollow definition was introduced. Verdict: pass subject to the
single documented split node.

3. **New statements.** I checked both new statements against their edge cases and the
existing library declarations. `degreewiseFiltered_acyclic` is the needed degreewise finite
filtration criterion and has no stronger hypotheses than its proof uses. The cone-filtration
statement specifies the image-sum filtration, exact degreewise bounds, and graded column-cone
homology comparison, without assuming a column quasi-isomorphism; it is strictly the missing
geometric construction. Search records show no duplicate Mathlib or library declaration.
Verdict: pass.

4. **Route and pruning.** The item proof follows the target downward: column quasi-isomorphisms
first give the lower bound, the split cone-filtration construction supplies the graded pieces,
and the degreewise acyclicity criterion proves the mapping cone acyclic. The removed direct
imports and direct proof dependencies listed in `## No longer needed` are no longer used by
the item proof; the spectral sequence and filtration imports remain through the modules that
use them. Verdict: pass.

5. **DAG and unit.** The item node's proof, proof dependencies, and proof origin match the
Lean proof. Both added declarations have matching stage-3 nodes with source, complete proof
plans, searches, and Lean records. The unit route remains the recorded Cartan--Eilenberg
augmentation and finite-diagonal filtration route; no unit statement or target was bypassed.
Verdict: pass.

I changed only this second-reading report section after the first dry run; no Lean source or
DAG content was changed.
