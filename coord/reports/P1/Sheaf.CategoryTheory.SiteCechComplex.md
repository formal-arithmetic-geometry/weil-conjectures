## What changed

Proved every verification theorem in `Sheaf.CategoryTheory.SiteCechComplex`, preserving
all existing declaration signatures and definitions. Added private, fully
proved helpers for recursively constructing fibre products, projection extensionality,
cochain index maps, their cosimplicial object, and comparison morphisms. Added proof-only
imports of `Mathlib.AlgebraicTopology.AlternatingFaceMapComplex` and
`Mathlib.Algebra.Homology.HomologicalComplexAbelian`.

Existence uses only pullbacks along covering arrows. The square-zero proof identifies the
specified differential with Mathlib's alternating coface differential. Comparison is
constructed by restriction along the unique product isomorphisms. Exactness uses exact
evaluation, componentwise preimages, and degreewise short exactness; extension by zero is
handled using `extendXIso` on the image and zero objects elsewhere. Updated the existing
node's proof and proof origin to describe these arguments. The unit route is unchanged.

Read the recorded node and its four proof dependencies, their Mathlib realizations, and
the source statements at https://stacks.math.columbia.edu/tag/03AK,
https://stacks.math.columbia.edu/tag/03AQ, and https://stacks.math.columbia.edu/tag/00VH.
The recorded local Stacks TeX files are absent on this machine, so the source was read
from the official Stacks pages. Search used LeanFinder, Loogle, and ripgrep over Mathlib
and both library roots. No existing theorem directly constructs these chosen covering
products, but Mathlib supplies the cosimplicial square-zero theorem and exactness tools.

## Proved and sorry left

All 14 original sorries are proved:

- `CategoryTheory.SiteCechComplex.exists_of_covering`
- `CategoryTheory.SiteCechComplex.fibreIso_exists_unique`
- `CategoryTheory.SiteCechComplex.differentialValue_zero`
- `CategoryTheory.SiteCechComplex.differentialValue_add`
- `CategoryTheory.SiteCechComplex.differential_squared`
- `CategoryTheory.SiteCechComplex.cochainsMap_comm`
- `CategoryTheory.SiteCechComplex.complexMap_id`
- `CategoryTheory.SiteCechComplex.complexMap_comp`
- `CategoryTheory.SiteCechComplex.complexFunctor_additive`
- `CategoryTheory.SiteCechComplex.integerComplexFunctor_additive`
- `CategoryTheory.SiteCechComplex.cohomologyFunctor_additive`
- `CategoryTheory.SiteCechComplex.degreewise_exact`
- `CategoryTheory.SiteCechComplex.comparison_exists`
- `CategoryTheory.SiteCechComplex.shortExact_map`

Each belongs to `def-weil-pbc-site-cech-complex`. No sorry remains, and no new node or
postponed statement is introduced. The module compiles locally without warnings.
The final dry run additionally checks the axioms of all declarations and compiles on
the project server.

## No longer needed

Removed the direct imports `Mathlib.Algebra.Category.Grp.AB` and
`Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`: AB4* is unused, and
ExactFunctor is already supplied by the proof import HomologicalComplexAbelian.
Use public `Mathlib.Algebra.Category.Grp.Abelian` for the abelian-group instances
required by definitions, and proof-only `Mathlib.Algebra.Homology.ShortComplex.Ab`
for elementwise exactness. No node or project module is pruned. All four recorded proof dependencies
remain relevant: site pullbacks, the complex/cohomology formalism, exact evaluation of
presheaves, and degreewise short exactness of complexes. A separate new development of
alternating-sum cancellation is unnecessary: Mathlib already proves it for cosimplicial
objects. Categorical exactness of arbitrary products is not needed in the proof, since
preimages are chosen componentwise; the narrower imports suffice.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or unusable statement was found. The second reader repaired
the overly broad public imports (record: `coord/changes/site-cech-complex-imports.md`). The product induction uses the
first factor and the tail instead of the last factor and the initial segment; the node
now describes the implemented order. The extra site axioms in `exists_of_covering` are
not needed by its proof, and its signature is preserved. No change to a target, public
definition, or statement is made.


## Second reading by P1

1. **Unchanged meaning: PASS.** Read the entire repository/sandbox module diff and
   checked the declaration tables independently. All existing signatures are byte for
   byte identical, every existing definition body is identical, and no declaration is
   removed. The only interface change is import pruning, recorded in
   `coord/changes/site-cech-complex-imports.md`; no target or mathematical definition changes.
2. **Proof and axioms: PASS.** Independently compiled the delivered module without
   errors or warnings. No sorry, axiom, unsafe, opaque, implemented_by, extern, or kernel
   checking bypass occurs. A scratch copy with `#print axioms` for all 14 verification
   theorems shows only propext, Classical.choice and Quot.sound. Read the recursive
   pullback construction, the projection-uniqueness arguments, the cosimplicial
   identification, comparison naturality, and the exactness/zero-extension proofs.
   None relies on an open project theorem.
3. **Split-off statements: PASS (none).** No public declaration or postponed theorem
   is introduced. Private helpers are proved construction details, not restatements.
   Checked singleton tuples/degree zero, empty covering index sets (the tuple-indexed
   groups are trivial), repeated factors, and integer degrees outside the embedding.
4. **Route and pruning: PASS after repair.** Mathlib's alternating-coface square-zero
   result is the direct route; the existing general Čech functor needs finite products
   and cannot supply existence from covering pullbacks alone. Componentwise choice
   proves exactness without AB4*. Removed the AB and redundant ExactFunctor imports,
   replacing AB with public Grp.Abelian and proof-only ShortComplex.Ab. Both added
   imports from the first worker are proof-only. All 14 direct importers compile
   unchanged against the narrowed module in a scratch overlay. The four old proof
   dependencies are genuinely used through their Mathlib realizations, so no DAG node
   is pruned. Read `dag/units/sk-thm-p1.json`: its realized statement/steps are unchanged,
   and this item does not bypass or replace a unit realization.
5. **DAG agreement: PASS.** Compared the node diff: only proof and proof_origin change.
   Checked all four dependency records against the actual Mathlib declarations. The
   recorded steps match tail-product induction, universal-property index maps,
   alternating cofaces, product comparison, componentwise exactness and degreewise
   short exactness after extension by zero. proof_deps is precisely the union of uses.
   No new node is required for an unfinished result because none remains.

Changed only imports and their report/change record during this reading; the first
worker's correct proofs and DAG proof description are preserved. The public-import
cleanup is declared explicitly for independent delivery review.
