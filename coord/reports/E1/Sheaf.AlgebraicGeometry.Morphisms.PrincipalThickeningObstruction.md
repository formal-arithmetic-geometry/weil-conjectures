## What changed

PrincipalThickeningObstruction now has a complete proof of
AlgebraicGeometry.Scheme.principal_thickening_obstruction, with its signature unchanged.
It imports the existing cohomology LongExact API and the new proof dependency
PrincipalThickeningCokernelSections. The ideal image and its multiplication definition
are unchanged. A proved private boundary_naturality lemma derives naturality directly
from Ext extension-class naturality and associativity. The proof constructs explicit
short complexes and uses exactness to lift boundary-zero sections.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.principal_thickening_obstruction
(new-principal-thickening-obstruction), the sole original hole.
Added and left: AlgebraicGeometry.Scheme.principal_thickening_cokernel_sections
(new-principal-thickening-cokernel-sections), in its own new module.
This is a decomposition: one hole closed, one strictly geometric comparison hole added;
net hole reduction is zero. The new lemma asserts a functorial H^0/section identification,
not a boundary map, exactness, or ambient lifting. All cohomology and lifting glue is proved.
No sorry remains in the item, no data definition was added, and the comparison witness
is eliminated only inside the theorem proof.

## No longer needed

None. Both original public imports support the unchanged public interface.
The node previously had no proof dependencies, so no existing dependency node or module
can be pruned by this delivery. The new imports are both used.
PrincipalQuotientMultiplicationImage and QuotientBaseChangeIdeal were inspected as
possible component tools but are not imported by this reduction.

## Where the brief, the DAG or earlier work was wrong

The original DAG had no named dependency for the quotient/thickening comparison,
although its first step is non-elementary. This delivery isolates that exact step,
including the quotient functoriality used in the original third step.
The existing docstring's description of Stacks 0H3D and 0H3E as ordinary quotient-sheaf
results is inaccurate: these are an inverse-system lemma and example. The second reader
corrected the old module and theorem docstrings to cite the relevant affine quotient
and closed-immersion functoriality results, 01IH and 01QP, and degree-zero cohomology 01DZ.
Sources checked: https://stacks.math.columbia.edu/tag/01IH and
https://stacks.math.columbia.edu/tag/01QP, together with 01DZ.
LeanSearch returned Internal Server Error twice; the failed attempts are recorded
without an absence verdict, and LeanFinder, Loogle and direct source searches were used.
The unit route is retained. Edge cases checked mathematically: empty W and unit g give
zero quotient groups; g=0 gives the identity quotient. No global-section surjectivity,
Noetherian, regularity, torsion, or vanishing assumption was introduced.

## New nodes

new-principal-thickening-cokernel-sections:
lean/Sheaf/AlgebraicGeometry/Morphisms/PrincipalThickeningCokernelSections.lean,
AlgebraicGeometry.Scheme.principal_thickening_cokernel_sections.
It isolates the functorial quotient identification in the original proof's steps 1 and 3.
Its docstring and node give the affine quotient calculation, gluing argument, and
cancellation of the quotient epimorphism. It contains the sole new sorry.
No interface change record or forced adaptation is needed.

## Second reading by E1

1. Interface: compared the delivered item with the repository using diff and the
   declaration parser. Every original signature and both data bodies are unchanged;
   the parser reports no statement changes. Only proof imports, a private proved helper,
   the original theorem proof and corrected source comments differ. No change record is
   needed. The new comparison has a separate module and a verbatim Lean statement in its node.
2. Proof: both modules compile locally through lcompile.py. The sole delivered sorry is
   principal_thickening_cokernel_sections, exactly as reported. There are no forbidden
   declarations, kernel-check bypasses or holed definitions. The comparison equivalences
   are obtained and used within a proposition proof; no arbitrary witness is installed
   as a data definition. Scratch #print axioms checks and the delivery tool's all-declaration
   probe check the axiom boundary; sorryAx remains because the geometric comparison is open.
3. Split statement: checked the quotient-power definition, the direction of kappa and h,
   the canonical quotient map, and the H^0-to-sections conversion. The affine quotient
   calculation glues over arbitrary W and the quotient epimorphism proves functoriality.
   Empty W, g=0, unit g, n=0 and m=n give the expected zero or identity comparisons.
   The statement is true, imposes no new assumptions, and is strictly the geometric
   comparison part of the original argument: it asserts neither a boundary nor lifting.
   Independent LeanFinder, Loogle and source searches found affine components and
   closedImmersion_unit_quotient, not a duplicate. The latter still needs ideal-image,
   pullback-unit and H^0 transport and does not directly close the new statement.
4. Route and pruning: checked the explicit short exact complexes, exactness at H^0,
   and the Ext-class naturality proof. They use the existing LongExact API directly.
   Both new imports are proof-only and used; the original public imports are needed by
   the signatures. The original proof_deps is empty, so the pruning report is complete.
   sk-prop-input-spreading has empty realized statement/step arrays; no realized node
   is bypassed, and the original quotient, exactness and naturality route is retained.
5. Nodes: the existing node changes only proof, proof_deps and proof_origin. These
   match the reduction and its new geometric dependency. The new node has its source,
   complete proof steps, search records, origin, creation, blueprint, chapter, unit and
   exact Lean record. Its named sorry has the source and full proof in its docstring.

Changed in this reading: corrected the two inaccurate source comments in the original
module, added independent comparison searches to the new node, and wrote this review.
No mathematical statement, definition or proof required repair. This remains a
one-for-one decomposition with zero net hole reduction, not an axiom-free completion.
