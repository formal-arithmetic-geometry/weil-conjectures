## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.picard_h1_product_spanning` with a proof
from `Modules.picard_kunneth_qcoh` and the new individual-cup comparison theorem.
Properness supplies compactness; the proved unit quasi-coherence instance supplies
Kunneth's coefficient hypotheses. Arithmetic splits every degree-one index into
(1,0) or (0,1). Local induction steps use tensor-product and direct-sum
induction to combine the individual generator formulas. Surjectivity of Kunneth and
the additive comparison then gives the requested factor classes.

Added `Sheaf.AlgebraicGeometry.PicardExternalCupScalarComparison`, with one theorem
isolating unit-coefficient comparison and scalar normalization of individual external
cup products. It has no properness hypotheses and no assertion that cups span. The
main theorem still uses the Kunneth equivalence essentially; the new theorem is not
a renamed spanning theorem. All existing signatures and public imports are unchanged. A local irreducibility
attribute on scalarCohomology avoids unnecessary unfolding during elaboration.
The repair proves explicitly that scalarMap at the top open equals the global-sections
structure map: the restriction map at the top open is the identity. Explicit additivity
calculations avoid rewriting inside the definitions of derived cohomology maps.
Updated the parent DAG proof and dependencies and added the new node. Added a change
record for the locally scoped elaboration commands required by the preflight.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.picard_h1_product_spanning`
(node `lem-sc-picard-h1-product-spanning`). No sorry remains in the assigned module.
The zero, additive, pure-tensor, and induction steps are proved without sorry.

Added and left: `AlgebraicGeometry.Scheme.picard_external_cup_scalar_comparison`
(node `lem-sc-picard-external-cup-scalar-comparison`). This is a decomposition:
one upper hole closed, one compatibility hole added, net zero new-hole reduction.
The existing `Modules.picard_kunneth_qcoh` remains an imported dependency. Its
assembly proof is complete in the current library, while its isomorphism and
functoriality dependencies still contain sorry; this delivery does not change them.

## No longer needed

Removed the direct proof import `Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural`
from the assigned module. Its use is localized in the new comparison module, so it
remains transitively needed; its node is not pruned. The parent's direct dependency
`lem-sc-module-abelian-zariski-cohomology` is replaced by the new comparison node,
which depends on that comparison. The field-linear operations and structure-sheaf
pullback definitions remain in the statement/definition closure and are used by the
new comparison, rather than being independent proof steps of the spanning argument.
Also removed the direct import `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`
from the assigned module: Kunneth and the new comparison already publicly import it.
It remains transitively needed, and its definition node is not pruned.
No whole module or mathematical dependency is pruned. Kunneth and ProperBasic stay.
No slice, rational-point, or slice-injectivity lemma is imported or used.

## Where the brief, the DAG or earlier work was wrong

The existing natural module/abelian comparison is natural in coefficient morphisms
on a fixed scheme; its Lean statement does not include change-of-scheme pullbacks,
cup products, or degree-zero scalar normalization. The parent plan's step 3 therefore
needs a compatibility theorem, not merely an application of that natural isomorphism.
This delivery isolates exactly that step. No mathematical statement was changed.

The new statement was checked on affine factors (all degree-one classes vanish,
so both equations are zero), on zero inputs and zero scalars, and with one affine
factor (the nonzero degree-one equation is scalar multiplication). Empty factors
cannot satisfy the bijective map from a nontrivial field to their zero section ring.
There is no need for rational points or properness in the compatibility theorem;
those are used only for the separate Kunneth spanning argument.

Checked the Stacks pages for [0BED](https://stacks.math.columbia.edu/tag/0BED)
(the pullback/cup maps), [03FD](https://stacks.math.columbia.edu/tag/03FD)
(module versus abelian cohomology), and [01F7](https://stacks.math.columbia.edu/tag/01F7)
(resolution construction of pullback). The cited local Stacks source files are absent
on this machine, so these primary-source pages supplied the source text. The scalar-normalization
resolution details are written explicitly in the new docstring and node as an agent
argument. Blueprint searches for cup product and 0BED found no duplicate statement.
The cube unit's route through the degree-one Kunneth argument is retained.


The earlier sandbox proof did not compile: it passed hX and hY where scalarMap
bijectivity was expected. It also spent excessive elaboration time rewriting the
additivity step. Both faults are repaired; no timeout limit or tool was changed.

## New nodes

`lem-sc-picard-external-cup-scalar-comparison`, in
`dag/nodes/sec-abelian-varieties/`, records the additive comparisons for the factor
unit modules and the product external unit coefficients, the degree-zero scalar
coordinates, and the two scalar-normalization formulas. Its proof constructs the
comparisons from the common section complexes, identifies external coefficients by
tensor unit isomorphisms, and computes cup with a scalar degree-zero section.
The prior worker recorded LeanFinder, Loogle, grep, and a failed LeanSearch attempt.
This repair repeated the parent LeanFinder, Loogle, and grep searches and searched both
library roots for a scalar cup comparison; no shorter spanning statement was found.
The node's Lean signature was corrected to match its actual explicit-morphism binders.
The conservative command-change check requires
`coord/changes/picard-h1-product-spanning-elaboration.md`; it documents the preserved
signature and the scope of the elaboration commands. No forced adaptations are needed.

## Second reading by U3

1. Compared both delivered modules with the repository versions. The existing theorem signature is byte-for-byte unchanged; the added comparison module is a genuinely new declaration. Verdict: pass.
2. Compiled the comparison module and the spanning module with `lcompile.py`; both compile without warnings after the proof repair. Sorries occur only in the explicitly split comparison theorem, with no forbidden declarations or hollow definitions. `#print axioms` for the spanning theorem reports only the imported split theorem's `sorryAx` together with permitted axioms. Verdict: pass.
3. Checked the new comparison statement against zero and affine-factor cases and verified it is strictly a compatibility statement, not a restatement of spanning. Its node, docstring, and signature agree. Verdict: pass.
4. Reviewed the proof from Kunneth through tensor and direct-sum induction and confirmed the shortest available imported route is used; removed no further imports. The unit's Kunneth route remains intact. Verdict: pass.
5. Checked the parent and new DAG nodes, proof dependencies, proof origins, and realized unit route against the Lean declarations. Verdict: pass.

Changed the additive closure step to an explicit calculation using `map_add` and `abel`, which reduced elaboration below the 60-second limit. Updated the elaboration change record to reflect the final local options and attributes.
