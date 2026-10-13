## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_acyclic`
by a compiled proof using the projection direct images, the existing qcqs direct-sum
cohomology bijection, and the existing additive Leray edge. The target signature and
all existing public imports are unchanged. Added proof imports of
`PicardExternalCoefficientsDirectImages`, `QcqsCohomologyDirectSum`,
`LerayDegenerateSections`, the source-library right-derived additivity instance,
and Mathlib's additive-group zero-object API.

The new direct-image theorem isolates the local geometric calculation of steps 1-2
and the basis decomposition at the start of step 3. It assumes only acyclicity of F;
it does not assume compactness or affine diagonal for Y, or acyclicity of G. Its
conclusion concerns sheaves on Y, not the cohomology of the product. The parent now
proves all of the direct-sum acyclicity and Leray glue in Lean.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_acyclic`
(node `lem-sc-picard-external-coefficients-acyclic`), the sole original hole.
No sorry remains in the item's module.

Added: `AlgebraicGeometry.Scheme.Modules.picardExternalCupCoefficients_directImages`
(node `lem-sc-picard-external-coefficients-direct-images`), one named theorem with
`:= by sorry` in its own module. This is a decomposition, not a net decrease in holes
or an axiom-free completion of the theorem. No data is selected for a definition.

Both sandbox modules compile with lcompile.py. The positive cohomology columns of
Leray are closed using zero-preservation, and the degree-zero column is closed using
surjectivity of the canonical direct-sum comparison and hG. The final additive
isomorphism gives a subsingleton module, hence IsZero.

## No longer needed

None globally, and no existing imports removed. The affine product, pullback-section,
tensor-section, Cech comparison and higher-direct-image presheaf nodes are not used
directly in the parent Lean proof, but remain needed in the new geometric node.
The parent's removed direct proof dependencies are
`lem-sc-cech-comparison-map-iso-affine`,
`lem-sc-picard-affine-diagonal-intersections`,
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-higher-direct-image-presheaf`,
`lem-weil-pbc-module-pullback-affine-sections`, and
`lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`.
Each remains in the new geometric node's proof plan; none is globally pruned.
For quasi-separatedness of Y the parent uses Mathlib instances and
`quasiSeparatedSpace_of_quasiSeparated`, not the affine-intersection lemma.
The qcqs direct-sum and Leray nodes remain directly used by the parent. Moving those
local calculations below the new node is not pruning them.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature change was found. The second reading corrected
the parent DAG's direct citation of the affine-intersection lemma: the compiled
quasi-separatedness argument uses Mathlib instead. The stated dependency interfaces
provide the local affine ingredients, not the combined calculation of R^q pr2_* E
or its degree-zero coproduct cofan. That geometric combination is the remaining hole;
merely importing the existing ingredients does not close it by a short application.

Read the source at https://stacks.math.columbia.edu/tag/0BED, especially the final
acyclic paragraph and its derived-direct-image display. The local literature source
file was absent on this machine. The unit route is retained: the parent's original
Cech/direct-image/direct-sum/Leray argument is unchanged, with its local portion made
a separate item. The unit record has no realized statement or steps to bypass.

Edge cases checked for the new statement: zero F or G, empty X or Y, and an infinite
basis of Gamma(X,F). The coproduct is in module sheaves, not a claim that sections on
arbitrary opens equal presheaf direct sums. Empty bases produce a zero coproduct.
On affine X, the statement is the usual section tensor formula with affine vanishing.
The lack of any acyclicity hypothesis on G prevents this lemma from being a renamed
version of the parent's conclusion.

Mathlib searches ran through msearch.py: LeanSearch was unavailable (HTTP internal
server error); LeanFinder returned generic Tor/flatness results, and Loogle returned
no result for the zero-object query. Mathlib grep and searches in both library roots
found no geometric direct-image theorem. Blueprint searches for 0BED and kunneth,
and the DAG external/direct-image searches found no duplicate of the new statement.

## New nodes

`lem-sc-picard-external-coefficients-direct-images`, in
`dag/nodes/sec-abelian-varieties/`, states positive-direct-image vanishing and the
zeroth-direct-image coproduct for an acyclic first factor. Its module is
`Sheaf.AlgebraicGeometry.PicardExternalCoefficientsDirectImages`. Its proof plan
retains the original local affine Cech ingredients and explicitly records field
flat tensor exactness, the finite cover, and the vector-space basis. The parent node
now records the three compiled steps combining this result with the existing
cohomology and Leray interfaces. There are no change records or forced adaptations.


## Second reading by K2

1. Compared the existing module with the repository using diff. Its only changes
are five plain proof imports and the replacement proof; the existing theorem
signature, public imports, docstrings, visibility, and coefficient definition are
byte for byte unchanged. There are no change records or adapted modules. PASS.

2. Compiled both delivered modules locally in import order. The sole remaining
sorry is the named `picardExternalCupCoefficients_directImages` theorem declared
in the report; no definition or private helper contains a hole, and there are no
forbidden declarations or compiler bypasses. Scratch-copy `#print axioms` checks
were run for both the parent and new theorem. Only standard axioms and `sorryAx`
from still-open statements occur; this is a decomposition, not an axiom-free
completion. PASS.

3. Read the new direct-image statement and its complete docstring proof against
https://stacks.math.columbia.edu/tag/0BED, including the affine-local calculation
and derived-direct-image display. The calculation needs hF but no hG: take X =
Spec k and F = O_X to get R^0 pr2_* E = G and zero higher direct images even when
G has positive cohomology. Thus the new statement is a local geometric part of
the argument, not a restatement of product acyclicity. Empty X gives the empty
coproduct; empty Y and either zero coefficient give zero objects. Infinite bases
are handled by coproducts of module sheaves and sheafification, not an incorrect
claim about sections on arbitrary opens. Gamma(X,F) is a module in universe w,
so its basis can be indexed in Type w. There is no arbitrary witness used as
definition data. Independent LeanFinder, Loogle, and grep searches used
pushforward/tensor and external-product wording; no matching theorem was found.
Read the related Kunneth modules and searched both project and upstream roots;
none gives this local result without passing back through this item. The local
geometric calculation cannot be closed by a short application of the available
affine ingredient statements. PASS.

4. Read the parent proof from its conclusion downward: the additive Leray edge
reduces to vanishing higher direct images and acyclicity of their degree-zero
coproduct; the latter follows from the existing qcqs cohomology comparison and
hG. Zero-preservation closes all other columns. The coproduct witnesses are used
only in this proof of a proposition. The existing public imports are needed by
the unchanged signature; the added parent imports supply proof APIs. Removed a
redundant Products import from the new module. Retained PQFCohomology after a
narrower-import experiment failed to synthesize injective resolutions. Listed
all removed direct dependencies under No longer needed; no module is globally
pruned. The unit sk-prop-av-cube and its realized fields are unchanged, and the
original local Cech/direct-image/direct-sum/Leray route is retained. PASS.

5. Compared the parent node with the original, checked the new node's required
fields, verbatim Lean statement, source, proof steps and union of dependencies.
Corrected the parent node to remove the affine-intersection lemma as a direct
proof dependency and to name the actual Mathlib quasi-separatedness argument.
The affine-intersection dependency remains in the new local geometric node.
Both nodes otherwise describe exactly the compiled reduction and the remaining
geometric proof plan. PASS.

Changes in this second reading: removed the redundant Products import in the new
module, corrected the parent DAG dependency, and expanded the pruning report.
No mathematical statement, definition, or proof body was changed.
