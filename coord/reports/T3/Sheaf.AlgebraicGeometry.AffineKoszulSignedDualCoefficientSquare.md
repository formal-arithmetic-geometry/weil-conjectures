## What changed

Replaced the sorry in `AlgebraicGeometry.affine_koszul_signed_dual_coefficient_square`
without changing its signature or its public imports. Added the proof-only import
`Sheaf.AlgebraicGeometry.AffineFiniteFreeCoefficientComparisons` and the exterior-power
basis API. The new comparison lemma concerns only individual Hom sheaves, with arbitrary
coefficient modules, and their pre/postcomposition identities.

Two proved private helpers assemble degree comparisons into signed complex isomorphisms
and prove the coefficient square. They handle negative degrees with zero objects, use
`extendXIso` and `extendMap_f` in nonnegative degrees, and prove the scalar conversion
from `-q.negOnePow` to `(-1)^(q+1)` for arbitrary coefficient modules. Keeping these
calculations generic avoids repeatedly unfolding the concrete Koszul construction.
The Koszul specialization supplies finite freeness from `Basis.exteriorPower` and the
recorded square-zero and coefficient reduction declarations.

The source pages read were Stacks Tags 01HV, lemma-spec-sheaves (4)-(5) and its
functoriality assertion, and 0BQZ, lemma-regular-immersion-ext, the displayed coefficient
Hom map. The local Stacks source files are absent on this machine; their web pages were
read directly. The scalar-only comparison modules were also read, but cannot supply the
quotient coefficient comparison or its naturality.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.affine_koszul_signed_dual_coefficient_square`
(node `new-g3-affine-koszul-signed-dual-coefficient-square`). Its complete Lean proof
assembles term isomorphisms, checks differential signs and extension boundaries, and
proves the coefficient equation by complex-morphism extensionality.

Added one hole, the entire proof of the public theorem
`AlgebraicGeometry.affine_finite_free_coefficient_comparisons`
(node `lem-sc-affine-finite-free-coefficient-comparisons`). It supplies only degreewise
finite-free affine Hom comparisons and pre/postcomposition naturality. It has no signed
differentials, extension by zero, complex isomorphisms, or quotient ideal. Consequently
this delivery is a decomposition: one hole closed, one strictly smaller hole added;
net hole reduction zero. Neither private helper has a sorry. No definitions were added
or changed, and no exported data are chosen from an unproved existence statement.

The remaining lemma is true for arbitrary coefficient modules: a finite free source
identifies Hom with a finite tuple of coefficient values. Empty bases, zero rings,
empty spectra, and zero coefficient modules all give the same tuple formulas. In the
specialization, n=0 and I=top require no extra assumptions. No regularity is used.

## No longer needed

No original import was removed and no module is claimed pruned. The original direct
proof edge to `lem-weil-pbc-spec-module-tilde-sections` now lies below the degreewise
comparison node and remains needed there. The scalar-only
`AffineFiniteFreeDualComplexComparison` and `AffineFiniteFreeDualNaturality` modules
are not imported: their proof pattern was used, but their scalar statements do not
solve coefficient naturality. They were not original dependencies, so this is not a
claim that the delivery prunes their modules from the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically correct. Its finite-basis localization step had
no declaration covering arbitrary coefficients and both naturality equations.
`affineBasisDualIso_naturality` concerns only the structure sheaf and precomposition;
there is no existing quotient-coefficient naturality interface to apply. The new node
isolates precisely that degreewise gap, while the extension and signed differential
parts of the original plan are now proved in Lean.

The blueprint ancestor tool returns None for the item because older created.item
records use module names. The new node records `lem-sc-finite-duality`, following the
explicit ancestor record of `new-j3-koszul-ext-coefficient-stalk-model`. The unit's
realized statement and step lists are empty; no unit route was bypassed. Blueprint
search for finite free Hom coefficients found no matching blueprint node.

## New nodes

`lem-sc-affine-finite-free-coefficient-comparisons`, in
`Sheaf.AlgebraicGeometry.AffineFiniteFreeCoefficientComparisons`, states simultaneous
termwise comparisons for every coefficient module, natural under the chain boundaries
and every coefficient map. Its source, complete finite-tuple proof, three actual search
kinds (LeanSearch unavailable), edge cases, and verbatim Lean signature are recorded.
No change records or forced adaptations are required.

## Second reading by T3

1. **Statements and accidental changes.** Compared both delivered modules with the
repository versions. The target theorem signature is byte-for-byte unchanged. The new
comparison theorem is a separate, strictly smaller statement with arbitrary coefficients,
degreewise finite-free terms, and exactly the two naturality equations used by the target.
No definition or existing public declaration was altered.

2. **Compilation and axioms.** Compiled both sandbox modules with `lcompile.py --all`;
both compile without errors or warnings. The target proof has no `sorry`, `axiom`,
`unsafe`, `opaque`, `extern`, or `implemented_by`. The only remaining `sorry` is the
named comparison theorem, and it is documented and represented by its DAG node.

3. **Truth and necessity of the split.** Checked the finite-basis tuple argument and
the pre/postcomposition formulas, including empty bases, zero rings, empty charts, and
zero coefficient modules. The split theorem supplies precisely the missing affine
coefficient comparison and its naturality; it does not restate the target or include
signed differentials, extensions, or quotient-specific conclusions.

4. **Shortest route and pruning.** The proof uses the exterior-power finite-free basis,
the new degreewise comparison, and the existing signed-complex and coefficient-map
declarations. The scalar-only comparison modules are unnecessary for this arbitrary-
coefficient argument and were not imported. No original import was removed and no
target-reachable module was incorrectly marked pruned.

5. **DAG and unit route.** Updated the target node's proof, dependencies, and origin to
match the Lean route; the new node contains its source, proof steps, searches, and
verbatim Lean declaration. The unit's realized statement and step lists are empty, so
the proof does not bypass a realized unit step. The target proof is a decomposition:
one target hole is closed and one strictly smaller comparison hole remains.

Changed only the target proof/imports, added the comparison module and node, updated the
target node route, and recorded this second reading.
