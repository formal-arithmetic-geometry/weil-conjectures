## What changed

The existing declaration `AlgebraicGeometry.Scheme.picard_affine_structure_projective_model`
keeps its signature byte for byte. Its proof now obtains a bounded finite-projective complex
with an actual representing isomorphism, then uses that isomorphism to establish the universal
low-homology clauses. Two new proof-only imports provide these separate steps.

The first worker's unpublished `PicardAffineStructureProjectiveModelCore` and
`PicardAffineStructureProjectiveModelComparison` modules and nodes were removed. The comparison
was false, and the core did not retain any relationship to the geometric image.
They are replaced by `PicardAffineStructureProjectiveRepresentation` and
`PicardAffineStructureProjectiveHomology`. There are no changes to existing definitions,
statements, visibility, or public imports, and no change record is needed.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Scheme.picard_affine_structure_projective_model`.
No `sorry` remains in the item module. This is a decomposition, not a completed proof:
the target's axioms still include `sorryAx`.

New holes added (two):
- `AlgebraicGeometry.Scheme.picard_affine_structure_projective_representation`, node
  `lem-sc-picard-affine-structure-projective-representation`;
- `AlgebraicGeometry.Scheme.picard_affine_structure_projective_homology`, node
  `lem-sc-picard-affine-structure-projective-homology`.

Each hole is an entire named public theorem in its own module, with its source and complete
natural-language argument in the docstring. No data is defined by choosing an unproved witness.
The existing existential proof uses `obtain` locally to prove another proposition.
There is one original hole and two added holes: the delivery's raw net is minus one;
no positive ledger progress or complete axiom-free target proof is claimed.

## No longer needed

No original imports or library modules are pruned. The unpublished Core and Comparison modules
and their nodes are removed from the proposed delivery, not counted as library pruning.

All four old direct `proof_deps` are removed from the item's direct list:
`lem-pc-affine-localized-derived-sheafification`, `lem-pc-perfect-affine-bounded-projective`,
`lem-pc-rf-perfect-base-change`, and `lem-sc-flat-derived-structure-unit`.
They remain needed transitively in the two new nodes' sourced arguments, so none is declared
unreachable or pruned. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first worker's comparison theorem tried to derive representation from bounded finite
projective terms and universal negative/H0 homology conditions. This is false even for the
identity of Spec K over a field K, with W=Spec K, U=top and M=O. A complex with K in degree
zero and another K in degree one, and all differentials zero, satisfies those conditions
after every extension K→B, but has nonzero H1. The geometric image for the identity has H1=0,
so it cannot be isomorphic to that complex. The universal adjunction unit is an isomorphism
in this example. The corrected homology statement takes representation as a hypothesis,
which excludes this counterexample.

The first worker's new nodes also lacked proof steps, complete docstring proofs and verbatim
Lean signatures, and copied searches from a different item. All of these faults are repaired.

## New nodes

`lem-sc-picard-affine-structure-projective-representation` states only bounded finite-projective
representation of the restricted image; it omits the universal H0 hypothesis and conclusions.
`lem-sc-picard-affine-structure-projective-homology` deduces only the universal negative/H0
clauses for a given representing bounded projective complex. Its finiteness is not needed.
Neither is a renamed restatement of the item, and they are assembled using the same witness P.

Independent searches via msearch.py used LeanSearch (unavailable: Internal Server Error),
LeanFinder (general K-projective and pushforward tools), Loogle (no extendScalars/homology hit)
and grep (rightDerivedZeroIsoSelf, but no affine scalar-extension comparison). The recorded
searches are in searches.jsonl and reproduced in the new nodes. Repository searches and reading
checked perfect_derivedDirectImage_baseChange, perfect_iff_affine_bounded_projective,
affine_localized_derived_sheafification, affine_open_perfect_source_model and
exists_flat_derived_structure_unit. These supply the ingredients in the new nodes' arguments,
but none directly states the geometric open-restriction representation or the homology
comparison for the explicit scalar-extended affine model. No source-library duplicate was found.

Sources checked: [0BF2](https://stacks.math.columbia.edu/tag/0BF2),
[0B91](https://stacks.math.columbia.edu/tag/0B91),
[08EB](https://stacks.math.columbia.edu/tag/08EB), and
[06Z0](https://stacks.math.columbia.edu/tag/06Z0). No change records.

## Second reading by E1

1. Compared the existing module with the repository using diff. Its sole existing declaration's
   signature is byte for byte unchanged; only two plain proof imports and its proof changed.
   No definitions, public imports or visibility were changed. Verdict: pass after repair.
2. Compiled both the initial proposed set and the repaired three-module set locally through
   lcompile.py. The repaired set compiles without errors or warnings. Exactly the two named
   theorems above retain sorry; there are no axioms, unsafe/opaque declarations, extern hooks,
   implemented_by attributes or definitions with sorry. Axiom inspection is recorded below.
3. Tested the initial comparison on the identity of a field spectrum and found the explicit
   extra-H1 counterexample above. Replaced it with the representation-first reduction. The two
   new statements are true: representation follows from proper relatively flat perfection and
   the affine perfect criterion; homology follows from actual representation, K-flat scalar
   extension, arbitrary base change and the ordinary structure unit. Also checked empty U,
   zero rings and identity maps. Each now has a sourced docstring proof, a matching complete
   node and independent Mathlib searches. Verdict: false initial split refused; repaired split
   passes as a decomposition with two genuinely smaller arguments still open.
4. Read the existing four proof-dependency interfaces and the generic affine source-model
   theorem for a shorter route. The missing work is exact open-image transport and the explicit
   affine scalar-extension/homology dictionary; it cannot be replaced by bounds and H0 alone.
   The two steps remain on the original perfection/affine-model/base-change route. The unit
   sk-prop-av-cube and its realized record were read and left unchanged. Every removed direct
   dependency is listed above; no library pruning is claimed. Verdict: pass.
5. The original node now names exactly the two declarations applied in Lean. New nodes have
   self-contained statements, verbatim Lean signatures, proof steps with their dependency union,
   sources, search records, creation/provenance fields, and the same chapter/unit. Verdict: pass.

Changes by second reading: removed the false comparison and disconnected core; installed a
representation-first decomposition with explicit representation as the homology hypothesis;
completed docstrings and DAG records; replaced inaccurate progress and pruning claims.

Axiom inspection of a scratch copy with #print axioms verified all three declarations:
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, with no other axioms.
The scratch copy was removed. All three modules compiled cleanly after the repair.
