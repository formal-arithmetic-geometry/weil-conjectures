## What changed

Proved `cyclicRepresentableCohomologyMap_naturality` by composing two strictly
lower naturality statements: free-representable Ext comparison naturality and
constant cyclic coefficient pullback compatibility. The missing compiled
prerequisite was copied into the sandbox solely to compile the delivery.

## Proved and sorry left

The target theorem `cyclicRepresentableCohomologyMap_naturality` is proved.
The strictly lower declarations `abelianRepresentableCohomologyMap_naturality`
and `cyclicCoefficientPullbackCompatibility` remain `sorry` and are split into
new nodes for parallel proof.

## No longer needed

The exploratory `AbelianRepresentableGeneratorNaturality` module and its draft
node are no longer needed. The scratchpad calculations and exploratory imports
are not part of the proof.

## Where the brief, the DAG or earlier work was wrong

The earlier BLOCKED result was caused by the shared compiled snapshot lacking
`CyclicDerivedHomComparisonMap.olean`; compiling that unchanged prerequisite in
the sandbox made the item compile. The DAG did not expose the two naturality
components as separate nodes, so they are added here.

## New nodes

`lem-sbc-abelian-representable-cohomology-map-naturality` and
`lem-sbc-cyclic-coefficient-pullback-compatibility`.

## Earlier second reading (a previous round; superseded)

The target proof and both decomposed interfaces compile in the sandbox; the two lower theorem proofs remain explicit named holes for the next workers.

## Second reading by S2

1. Compared the delivered target module with the repository version. The theorem signature and all existing declarations are unchanged; only the target proof and proof-only imports were added, alongside the two explicitly split lower modules.
2. Compiled all four sandbox modules with `lcompile.py --all`; compilation succeeds with no errors. The target has no `sorry`, and the only remaining holes are the two named lower theorems, each documented and represented by a DAG node. No forbidden declarations or hollow definitions are present.
3. Checked the split statements against their uses and searched the repository for duplicates. Both are strictly smaller naturality/compatibility interfaces required by the target proof, have source and proof documentation, and are not existing library declarations.
4. Checked the proof route and pruning. The target proof uses exactly the two lower naturality components and definitional unfolding; no exploratory imports or modules are needed. The unit route remains represented by the target node and its lower split nodes.
5. Checked DAG and report consistency. The target node now records the actual proof steps, dependencies, and origin; the two new nodes match their Lean declarations and report entries.

Changed the target proof and added plain proof-only imports for the two lower components. Added the two documented split theorem modules and their DAG nodes, and updated the target node's proof metadata.
