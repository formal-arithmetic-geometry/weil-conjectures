## What changed

Completed `AlgebraicGeometry.SingleComplexBaseChange.openRestricted_tensor_chain_transport_pure`
from the strictly smaller coefficient-one germ calculation and a proved scalar compatibility
lemma. Its signature, geometric comparisons, definitions, and existing public import are unchanged.
Added proof imports of `OpenRestrictedTensorChainTransportPureOne` and `RestrictStalkInvSmul`.
The general proof rewrites a pure tensor as d times its coefficient-one tensor, applies the
linearity of both tensor-stalk maps and the output stalk map, and uses inverse restriction
semilinearity for the actual projection stalk map. The existing unused-let lint warnings in the
original signature are suppressed locally without changing those lets or the elaborated type.

The new `RestrictStalkInvSmul` module proves
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso_inv_smul`.
Its private forward germ arguments reuse the already proved private helpers of
`OpenSemilinearInputComplexIso` and `Modules.RestrictionStalkExtensionIso`; injectivity of the
forward additive comparison and both inverse identities give the inverse formula.
`FlatPullbackStalk` is imported privately for its module-on-stalk instance.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.SingleComplexBaseChange.openRestricted_tensor_chain_transport_pure`
(node `lem-pc-open-restricted-tensor-chain-transport-pure`).

Added one hole:
`AlgebraicGeometry.SingleComplexBaseChange.openRestricted_tensor_chain_transport_pure_one`
(node `lem-pc-open-restricted-tensor-chain-transport-pure-one`). It is exactly the
coefficient-one compatibility of the specified composition mates and section germs, and has a
complete natural-language proof in its docstring. The original module has no remaining sorry.
This is a decomposition with one hole closed and one hole added, not a net hole reduction.

Also proved `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso_inv_smul`
(node `lem-pc-restrict-stalk-inv-smul`) and all its private helpers, with no sorry.
All three sandbox modules compile through lcompile.py. The scalar lemma is checked from
Mathlib germ formulas and the existing module-on-stalk instance. The original theorem still
inherits sorryAx through the explicitly split coefficient-one lemma and existing dependencies.

## No longer needed

None. No original import is removed: the original public import is needed by the statement.
The original planned `lem-weil-pbc-module-stalk-pullback` remains needed by the coefficient-one
calculation. No unit statement or realized proof step is bypassed. Searches also found
pinned-open comparison theorems, but their schemes and specified comparison maps differ; these
modules were not imported and are not claimed as pruned from an existing dependency route.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped before extending the coefficient-one case to arbitrary coefficients,
left the original sorry, and provided an incomplete new-node record and proof description.
The semilinear extension is now a complete Lean proof. The scalar compatibility can be proved
by reusing existing forward restriction germ arguments; it does not require another hole.
The coefficient-one theorem remains the geometric part of the parent's documented argument,
not the parent statement renamed: its scalar is fixed to 1, and the general coefficient proof
is explicit Lean algebra. Edge cases are empty opens (no point), zero rings and modules, top
opens, and all integer degrees; no new hypothesis is required. LeanSearch was unavailable;
LeanFinder, Loogle, and source searches were performed and recorded. No interface adaptation,
target change, or hollow definition was made.

## New nodes

`lem-pc-open-restricted-tensor-chain-transport-pure-one` in
`OpenRestrictedTensorChainTransportPureOne.lean` records the remaining coefficient-one germ
and adjunction-unit calculation. Its statement excludes the arbitrary coefficient, and its
proof description spells out the specified tensor-stalk and restriction components.

`lem-pc-restrict-stalk-inv-smul` in `RestrictStalkInvSmul.lean` records the proved inverse
restriction scalar identity for every open immersion and module sheaf. It is a generic
stalk-map calculation independent of the base-change square and the tensor mates.

No change records: all existing signatures and definitions are preserved.

## Second reading by E3

1. **Statements and signatures.** Compared the delivered item module with the repository version. The target declaration and all existing definitions have byte-for-byte identical signatures; only proof imports, a local linter option, and the proof body changed. The two added declarations have explicit statements matching their DAG nodes.

2. **Proof and axioms.** Compiled all three sandbox modules with `lcompile.py --all`; compilation succeeds with no errors. The item theorem has no `sorry`; the coefficient-one theorem is the single documented split-off `sorry`, and the inverse restriction scalar theorem is fully proved. No definitions contain `sorry`, and no forbidden declarations were added.

3. **Truth and strength of split statements.** Checked the coefficient-one statement as the strict scalar-1 specialization used by the parent proof, and the inverse restriction statement as the general semilinearity identity for an open immersion. Both are needed, have complete proof descriptions and DAG nodes, and add no hypotheses or weakened conclusions. The coefficient-one split is a genuine lower geometric step rather than a restatement of the parent theorem.

4. **Route, imports, and pruning.** The proof follows the unit route through the coefficient-one germ calculation, then scalar extension using inverse restriction semilinearity. The added imports are proof-only imports; the original public import remains required by the statement. No old proof dependency is unused, so no pruning is claimed.

5. **DAG agreement.** Updated the item node's proof, proof dependencies, and proof origin to match the Lean proof while preserving its original creation and review metadata. Added nodes for both new public declarations with matching statements, sources, proof steps, unit, and module records. The unit's realized route is unchanged.

Changed: added the two proof-only modules and their DAG nodes, completed the parent proof by scalar reduction, proved inverse restriction semilinearity, and recorded this second reading.
