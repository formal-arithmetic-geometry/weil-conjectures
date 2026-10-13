## What changed

Replaced the sole proof hole in
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoCoherentModuleExtension` with a complete
Lean proof from the new affine lemma
`AlgebraicGeometry.Scheme.affine_depth_two_pushforward_hull`.
The original theorem signature and all original public imports are unchanged.
Added two proof-only imports: the new affine module and the proved source-library
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`.

The extension is the actual, already defined pushforward `B.toModule`.
Quasi-coherence follows by giving presentations on every affine chart.
Finite affine sections follow from
`finite_sections_of_finite_sections_restrict_fromSpec`.
For a boundary point the proof selects an affine chart, transfers finite generation
through its semilinear stalk isomorphism, and transports regular sequences to obtain
the depth bound. The restriction isomorphism is the identity.
Three private helpers are fully proved: `depth_le_of_semilinear_equiv`,
`stalkMap_appIso_inv_germ`, and `restrict_stalk_smul`.
In particular, there is no unproved stalk-transport theorem and no data chosen
from an unproved existence theorem.

The affine computation is isolated in the new module
`Sheaf.AlgebraicGeometry.Morphisms.AffineDepthTwoPushforwardHull`, with a public
statement, complete sourced proof in words, and a matching DAG node.
The existing node's proof and dependencies now follow the Lean argument.
The second reading added the new affine module's three private planned-dependency
imports: `WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward`,
`Sheaf.AlgebraicGeometry.ModuleFinitePresentationExtension`, and
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsAlgebraComparison`.
Both modules compile cleanly with `lcompile.py --all`.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.exists_depth_two_coherent_module_extension`
(node `lem-sbc-depth-two-coherent-module-extension`).
There are no sorries left in the item's module.

Added 1 hole, exactly the whole proof of the public theorem
`AlgebraicGeometry.Scheme.affine_depth_two_pushforward_hull`
(node `lem-sbc-affine-depth-two-pushforward-hull`).
It asks only for quasi-coherence, finite global sections and boundary depth on
an individual affine chart, rather than a global extension and its gluing.
This is a decomposition, with one hole closed and one added (declaration-level net zero), not a
sorry-free proof of the extension theorem or of its full dependency closure.

The affine lemma was checked mathematically for empty charts, empty U, U equal
to the whole scheme, the zero finite etale algebra, and nonintegral Noetherian
charts. Empty-chart assertions are vacuous, the zero module has infinite depth,
and the local kernel calculation uses regularity of the chosen pair rather
than an assumption that the base ring is a domain.

## No longer needed

No imports were removed relative to the original module, and no existing DAG
node is claimed to leave the targets' closure.

Explicit global overlap isomorphisms, cocycle verification and object descent
are unnecessary in this proof: the chosen object is the canonical pushforward.
Consequently this proof needs no import of
`Sheaf.Topology.GlueSheavesOfModules`, `Sheaf.Topology.ModuleObjectOpenDescent`,
or `WeilConjectures.AlgebraicGeometry.Modules.DescentEffective`.
These were prospective routes, not imports removed from the baseline.
Hartogs remains necessary in the affine lemma's proof plan and is not pruned.
The integral reflexive-extension results of Tags 0EBI and 0EBJ are replaced in
that plan by coherent extension (0G41), the direct kernel calculation, and 0E9I.

## Where the brief, the DAG or earlier work was wrong

The original node has a single non-elementary step with no named proof
dependencies. It does not already provide the double-dual construction,
the depth computation, or the global gluing theorem as applicable Lean statements.
The new node isolates the genuinely affine computation, while the present delivery
proves the local-to-global part and all stalk compatibility in Lean.

The cited Stacks Tags 0EBI and 0EBJ explicitly assume an integral scheme; the item
does not. The statement need not change: the finite-free-kernel regular-pair
calculation written in the docstring works without integrality. The new lemma
makes this distinction explicit and cites Tag 0G41(2) for the coherent extension
step and Tag 0E9I for Hartogs. Read source pages:
[0EY6](https://stacks.math.columbia.edu/tag/0EY6),
[0G41](https://stacks.math.columbia.edu/tag/0G41),
[0EBI](https://stacks.math.columbia.edu/tag/0EBI),
[0EBJ](https://stacks.math.columbia.edu/tag/0EBJ), and
[0E9I](https://stacks.math.columbia.edu/tag/0E9I).
The unit's depth-two extension route is kept.

## New nodes

`lem-sbc-affine-depth-two-pushforward-hull`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-affine-depth-two-pushforward-hull.json`,
states the affine coherent-hull computation for the actual finite etale
pushforward. Its Lean module is
`Sheaf.AlgebraicGeometry.Morphisms.AffineDepthTwoPushforwardHull`.
Its proof plan records coherent extension, finite-flat pushforward and Hartogs
through their existing nodes, and spells out the double-dual kernel argument.
No definition, existing public statement, or other module interface was changed;
no change record or forced adaptation is needed.


## Second reading by V1

1. **Interfaces: pass.** Compared the complete item module with the repository by
   `diff` and checked its declaration table. The existing theorem signature and
   visibility are byte-for-byte unchanged. All original public imports and the
   existing docstrings are unchanged. There is no definition or statement change,
   no forced adaptation, and no change record is required.
2. **Proof and axioms: pass as a decomposition.** Both delivered modules compile
   with `lcompile.py --all`. Read every proof, including the regular-sequence
   transport and the common-neighbourhood germ calculation for scalar compatibility.
   A scratch copy with `#print axioms` shows only `propext`, `Classical.choice` and
   `Quot.sound` for all three private helpers. The existing extension theorem and
   the new affine theorem additionally use `sorryAx`, as reported. The only literal
   hole in the delivery is the whole named affine theorem. There is no forbidden
   declaration, hollow definition, or arbitrary data obtained from an open
   existence theorem: the global witness is the constructed actual pushforward.
3. **Split statement: pass.** Independently checked the affine theorem against
   Stacks 0EY6, 0G41(2), and 0E9I. Its double-dual construction is finite over a
   Noetherian affine ring, agrees with the locally free module on the open, and
   is a kernel between finite free modules. A regular pair in the base therefore
   remains regular on each nonzero boundary stalk; Nakayama supplies properness.
   Hartogs identifies this coherent sheaf with the displayed actual pushforward.
   This works for nonintegral rings. Checked empty charts, empty open, full open,
   and zero algebra: the zero module has infinite depth and empty boundary
   conditions are vacuous. The lemma fixes one affine chart and contains no
   global existence or gluing assertion, so it is a strictly local part of the
   argument rather than a renamed restatement. Its sourced docstring and matching
   node are complete. Independent `msearch.py` searches used “direct image of a
   finite locally free module across an open immersion”, `IsLocalRing.depth`, and
   `doubleDual|double_dual|depth.*kernel|kernel.*depth`; `rg` checked both library
   roots and the local Mathlib sources. No exact existing affine hull was found.
   Loogle's newer Mathlib depth lemmas use a different ModuleCat/Ext definition;
   this project uses `Sheaf.RingTheory.Depth`. No few-minute closure of the affine
   calculation was available.
4. **Route and pruning: pass after import repair.** The shortest available route
   is the actual pushforward plus affine descent; the stalk transport is already
   fully proved. Both proof-only imports in the item are used. Its old node had
   empty `proof_deps`, so there is no omitted dependency to list as pruned. No
   original module import was removed. The unit record
   `dag/units/sk-prop-input-spreading.json` was read and left unchanged: its depth-two
   extension step is retained, and no higher unit route is bypassed. The new
   module's public Tilde import was tested against a narrower quasi-coherence
   import: the narrower import fails because the signature needs the module
   action on global sections of a Spec module supplied by Tilde. Kept Tilde
   public for that statement dependency. Added the three modules of the planned
   proof dependencies as private imports under the standing brief's
   dependency-import rule. These imports prepare the remaining affine proof; they do not assert
   that its hole is closed. No module is claimed pruned from the target closure.
5. **Nodes: pass.** Both `lean.statement` records equal the theorem signatures in
   the delivered Lean. The existing node's only changed fields are its proof,
   proof dependencies and proof origin. Its argument uses the new affine node,
   the source-library affine presentation/section criteria, and the proved local
   helpers exactly as described. The new node has its source, proof steps,
   dependency union, origin, three search records, creation/blueprint data,
   chapter, unit, status and Lean record. Its three planned dependencies have
   existing declarations and are now privately imported by its module.

Second-reading changes: added the three private planned-dependency imports
to the new affine module and
clarified that the report's net-zero count is at the declaration level; the
pinned sorry ledger determines closure progress. Added this independent review.
No proof body or existing signature was rewritten. The result remains one
original hole closed and one strictly affine hole added, a decomposition.
