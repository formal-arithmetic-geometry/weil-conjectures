## What changed

Proved `TopCat.irreducible_constant_sections` in
`Sheaf.Topology.IrreducibleConstantSections` with its signature unchanged. Added the
proof-only import `Sheaf.Topology.ConstantSheafLocallyConstantComparison`.
The proof chooses a point of each nonempty open, constructs an additive evaluation
equivalence with inverse the constant function, and composes it with the comparison.
It proves the restriction equation by function extensionality, comparison naturality,
and constancy on the larger preconnected open. Choice of points has no effect on the
restriction identity. No definitions or existing public interfaces were changed.

The missing step of the plan is the additive, natural comparison between abstract
constant sheafification and locally constant maps. The existing
`TopCat.locallyConstantMapsPresheaf_isSheaf` says only that the set-valued presheaf is
a sheaf; it supplies neither the additive comparison nor the universal-property
factorization. Isolated this step as a generic theorem for arbitrary topological
spaces and all opens, rather than assuming the original irreducible-space conclusion.
Updated the original DAG node to describe the proof actually written.

Local compilation of both modules passes without errors or warnings.
The final dry run also checks compilation and the declaration/axiom probes.

## Proved and sorry left

Proved the original module's sole sorry:
`TopCat.irreducible_constant_sections`
(node `lem-sc-irreducible-constant-sections`), from the new comparison theorem.
The original module contains no remaining sorry.

One sorry was split off:
`TopCat.constantSheaf_locallyConstant_comparison`
(node `lem-sc-constant-sheaf-locally-constant-comparison`, module
`Sheaf.Topology.ConstantSheafLocallyConstantComparison`). Its whole proof is `by sorry`;
its docstring and node give the gluing and sheafification universal-property argument.
This is step 2 of the original four-step proof. Steps 1, 3, and 4 are now Lean proofs.
There are no other added or retained sorries in the delivery.

Edge cases: the comparison includes empty opens, where both section groups are
trivial; disconnected spaces, where it compares with locally constant functions rather
than with A; and zero coefficients, where both groups are trivial. The main proof
requires a point only when the existing nonemptiness hypothesis supplies one.
It works with a singleton space and with inclusions V = U. The coefficient and space
universes, as well as the original `HasWeakSheafify` assumption, are unchanged.
The comparison uses `AddEquiv` between possibly different universes rather than
requiring the locally constant function type to belong to `AddCommGrpCat.{v}`.

## No longer needed

No existing import was removed. No node or module from the original argument is
pruned globally: the locally constant sheaf lemma and the constant-sheaf definition
remain dependencies of the new comparison node. The removed direct proof dependencies are
`lem-weil-pbc-locally-constant-maps-sheaf` and `def-weil-pbc-constant-sheaf`;
both now occur below the comparison. Neither is globally pruned. The connectedness and locally
constant-map nodes remain direct dependencies, realized by their Mathlib matches.
The unit route is preserved; `sk-thm-curveestimate.realized` does not designate this
node as a unit statement or step, and its original four-step route is retained.

## Where the brief, the DAG or earlier work was wrong

The DAG's step 2 contains more than the existing stated dependencies provide. Its
set-valued sheaf lemma alone does not state the comparison of the constant abelian
sheaf with locally constant maps. The new theorem exposes that missing bridge.
The source and the original statement were not changed.

The cited literature files are absent from this read-only clone. Read the primary
source online: [Definition 006W](https://stacks.math.columbia.edu/tag/006W) defines the
constant sheaf by locally constant maps, and
[Example 0081](https://stacks.math.columbia.edu/tag/0081) identifies it with constant
presheaf sheafification. Their expanded universal-property proof was already given
in the original node; it is now carried by the new comparison node and docstring.

Searches: LeanFinder returned constant-sheaf definitions, the sheaf of all functions,
and condensed locally constant presheaves, but no topological comparison. Loogle
`LocallyConstant, ConnectedSpace` returned no hits. LeanSearch returned Internal
Server Error and is recorded as unavailable. Searches across all of `lean/Sheaf`,
`lean/WeilConjectures`, Mathlib, and the blueprint found no duplicate topological
comparison. `AlgebraicGeometry.constantSheaf_sections_locallyConstant` concerns
schemes and the small étale site and does not apply here. Mathlib's
`Topology.IsOpenEmbedding.preirreducibleSpace`,
`PreirreducibleSpace.preconnectedSpace`, `LocallyConstant.eq_const`, and
`LocallyConstant.apply_eq_of_preconnectedSpace` close the other steps directly.

## New nodes

`lem-sc-constant-sheaf-locally-constant-comparison`:
`dag/nodes/sec-curve-estimates/lem-sc-constant-sheaf-locally-constant-comparison.json`.
One generic theorem states additive equivalences between constant abelian sheaf
sections and locally constant functions on every open, together with pointwise
restriction naturality. It has no irreducibility assumption and does not identify
sections with A. Its source is Definition 006W and Example 0081; its proof dependencies
are the existing locally constant sheaf lemma, constant-sheaf definition, and
sheafification universal property. The original theorem still has to prove evaluation
is an additive equivalence and restriction becomes the identity, which it does in Lean.
No change record is needed: there is no changed existing definition or statement.


## Second reading by A2

1. Statements: PASS. Read both modules and diffed the target against the repository.
   The existing theorem signature is byte-identical, including irreducibility,
   sheafification, universes, nonempty-open hypotheses, additive equivalences and
   the restriction equation. Only its proof and a plain proof-only import changed.
   No existing definition or public import changed; no change record is needed.

2. Proof and axioms: PASS as a partial reduction. Both modules compile together
   cleanly through lcompile.py. Read the evaluation inverse laws and final hc
   rewrite: its two evaluation points lie in the same preconnected U, so
   apply_eq_of_preconnectedSpace gives the restriction equation regardless of the
   choices. There are no forbidden declarations, attributes, or hollow definitions.
   The target contains no sorry; the comparison's whole proof is the sole named
   sorry. A scratch #print axioms check of both declarations gives exactly propext,
   Classical.choice, Quot.sound and sorryAx. This is a reduction depending on the
   open comparison, not yet an axiom-clean proof of the target.

3. Split-off theorem: PASS. Read Definition 006W
   (https://stacks.math.columbia.edu/tag/006W) and Example 0081
   (https://stacks.math.columbia.edu/tag/0081): locally constant maps with restriction
   describe the constant sheaf and are constant-presheaf sheafification. The new
   theorem is their abelian version. Read its complete gluing proof and docstring:
   open fibres cover U, unequal fibres have empty overlap, the empty-cover sheaf
   condition makes sections there unique, and common refinements give independence.
   Intersections of fibres of f and g prove addition; intersection with V proves
   restriction; uniqueness gives the universal property. Checked empty opens,
   singleton spaces, a two-point discrete space (sections A × A), zero coefficients,
   and identity inclusions. No connectedness is required by this comparison. Its
   cross-universe AddEquiv does not force LocallyConstant U A into AddCommGrpCat v;
   the sheafification existence assumption is retained. It isolates step 2, while
   evaluation and the restriction equation remain actual Lean proofs in the target.
   Fresh LeanFinder search for sheafification of the constant presheaf found generic
   and condensed constant sheaves and the sheaf of all functions, no topological
   comparison. Fresh msearch grep and rg on Mathlib topology sheaves, repository
   Lean and upstream source found no duplicate. Read the nearby DAG nodes: the
   existing locally-constant comparison uses schemes and their small étale sites;
   the open-maps result concerns morphisms of set-valued sheaves, not this additive
   comparison. No available interface closes this construction in a few minutes.

4. Pruning and route: PASS after report clarification. Mathlib directly closes
   inheritance of preirreducibility, preconnectedness, eq_const and constancy of
   evaluation. The new import is plain because only the proof uses it; the new
   module's public imports provide its signature and locally constant group
   structure. No unused proof-only import was found. Old/new proof_deps remove
   exactly the locally-constant sheaf node and constant-sheaf definition as direct
   edges; both remain under the comparison, and are now explicitly listed above.
   No module or node is globally pruned. Read sk-thm-curveestimate.realized:
   its statement is thm-sc-proper-cohomology, with no designated step for this
   item. The original four-step route remains and no unit is bypassed.

5. Nodes: PASS after metadata repair. The existing node changes only proof,
   proof_deps and proof_origin, and follows the Lean's four steps. Checked the new
   node's source, complete proof, dependency union, searches, split status, created
   record, blueprint ancestry, chapter/unit and verbatim Lean statement. Its
   declaration and module match the file. Its gluing construction had incorrectly
   been marked elementary without citing the sheaf condition; now it is marked
   non-elementary, cites def-weil-pbc-sites-and-cohomology, and spells out the fibre
   covers used to prove addition and restriction. Updated its dependency union.

Second reading changed only the report's explicit list of removed direct proof
edges and the new node's gluing-step classification, citation and explanation.
No Lean proof or statement needed repair.
