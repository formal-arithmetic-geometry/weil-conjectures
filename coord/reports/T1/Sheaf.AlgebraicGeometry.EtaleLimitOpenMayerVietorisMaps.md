## What changed

Replaced the sorry in `etale_limit_open_mayerVietoris_maps` by a construction of both
product cocone transformations, their naturality and four projection identities, followed
by assembly of the restriction row and difference/boundary rows. The stage and limit cover equations are also proved directly by inverse-image
preservation of unions and top. The target signature and visibility are unchanged. Added `EtaleLimitOpenRestrictionTransform` and
`EtaleLimitOpenBoundaryTransform`, with a node for each.

## Proved and sorry left

The original hole in `AlgebraicGeometry.Etale.etale_limit_open_mayerVietoris_maps` is
closed by decomposition. The product legs and projection formulas are proved directly.
`AlgebraicGeometry.Etale.etale_limit_open_restriction_transform` constructs the actual
restriction transformation, proves naturality and its right cocone square from
`openSquareCoefficient_cohomology`, and proves its two component identities.

One new hole remains:
`AlgebraicGeometry.Etale.etale_limit_open_boundary_transform`, node
`lem-weil-pbc-etale-limit-open-boundary-transform`. It constructs only the difference and
boundary maps, their exact pairs, and the two left squares, using a supplied canonical
restriction row. This is a decomposition, not a claim of a sorry-free geometric theorem.
No sorry occurs in any definition or private helper.

## No longer needed

Removed the parent module's unused proof imports:
`Sheaf.AlgebraicGeometry.EtaleMayerVietoris`,
`Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback`, and
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`.
Their corresponding nodes are no longer direct proof dependencies of the parent.
These modules and nodes remain needed by the boundary-transform dependency, so no
module is claimed pruned from the transitive target closure. The complete list of old
parent proof dependencies removed is `lem-weil-pbc-cohomology-pullback-functorial`,
`lem-weil-pbc-etale-limit-open-cohomology-cocone-degree`,
`lem-weil-pbc-etale-mayer-vietoris`, and
`lem-weil-pbc-etale-mayer-vietoris-pullback`. The degree-cocone node remains a
statement/definition dependency through its public module import.

The construction theorem `etale_limit_open_cohomology_cocone_degree` is not invoked:
the open diagrams and legs are already supplied by the target's hypotheses. Its module
is retained as a public import because it supplies the canonical map definitions used
in the unchanged signature. No node or module in the unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous retry timed out while checking the parent assembly. This retry preserves the
same reduction and successfully compiles the complete parent proof through `lcompile.py`
(56.7 seconds). It introduces the statement's leading lets explicitly, wraps the concrete
product-leg construction in a proved existential helper, and checks the right square and
four projection equations pointwise. Local irreducibility of `upperStar` and
`cohomologyMap` keeps the transported map types symbolic during elaboration. These local
attributes change no exported signature or definition. Both new modules also compile;
the first dry run compiled the set and passed its axiom probes, but preflight required
a change record for the local attribute command. The record documents that no definition
or exported interface changes; the second-reading section remains the next worker's. No tool or wall-clock compile limit
was changed.

The earlier attempt's claim that no strictly simpler intermediate statement could be
written was incorrect. The restriction row is independent of the boundary construction;
the difference/boundary rows can be stated with a supplied restriction transformation
identified by its two actual components. The product cocone transformations can be
constructed directly and their projections proved definitionally.

The new intermediate statements omit coefficient identity/composition and G-arrow laws:
the supplied natural diagrams and canonical arrow formulas already carry the needed
naturality. Their proofs do not need these additional hypotheses. Empty or coincident
opens, zero coefficients, a singleton diagram, and arbitrary cocones preserve the
component arguments. The boundary statement receives the actual stage and limit covers; no compactness,
limit or colimit hypothesis is introduced. Sources read: Stacks Tags 0A50 and 09YQ.

## New nodes

`lem-weil-pbc-etale-limit-open-restriction-transform` records the actual restriction
transformation and right square, with two canonical component identities. Module:
`Sheaf.AlgebraicGeometry.EtaleLimitOpenRestrictionTransform`.

`lem-weil-pbc-etale-limit-open-boundary-transform` records difference and boundary maps
and the two left squares with exactness, for a supplied canonical restriction row.
Module: `Sheaf.AlgebraicGeometry.EtaleLimitOpenBoundaryTransform`.

The parent node's proof and proof dependencies now follow this assembly. No statement
or definition was changed and no adaptation is needed. Change record:
`coord/changes/etale-limit-open-mayer-vietoris-local-reducibility.md`, required by the
static check for the local attribute command.

## Second reading by T1

1. Compared the parent module with the repository using diff and an exact text
   comparison of its declaration signature: byte-for-byte unchanged. The other two
   modules are new. No exported definition changes or forced adaptations occur.
   The local irreducibility command is scoped to the namespace and affects proof
   elaboration only; its change record accurately describes this scope. Verdict: pass.
2. Independently compiled all three modules through lcompile.py: boundary 27.7 s,
   restriction 49.3 s, parent 52.0 s, without errors or warnings. Read the concrete
   pairLeg definition and its naturality proof, both restriction component proofs,
   and the final assembly. The only delivered sorry is the named boundary theorem;
   none occurs in a definition or private helper, and no forbidden declaration or
   kernel-check bypass occurs. Explicit #print axioms probes in a scratch module show only propext,
   Classical.choice and Quot.sound for the restriction theorem, with sorryAx also
   present for the parent and the declared boundary hole. Verdict: pass, conditional
   on the reported boundary hole.
3. Read the boundary statement, its full docstring proof and node. It is strictly a
   part of the parent: the restriction transformation and product leg are supplied,
   and no right square is asserted. Its canonical component assumptions determine
   the restriction row; no arbitrary witness is installed in a definition. Exactness
   is preserved under the supplied isomorphisms. Coefficient and pullback naturality
   of a single functorial Mayer--Vietoris construction give simultaneous naturality
   of the boundary, rather than independent choices of connecting maps. Checked
   empty opens, coincident opens (the difference sequence is split), zero sheaves,
   degree zero and singleton index diagrams; no extra geometric hypothesis is needed.
   Read [Stacks 0A50](https://stacks.math.columbia.edu/tag/0A50) and
   [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ). The latter supplies the
   coherent-system context, not a colimit hypothesis for this lemma. Repeated searches
   with leanfinder (connecting homomorphism naturality), loogle (biprod.lift), grep
   (delta naturality), and rg in both library roots found construction tools and
   the existing single-square results, not a duplicate of the boundary transformation.
   Closing this geometric assembly requires more than a short application. Verdict: pass.
4. The proof uses the existing openSquareCoefficient_cohomology declaration for
   restriction, biprod.lift for its pair, and elementary pointwise products for both
   legs. These are direct routes. Public imports support signature definitions,
   biproduct instances and Function.Exact; the new transformations are plain proof
   imports. All four removed old direct node dependencies are now explicitly named
   above. No transitive module is claimed pruned. Read sk-thm-p1's realized statement
   and all step records: this reduction is below that unit and bypasses none of them.
   Verdict: pass.
5. Each node's stored Lean statement matches the actual declaration. Only proof,
   proof_deps and proof_origin change in the existing node. The restriction node's
   dependency legitimately includes openSquareCoefficient_cohomology in the
   degree-zero cocone node's lean.declarations; it does not claim to invoke that
   node's existential cocone theorem. The two new nodes have source, complete proof,
   search records, provenance, blueprint, unit/chapter and Lean fields. Their proof
   dependency unions match their recorded steps and the parent assembly. Verdict: pass.

Second reading changed the report only: completed the removed-node inventory and
recorded the independent review. No Lean proof or statement required repair. One old
hole closes and one new hole is added, so this is a decomposition with net zero holes,
not a sorry-free proof of the geometric result.
