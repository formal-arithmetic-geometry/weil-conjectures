## What changed

Replaced the sole sorry of `AlgebraicGeometry.Smooth.stableUnderGeneralization_section_component`
by a complete Lean reduction to local noetherian approximation and the noetherian
specialization case. Added two proof-only imports and their two new modules. The
original declaration, universes, hypotheses, public imports and docstring are unchanged.
Updated its DAG proof to match the reduction.

The top-level proof chooses a neighbourhood and model at the special point. An open
contains every generalization of its points; subtype specialization and continuity
therefore transport the specialization to the model. Component membership transfers
forward at the special point and backward at the general point. No model is chosen in
a definition; the existential theorem is eliminated solely into the theorem's proof.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Smooth.stableUnderGeneralization_section_component`
(node `lem-sbc-smooth-section-component-generalization`).

Added two holes, so this is a decomposition, not an unconditional geometric proof:

- `AlgebraicGeometry.Smooth.exists_section_component_noetherian_model`
  (`lem-sbc-smooth-section-component-noetherian-model`).
- `AlgebraicGeometry.Smooth.section_component_generalization_of_isNoetherian`
  (`lem-sbc-smooth-section-component-noetherian-generalization`).

No sorry remains in the item's module. Each new module contains precisely one public
named theorem whose entire proof is `by sorry`, with source and proof in words.
All three modules compile locally without warnings. The local axiom probe is run
by the delivery dry run; existing dependency holes remain part of this decomposition.

Edge cases checked: an empty source has no point needing a model; the identity
morphism has singleton fibres and immediate component membership; equal specialization
points require no trait argument. The noetherian theorem does not assume the source
or its fibres are globally connected, affine, separated or proper. In its argument
only the relevant special-fibre component and total-space component are retained.
The model theorem quantifies over all points of its open, with no component membership
or specialization premise, so it supplies approximation data rather than the goal.
The other theorem has the genuinely restrictive extra noetherian-base hypothesis.

## No longer needed

None. The original node had no proof dependencies or proof-only imports, and both
new proof imports are used. `WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat`
is not imported: it reaches this item via Slicing and would create an import cycle.
Its affine theorem does not cover a nonaffine total space. No unit statement or
realized unit step is bypassed; this unit's `realized` arrays are empty.

## Where the brief, the DAG or earlier work was wrong

The existing node's sole non-elementary step contained approximation, base-change
compatibility, trait tracing and generic-fibre connectedness but named no proof
nodes. This delivery makes the two main geometric parts separate Lean tasks.
There is no Mathlib global component theorem found by the searches. LeanSearch was
unavailable; LeanFinder, Loogle and source searches were used as well.

WANTED: Stacks Project source, Tags 055Q, 055M, 054F and 055J, for the two new nodes.
The local `literature/stacks-project` and blueprint directories are absent on this
machine. The Stacks statements and arguments were checked on their official online
pages; the formal decomposition is recorded with agent proof origin.

## New nodes

`lem-sbc-smooth-section-component-noetherian-model`:
`lean/Sheaf/AlgebraicGeometry/SmoothSectionComponentNoetherianModel.lean`.
This isolates finite-presentation descent and component base-change compatibility;
it is independent of specialization and constructs local noetherian model data.

`lem-sbc-smooth-section-component-noetherian-generalization`:
`lean/Sheaf/AlgebraicGeometry/SmoothSectionComponentNoetherianGeneralization.lean`.
This isolates the noetherian trait argument of Tag 055Q. Its proof plan removes
unwanted special-fibre components and uses Tag 055J before returning by Tag 055M.

Both inherit chapter and unit from the item and have source, proof steps,
three kinds of recorded searches and exact Lean records. No change record is needed:
all existing interfaces are unchanged and new modules are imported only for proofs.

## Second reading by C1

1. Interfaces: PASS. Compared the delivered item with the repository by `diff -u`.
   The existing declaration's signature, universes, hypotheses, conclusion and docstring
   are byte-for-byte unchanged. Only two plain proof imports and the proof body change.
   The existing node changes only `proof`, `proof_deps` and `proof_origin`. There are
   no changed definitions or change records.
2. Kernel and holes: PASS as a decomposition. Compiled all three modules through
   `lcompile.py --all`; no errors or warnings. Inspected every declaration: no axiom,
   unsafe, opaque, implemented_by, extern or data definition occurs. The only two
   sorries are precisely the public named theorems listed above. A scratch-copy
   `#print axioms` checks all three declarations; only standard axioms and `sorryAx`
   occur. The existential model is eliminated inside a theorem proving a proposition,
   never used to define an arbitrary data object. The delivery probe also checks axioms.
3. Split statements: PASS. Read the official Stacks pages
   [055Q](https://stacks.math.columbia.edu/tag/055Q),
   [055M](https://stacks.math.columbia.edu/tag/055M),
   [054F](https://stacks.math.columbia.edu/tag/054F) and
   [055J](https://stacks.math.columbia.edu/tag/055J).
   Finite presentation follows from smoothness plus the two compactness hypotheses.
   Smoothness can be descended after increasing the approximation stage. Component
   base change applies because the component contains the rational section point.
   On the trait, the unwanted special components are closed in the total space;
   the two sections remain after removing them and after retaining the total-space
   component meeting the connected special fibre. Flatness and reduced special
   fibre then meet exactly the hypotheses of 055J. Checked empty sources, equal
   points, identity morphisms and disconnected smooth fibres: no connectedness of
   the whole fibre or whole source is assumed. Both holes are strict parts of the
   argument, not renamed versions of the unrestricted item. Each has a source,
   complete proof docstring and matching node. Independent LeanFinder query
   "Connected components in fibres of smooth scheme morphisms with a rational
   section and specialization of points" returned only stalk, flat-map, fibre and
   rational-map tools. Loogle `"Smooth", "connectedComponentIn"` and msearch grep
   `connectedComponentIn.*specializ|section_component|geometricallyConnected.*section`
   returned no match. Direct `rg` searches of both source roots confirmed that the
   existing SlicingFlat theorem requires affine source and base; its base-change
   theorem is not the local-model theorem and importing that file here is cyclic.
   General approximation tools do not supply the complete new statements directly.
4. Route and pruning: PASS. The proof first reduces to an open neighbourhood and
   a noetherian model, transports specialization using subtype topology and
   continuity, and applies the noetherian result. Both proof imports are used;
   the public Mathlib import supplies the signatures. The repository node had no
   old proof dependencies to prune. The unit `sk-prop-normal-form` has empty
   `realized.statement` and `realized.steps` arrays; the argument keeps its slicing
   route and bypasses no realized node. No split hole can be closed in a few minutes
   using the searched declarations.
5. DAG agreement: PASS. The parent node's two dependencies are exactly the two
   geometric theorems used by the Lean proof; its elementary step is the actual
   open/subtype/continuous-map argument. Both new nodes have the required creation,
   source, proof-origin, search, blueprint, chapter, unit and Lean records, and
   their Lean signatures agree with the modules.

Second reading changed only this report: added independent source, edge-case,
search, signature, axiom, route and node checks. No Lean repair was needed. One
original hole is closed and two lower holes are added: this remains a decomposition,
with net holes closed minus added equal to -1 for these declarations, not an
unconditional proof or a claimed closure-ledger improvement.
