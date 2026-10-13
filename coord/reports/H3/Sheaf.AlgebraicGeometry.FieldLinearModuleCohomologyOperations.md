## What changed

Completed eleven existing proof obligations in
`lean/Sheaf/AlgebraicGeometry/FieldLinearModuleCohomologyOperations.lean`.
No existing signatures or definition bodies changed. Added four proof-only Mathlib imports:
`CategoryTheory.Adjunction.Additive`, `RingTheory.Flat.CategoryTheory`,
`CategoryTheory.Monoidal.Braided.Reflection`, and
`CategoryTheory.Monoidal.Closed.FunctorCategory.Basic`.
All original global commands, including attribute placement, are unchanged.
A proved private tensor-comparison helper and a local irreducibility attribute support the
pure-tensor characterization. The local command is documented in
`coord/changes/fieldLinearTensorCoefficientLocalTransparency.md`; it does not affect any importer. Updated the existing node's proof route and proof origin.

The scalar restriction proof uses naturality of the structure ring map.
The sheaf proof reflects sheafhood through the forgetful functor to abelian groups.
Finite limits are reflected from sectionwise evaluation. Inverse image uses its left
adjunction, additive pushforward, and the flat opens map. Tensor exactness uses flatness over
a field, sheafification, reflective monoidal closedness, and the braiding.
The tensor coefficient formula is the sheafification adjunction identity composed with
its monoidal comparison, evaluated on a pure tensor.

## Proved and sorry left

Holes closed (eleven of seventeen original holes; no holes added, no decomposition):

- `AlgebraicGeometry.Scheme.Modules.exists_scalarTensorCoefficient`.
- `AlgebraicGeometry.Scheme.Modules.scalarFunctor_preservesFiniteLimits`.
- `AlgebraicGeometry.Scheme.Modules.scalarInverseImage_additive`.
- `AlgebraicGeometry.Scheme.Modules.scalarInverseImage_preservesFiniteColimits`.
- `AlgebraicGeometry.Scheme.Modules.scalarInverseImage_preservesFiniteLimits`.
- `AlgebraicGeometry.Scheme.Modules.scalarPresheaf_isSheaf`.
- `AlgebraicGeometry.Scheme.Modules.scalarRestriction_linear`.
- `AlgebraicGeometry.Scheme.Modules.scalarTensorLeftColimits`.
- `AlgebraicGeometry.Scheme.Modules.scalarTensorLeftLimits`.
- `AlgebraicGeometry.Scheme.Modules.scalarTensorRightColimits`.
- `AlgebraicGeometry.Scheme.Modules.scalarTensorRightLimits`.

Existing holes left, each with source, proof in words, and
`(blueprint: def-sc-field-linear-module-cohomology-operations)`:

- `AlgebraicGeometry.Scheme.Modules.exists_moduleExtEquiv`.
- `AlgebraicGeometry.Scheme.Modules.exists_scalarPullbackCoefficient`.
- `AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_add`.
- `AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_bijective`.
- `AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_smul`.
- `AlgebraicGeometry.Scheme.Modules.scalarFunctor_preservesFiniteColimits`.

The two private helpers used during experiments are not new obligations. Only the proved
private helper `scalarTensorInclusionComparison` is present in the delivered module.

## No longer needed

None. No original import, node, or module was pruned. Each added import supports a proof:
additive adjunctions for inverse image; field flatness for tensor limits; monoidal reflection
for tensor colimits and the tensor comparison; closed functor categories for tensor colimits.
No new Sheaf dependencies were introduced, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The prior sandbox attempt had no report or node update and its full-file compile exceeded
60 seconds. Diagnostic prefixes and kernel profiling showed expensive checking around the
Ext comparison constructions. Several additivity proofs were tried, including an explicit
composition of additive identities and a proved private Ext-map helper. They did not give a
full module within the required limit, so `scalarCohomologyExtMap_add` remains its original
named whole-proof hole. No definition was split and no timeout limit or kernel check was
changed. Profiling options and diagnostic files remain only in the scratchpad and are not
part of the delivery.

The existing node's prose referred to seventeen remaining obligations after K1; this
partial delivery leaves six. No mathematical statement error was found.

## Second reading by H3

1. PASS. Read the full module and diff against the repository version. Every existing
   declaration signature and definition body is byte-for-byte unchanged. The additions
   are eleven proof bodies, four plain proof-only imports, a proved private helper, and
   the documented local irreducibility attribute. Existing global commands are unchanged.
   The local attribute changes elaboration inside this file only, not exported data.
2. PASS. The delivered file compiled locally with lcompile.py in 44.8 seconds, without
   errors or warnings. A scratch copy with explicit `#print axioms` for each of the eleven
   closed declarations compiled in 53.2 seconds: each uses only propext, Classical.choice,
   and Quot.sound, with no sorryAx. Text inspection finds exactly the six listed existing
   whole-proof holes, no added holes, forbidden trust bypass, or sorry in a definition.
   The existing choices are characterized comparisons: resolution cocycles determine
   moduleExtEquiv, and the adjunction's sectionwise formula determines the pullback map;
   they are not arbitrary witnesses of mere existence.
3. PASS. No new statement was split off, and no new public declaration was introduced.
   The private tensor helper is fully proved; its comparison is the adjunction-unit
   identity after cancelling the sheafification tensor comparison. Independent LeanFinder
   and grep searches for monoidal adjunction tensor/unit identities returned the general
   adjunction formulas, but no duplicate of this specialized Sheaf.tensorLeftIso formula.
   Restriction maps, zero sheaves, the empty open, identity inverse image, and degree zero
   introduce no exceptional hypotheses in these proofs.
4. PASS. The closed holes reduce directly to sectionwise module laws, Mathlib reflection
   of sheafhood and limits, additive adjunctions, flat Kan extension, field flatness,
   reflective monoidal closedness, and braiding. The tensor formula applies the
   sheafification homEquiv inverse identity and then evaluates on a pure tensor.
   Each added plain import supplies a used result or instance. No old proof dependency
   was removed (the old proof_deps is empty), so No longer needed is complete. Read
   dag/units/sk-prop-av-cube.json: no realized statement or step is changed or bypassed.
5. PASS. Compared the node JSON with its repository version: only proof and proof_origin
   change. The added proof step describes exactly the eleven closed obligations and the
   six existing obligations left open; proof_deps remains empty, consistently with this
   route using Mathlib and existing local constructions rather than new DAG obligations.
   There are no new nodes or missing split-off records.

Second reading changed only this report by recording the independent checks and verdicts.
No Lean repair, signature change, additional hole, or pruning was needed.
