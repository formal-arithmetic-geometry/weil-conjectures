## What changed

Added the proof of `externalGlobalSectionsTensor_bijective_of_finite_cover`. The proof uses the pairwise-intersection limit characterization of sheaves and finite-limit preservation by tensoring over a field. Added the strictly smaller intermediate statement `exists_externalSectionsRestrictionComparison`, whose proof is left for a subsequent worker. The module imports this intermediate result and the Mathlib flatness and sheaf-condition APIs.

## Proved and sorry left

Closed the original hole in `externalGlobalSectionsTensor_bijective_of_finite_cover` by a compiling proof from the new restriction-comparison theorem. This is a decomposition (one hole closed, one added), not a sorry-free proof of the transitive argument. The added theorem `exists_externalSectionsRestrictionComparison` remains `sorry`; it is a strict restriction-compatibility component of the argument and has node `lem-sc-external-global-sections-restriction-comparison`.

## No longer needed

The finite-cover proof does not use the planned open-immersion pullback/restriction declarations directly, nor the composite-adjunction and conjugate-unit declarations. They remain cited only by the split intermediate node's planned proof. No existing imports were removed, and no module is claimed globally pruned.

All four old proof dependencies removed from the finite-cover node's direct route are:
`lem-weil-pbc-open-immersion-module-pullback-restriction`,
`lem-weil-pbc-module-restriction-open-immersion-colimits`,
`def-weil-pbc-composite-adjunction`, and `lem-weil-pbc-conjugate-iso-unit-equation`.
The first, third and fourth remain dependencies of the restriction-comparison node;
`lem-weil-pbc-module-restriction-open-immersion-colimits` is unused by either proof route.
The scalar-presheaf sheaf condition is recorded explicitly through
`def-sc-field-linear-module-cohomology-operations`.

## Where the brief, the DAG or earlier work was wrong

The DAG's prose describes a large equalizer argument but provides no Lean-level comparison identifying the global external map with the chartwise maps. The local Stacks TeX checkout is absent; Tag 0BED was read at https://stacks.math.columbia.edu/tag/0BED. It omits the degree-zero canonical-cup verification, so the new node records an agent-written expansion. That missing compatibility is isolated as the intermediate theorem above; the remaining descent argument is completely implemented.

## New nodes

`lem-sc-external-global-sections-restriction-comparison` — `Sheaf.AlgebraicGeometry.ExternalGlobalSectionsRestrictionComparison`; no existing public interface changes.


## Second reading by M1

1. **Existing interfaces: pass.** Read both delivered modules and diffed the finite-cover
module against the repository. The existing theorem's signature and docstring are byte
for byte unchanged: the arbitrary field, schemes, coefficients, finite index type,
cover equality, chart bijectivity and overlap bijectivity remain exactly as before.
The existing public import is retained; the three added imports are proof-only.
The comparison module is new, and no existing definition or target is changed.
No change record is needed.

2. **Kernel and data checks: pass, with the reported hole.** Both files compile locally
through lcompile.py in import order, without warnings. Explicit scratch-copy
`#print axioms` checks show only propext, Classical.choice, Quot.sound and sorryAx
for the finite-cover theorem and residual theorem; the two new data declarations
externalSectionsPushforward and externalSectionsTopIso use no sorryAx.
There is exactly one delivered sorry, the named public theorem
exists_externalSectionsRestrictionComparison. There are no axioms, unsafe/opaque
or external implementations, no skipped kernel checking, and no holed definitions.
The proof obtains c and the isomorphisms locally to prove a proposition; it does not
use this existence theorem to define any data. The generic private helper proves
its conclusion by conePointsIsoOfNatIso and naturality, without holes.

3. **Residual statement: pass as a strict component.** Read Stacks Tag 0BED at
https://stacks.math.columbia.edu/tag/0BED, especially the definition of the external
cup map and the final omitted degree-zero verification. The new docstring is an
agent expansion of that omitted compatibility, not a claim that the source states
the stronger arbitrary-module descent theorem verbatim. The residual theorem
requires neither a cover nor local bijectivity and asserts only a natural map and
its identifications on open restrictions. Thus it does not restate finite-cover
bijectivity. Checked the construction on V=top, V=empty, zero F or G, and empty X
or Y: restrictions and coefficient isomorphisms still exist; at empty opens all
section modules are zero. The k-actions agree by the pullback equation. Tensor
bilinearity, adjunction-unit naturality, open base change, composition comparison
and the tensor-pullback comparison supply exactly the docstring's steps.
Independent searches used leanfinder with 'Sheaf tensor sections natural
transformation restriction open immersion pullback', loogle with
'"conePointsIsoOfNatIso"', and grep with 'tensor.*restriction|restriction.*tensor|cone.*[Ii]so'.
Also searched lean/Sheaf, lean/WeilConjectures, Mathlib module sheaves, and flat
category theory. Found restrict_obj, restrict_map, restrictFunctorIsoPullback,
restrictAdjunction_unit_app_app, tmulSection_map and generic cone-point tools,
but no assembled restriction comparison. The existing ModulePullbackTensor
provides a relevant building block; it is not the residual statement. Closing
that residual requires a substantial construction and is not a few-minute repair.

4. **Descent and pruning: pass after report repair.** The proof actually carries out
the finite-cover part: flatness over a field preserves the finite pairwise limit;
the scalar section sheaf and its pushforward give the other two limit cones;
the chart and overlap hypotheses identify every component as an isomorphism;
cone-point uniqueness then gives the top map's bijectivity. An empty cover is
covered by the empty pairwise diagram and hcover; zero modules and empty overlaps
are included without additional assumptions. The three proof imports respectively
supply restriction compatibility, pairwise sheaf limits and tensor finite-limit
preservation, so none is redundant. The public ScalarGlobalSectionsComparison
import is needed by the signature. Checked dag/units/sk-prop-av-cube.json: its
realized statement and step lists are empty, and this below-unit decomposition
changes none of the unit's fixed route. No module import is removed. Expanded
No longer needed to name every old direct proof dependency that was removed,
including the colimit-preservation node unused even by the new residual route.

5. **DAG and Lean: pass after dependency repair.** Read both JSON nodes. The parent
now records the restriction comparison followed by the actual pairwise-limit
argument; the new node records the construction and restriction comparison, with
source, complete docstring proof, searches, creation metadata, blueprint ancestor,
chapter/unit and verbatim Lean statement. Added the explicit dependency
 def-sc-field-linear-module-cohomology-operations to the parent's second proof
step and proof_deps because scalarPresheaf_isSheaf is used there. The parent
signature in its lean record still matches the unchanged Lean declaration.
The new theorem's existential c and eS/eT express compatibility only; its use in
the parent discharges a strictly separate descent argument.

Second reading changed only dependency metadata and reporting: completed the
removed-dependency list, recorded the scalar-presheaf dependency, and added this
review. The Lean proof and residual statement needed no repair. One original
hole is closed and one lower hole is added: net zero, a decomposition rather
than a completed transitive proof.
