## What changed

Prepared a reduction of AlgebraicGeometry.nonempty_localizedResidueHomology_restriction_iso
into a homology-sheaf restriction comparison and a global-sections scalar comparison.
The latter is proved using the existing tensor-pullback-tilde comparison and the
one-point evaluation equivalence. Its statement works for arbitrary field maps.
The assigned theorem composes the two comparisons by whiskering natural isomorphisms.
The new modules compile separately and together in dependency order.

The assigned module and both auxiliary modules compile in dependency order.
The missing published definition module reported by the earlier attempt is now
available. No dependency source is included in this delivery merely to supply
compiled artifacts. The main proof uses local instances written with `let` and
has no redundant `change` tactic.

## Proved and sorry left

Proved and compiled:
AlgebraicGeometry.nonempty_fieldSpec_tensorPullback_globalSections_iso
(node lem-sc-field-spec-tensor-pullback-global-sections).

Closed the one original hole:
AlgebraicGeometry.nonempty_localizedResidueHomology_restriction_iso
(node lem-sc-localized-residue-homology-restriction). This is a decomposition, not a complete proof of the import closure.

One hole added:
AlgebraicGeometry.nonempty_localizedResidueHomology_sheaf_restriction_iso
(node lem-sc-localized-residue-homology-sheaf-restriction). Its statement compiles.
It compares homology sheaves before global sections and scalar extension; it is
strictly a part of the original argument, rather than the original module-valued statement.

There are no other textual sorries in the delivery. The new statements include the
zero object and arbitrary derived objects; the open-site comparison is vacuous for
an empty open, since x is a point of that open.

## No longer needed

Removed direct proof imports from the assigned module:
Sheaf.AlgebraicGeometry.DerivedPullbackComposition,
Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses,
Sheaf.Topology.PointModuleEvaluationEquivalence, and
Sheaf.AlgebraicGeometry.ResiduePullbackGlobalSections.
The first two remain dependencies of the new homology-sheaf comparison.
PointModuleEvaluationEquivalence remains a dependency of the proved field comparison.
Only Sheaf.AlgebraicGeometry.ResiduePullbackGlobalSections
(node lem-sc-residue-pullback-global-sections) is no longer needed by this route.
No claim is made that this module is unreachable from other targets.

## Where the brief, the DAG or earlier work was wrong

The existing interfaces leave naturality, exact homology transport, and localization
universe transport to be assembled. The new sheaf-level statement records this remaining
part explicitly; the scalar part can already be proved through tilde and evaluation.
The source documents are not in this machine's literature checkout. The arguments
are recorded as agent assemblies of the source-based declarations that were read.
LeanSearch is unavailable (Internal Server Error), and this is recorded as unavailable.
The blueprint ancestor tool returns None for this item's id, apparently because its
created.item is a module name. New nodes preserve the existing node's blueprint ancestor
thm-sc-theorem-of-cube and add this node to its via chain.
The earlier missing published object file is now available; the composition compiles.

## New nodes

lem-sc-field-spec-tensor-pullback-global-sections:
lean/Sheaf/AlgebraicGeometry/FieldSpecTensorPullbackGlobalSections.lean.
A proved scalar comparison for every field homomorphism; precomposition by the tilde
equivalence reduces it to the existing tensor-pullback-tilde comparison. No hole added.

lem-sc-localized-residue-homology-sheaf-restriction:
lean/Sheaf/AlgebraicGeometry/LocalizedResidueHomologySheafRestriction.lean.
The one remaining hole, a comparison valued in module sheaves on the new residue scheme,
before taking any global sections. It records derived open pullback, the residue square,
composition, exactness of pullback along the residue-field isomorphism and universe transport.
There are no definition or signature changes and no change records.


## Second reading by M4

1. **Declarations unchanged.** I diffed the assigned module against the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only its proof and proof-only imports changed. The two additional Lean files are new modules corresponding to the two new DAG nodes.

2. **Proof and axioms.** All three modules compile together with `lcompile.py`. The closed theorem has no textual `sorry`; the only remaining `sorry` is the named theorem `nonempty_localizedResidueHomology_sheaf_restriction_iso` in its own split-off module. The field-spectrum comparison reports only `propext`, `Classical.choice`, and `Quot.sound`; the two theorems depending on the split-off statement additionally report `sorryAx`, as expected. No axiom, unsafe, opaque, extern, implemented_by, or hollow definition occurs.

3. **New statements.** The field-spectrum statement is a genuine scalar comparison, proved by the existing one-point evaluation equivalence and tensor-pullback/tilde comparison. The sheaf-level statement is a strict intermediate: it stops before global sections and scalar transport, and is therefore strictly simpler than the assigned module theorem. Both statements include arbitrary objects and the zero object; an empty open has no possible point `x`, so it introduces no counterexample. Searches found no existing declaration of either result.

4. **Pruning and DAG agreement.** The target proof uses exactly the two split/field comparison nodes recorded in its updated `proof_deps` and follows their proof steps. The old direct proof-only imports are no longer needed; `ResiduePullbackGlobalSections` is no longer used. In the scalar module, the proof-only `public import Mathlib.AlgebraicGeometry.Modules.Tilde` was redundant through TensorPullbackTilde and was removed entirely. I read `dag/units/sk-prop-av-cube.json`: its realized fields are empty in the baseline, and this delivery does not bypass or change its step applying the general cube theorem. The existing theorem-of-cube ancestor and its via chain are retained in the new nodes; no target or definition was changed.

5. **Delivery checks.** The local all-modules compile succeeds, and deliver3.py --no-push printed OK with the expected CODEX class (new nodes and one split-off sorry). I changed only the scalar module's import visibility and the target proof/imports; no other module's interface was adapted.

What I changed: added this second-reading report section, removed the redundant proof-only public tilde import, and confirmed the existing proof/decomposition and DAG metadata. No further theorem could be closed without proving the genuinely missing sheaf-level comparison.

Source check: I also read Stacks Tags [08DW](https://stacks.math.columbia.edu/tag/08DW), [0D5S](https://stacks.math.columbia.edu/tag/0D5S), [009A](https://stacks.math.columbia.edu/tag/009A), and [01I9](https://stacks.math.columbia.edu/tag/01I9) online. These support open compatibility, derived composition, the one-point identification, and tensor pullback of tilde; the new comparisons are assemblies of those results and the existing Lean declarations, not direct quotations of those tags.

Final cache check: removed an old sandbox compiled copy of the non-delivered LocalizedResidueHomology dependency, and all compiled scratch probes. The final delivery checks therefore resolve that dependency from the published library.
