## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_target_leray_comparison`
with a reduction to two independent mathematical steps. The source and target
cohomology models are compared for the scalar-extension unit; a separate module, with the supplied algebra explicitly identified with the canonical
section map, then supplies the chart identification and the normalized affine target Leray map
in module cohomology. The assigned theorem explicitly constructs e0, uses source
coefficient naturality at restrictFunctorIsoPullback, and composes the two map
equalities. All existing signatures and public imports stay unchanged.

Validation: the sandbox set compiles without warnings through lcompile.py. The
assigned file remains within the required single-file compile limit. The final
delivery dry run performs the preflight and axiom probes; nothing is pushed.

Added `Sheaf.AlgebraicGeometry.ModuleCohomologyExtPullbackComparison` and
`Sheaf.AlgebraicGeometry.FlatBaseChangeModuleLerayComparison`, each with one named
public theorem, a source, a full proof in words, and a matching new DAG node.
Updated the assigned node's proof, proof_deps and proof_origin to this reduction.
No definition, target statement, existing auxiliary signature or visibility changed.

## Proved and sorry left

Closed the assigned module's one hole:
`AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_target_leray_comparison`
(node `new-flat-base-change-target-leray-comparison`).

Added exactly two holes, both in new statement modules:

- `AlgebraicGeometry.Scheme.Modules.exists_moduleCohomology_ext_pullback_comparison`
  (node `new-module-cohomology-ext-pullback-comparison`).
- `AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_module_leray_comparison`
  (node `new-flat-base-change-module-leray-comparison`).

This is a decomposition: one upper hole closed and two strictly separate lower
holes added, net minus one hole. It is not a proof free of sorry dependencies.
The first new theorem has no ambient higher image, resolution choices or Leray
edge. It compares only the module and Ext maps of a scalar-extension unit, with
natural comparisons for every coefficient module. The second has no source Ext
comparison and no H.baseChangeLinear: it proves only the target chart/unit/Leray
part in module cohomology, allowing any natural target coefficient comparison.
Neither is a renaming or repackaging of the assigned theorem.

The new statements include p=0, zero coefficients and empty schemes/opens. In the
first, zero rings and arbitrary nonflat scalar extensions are permitted: exactness
is used only for abelian inverse image. In the second, quasi-coherence and qcqs
are used only for the target affine Leray isomorphism, and no cohomological
pullback is asserted bijective. An arbitrary natural E on the target is admissible
because scalar endomorphism naturality makes it linear; its inverse merely changes
coordinates on the already normalized module-cohomology edge.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Mathlib.AlgebraicGeometry.Modules.Sheaf`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices`
- `Sheaf.AlgebraicGeometry.LerayDegenerateSections`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`
- `Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison`
- `Sheaf.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `Sheaf.Paper.HigherDirectImagePresheaf`
- `Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`

The statement primitives are available through unchanged public imports and the
new statement modules. The assigned node now directly uses only the two new
nodes and `lem-weil-pbc-open-immersion-module-pullback-restriction`. Its former
proof dependencies are removed as direct dependencies, except that restriction
comparison. The source comparison, module/abelian comparison, affine class map,
scalar compatibility, higher-image presheaf and module h-map functoriality remain
needed in the lower proof plans. No global pruning of those nodes or modules is
claimed; no blueprint unit statement or realized step is bypassed.

The complete list of former direct DAG proof dependencies retired from the assigned
node is:

- `def-pc-fibre-product`
- `def-pc-flat-cohomology-comparison`
- `def-pc-module-pullback`
- `def-weil-pbc-flat-base-change-open-choices`
- `def-weil-pbc-module-cohomology-fmap`
- `lem-pc-affine-vanishing`
- `lem-pc-leray-degenerate-sections`
- `lem-pc-ordinary-higher-image-quasi-coherent`
- `lem-sc-module-abelian-zariski-cohomology`
- `lem-sc-module-cohomology-source-comparison`
- `lem-weil-pbc-higher-direct-image-presheaf`

These are direct-edge retirements, not claims that their modules leave the targets’
import closure. Global modules pruned: none.

## Where the brief, the DAG or earlier work was wrong

The original plan describes the correct mathematical comparison but does not
expose its cross-model unit-map compatibility in a usable Lean theorem.
`exists_moduleCohomology_source_comparison` gives naturality only for coefficient
morphisms on one scheme; independent choices on source and target do not establish
compatibility with scheme pullback. That normalization is the first new item.
The affine section bijectivity result alone does not identify the scalar-extension
chart or compare its coefficient map with D.psi; that is the second new item.

Checked the unit record `sk-thm-p1`: the assigned node is below its realized
statements/steps. The reduction preserves the affine-local dictionary used by the
formal-functions branch and adds no flatness assumption.

Read Stacks Tags 03FD, 01FB, 01F7, 01E4, 01XK and 02KH directly on the Stacks website; the local
clone contains the literature index but not the regenerated Stacks source files.
LeanFinder returned generic Ext-resolution and affine-geometry lemmas, Loogle gave
no exact match (the Sheaf.H.mapFunctor identifier was unknown to that service),
and LeanSearch returned Internal Server Error. Local searches included Mathlib,
the adopted library, the source comparison, h-map functoriality, normalized affine
section classes and existing derived chart comparison modules. No exact match
was found; the failed service is not evidence of absence.

## New nodes

`new-module-cohomology-ext-pullback-comparison`, in
`Sheaf.AlgebraicGeometry.ModuleCohomologyExtPullbackComparison`, isolates natural
coefficient comparisons normalized to intertwine the base-change unit h-map with
H.baseChangeLinear. Its proof follows the common injective-section diagram of
03FD and 01FB and exact abelian inverse image; there is no target Leray assertion.

`new-flat-base-change-module-leray-comparison`, in
`Sheaf.AlgebraicGeometry.FlatBaseChangeModuleLerayComparison`, isolates the chart
identification, coefficient-unit transport, target affine Leray isomorphism and
its D.targetClass normalization, entirely in module cohomology. Its proof follows
01XK, 01E4 and h-map functoriality. The report records the edge cases above, and the
node records the available searches and the existing lower declarations to use.

There are no change records or forced adaptations.

## Second reading by P4

1. Compared the assigned module against the repository with diff. The existing
   theorem signature is byte-for-byte unchanged; the existing public imports,
   docstring and visibility are unchanged. Only proof imports, local options and
   the proof body differ. There are no definitions, adaptations or change records.
   Verdict: pass.
2. Read the full proof and both new modules. The assigned proof constructs e0
   explicitly and combines source coefficient naturality, unit-map compatibility
   and the normalized target formula by equality transitivity. The only two
   remaining sorries are exactly the public theorems listed above. There is no
   forbidden declaration or hollow definition. E, E prime and b are witnesses
   eliminated inside a proof of a proposition, and e0 is explicitly their
   composite; no definition exports data chosen from either open theorem.
   Local compile and axiom checks
   are recorded below after validation. This remains a decomposition, not a
   sorry-free proof of the assigned result. Verdict: pass as a decomposition.
3. Checked the two split statements against their Lean signatures, their nodes,
   the existing source comparison, h-map functoriality, affine class bijectivity
   and scalar compatibility declarations, and Stacks Tags 03FD, 01FB, 01XK and
   01E4. The first isolates a comparison of cohomology models for the unit;
   the second isolates chart transport and the target class map. Neither
   restates the assigned theorem. Arbitrary target E is admissible: naturality
   at coefficient multiplication transports the displayed B-action, and the
   inverse of E changes coordinates in the class equivalence. Checked p=0,
   identity and nonflat scalar extension, zero rings, zero modules and empty
   opens at the level of these constructions. None introduces an extra
   invertibility assumption. Independent LeanFinder, Loogle and Mathlib/source
   searches found no exact reusable cross-model/unit or chart/class comparison;
   neither remaining hole is a few-minute consequence of the available lemmas.
   Verdict: both statements are true, needed, and strictly separate parts of
   the argument; pass.
4. Checked the original dependencies and the realized fields of sk-thm-p1.
   No realized unit statement or step is bypassed. Proof-only imports are plain
   imports; new public imports supply types and definitions in the new
   signatures. Completed the explicit list of all retired direct proof edges
   above, while preserving the distinction from global module pruning.
   Verdict: pass after the reporting correction.
5. Checked that proof_deps equals the union of uses in each node's proof, the
   new Lean records reproduce their signatures, and new nodes carry source,
   searches, created, blueprint, chapter, unit and lean fields. The assigned
   node's proof and proof_origin describe the actual equality composition.
   Verdict: pass after making the new node's algebra hypothesis explicit.

Second reading changes: made the retired direct DAG dependencies explicit;
clarified the canonical algebra hypothesis in the new Leray node's prose;
added independent search records and this review. The original delivered proof
was retained: it passed the initial full compile, scratch axiom checks and
required dry run. Later artifact-producing compiles hit the process timeout on
the shared machine; attempted proof elaboration simplifications and local
transparency/linter settings did not resolve it, so all were reverted. No
Lean proof, signature, definition or additional linter setting is changed by
this second reading.

Validation: independently ran lcompile.py --all on the three delivered modules;
all compiled without warnings. The source files contain zero, one and one
sorries respectively, exactly as listed under Proved and sorry left.

A scratch module imported all three compiled modules and ran #print axioms on
each delivered theorem. Each reported exactly propext, Classical.choice,
Quot.sound and sorryAx; no other axiom. The scratch file compiled cleanly.
The sorryAx dependence is expected from the two explicitly documented holes.

The required deliver3.py --no-push run printed OK: the set compiles and passes
the preflight. Review class is CODEX because this decomposition adds two public
statement modules and DAG nodes. No axiom-probe failure was reported.
