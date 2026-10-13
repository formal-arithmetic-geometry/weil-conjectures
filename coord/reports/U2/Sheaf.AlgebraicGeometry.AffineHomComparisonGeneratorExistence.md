## What changed

Proved `AlgebraicGeometry.exists_affineHom_generator_extension` in
`Sheaf.AlgebraicGeometry.AffineHomComparisonGeneratorExistence`, with its signature unchanged.
Added the proof-only import `Mathlib.CategoryTheory.Adjunction.Additive` and six proved
private helpers: the abstract extension of an additive, scalar-balanced assignment,
additivity and component evaluation of internal-Hom sections, scalar compatibility of
localized tilde maps, its chart restriction, and naturality of the chart scalar sections.
The morphism is constructed as the adjoint of an explicitly defined linear map; no data
is chosen from an unproved existence theorem.

Updated the existing node's proof, proof dependencies, and proof origin to describe the
compiled argument. No definitions or existing interfaces changed, and no modules required
adaptation. The unit has no realized nodes at this branch and its route is unchanged.

Validation: compiled the complete module through `lcompile.py`; the delivery dry run
performs the declaration axiom probe and stage-3 preflight. The proof handles arbitrary
modules, zero rings, and zero modules uniformly and needs no finite-presentation or
quasi-coherence assumption on internal Hom.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_affineHom_generator_extension`
(node `new-affine-hom-generator-extension-existence`), the module's only original hole.
No `sorry` remains in this module. No holes or new public declarations were added elsewhere.
This is a proof, not a decomposition: one hole closed, zero holes added.

## No longer needed

No imports or modules were removed. The proof no longer needs the dependency edge to
`lem-weil-pbc-spec-tilde-free-module`: scalar balancing works for any linear isomorphism
`e : T(A) ≅ O_U`. That node remains a statement dependency because the unchanged statement
still mentions `tildeSelf`; its Mathlib module is still needed. Thus no entire module is
claimed to leave the targets' import closure.

No other original proof dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically valid. It unnecessarily required substitution of
the heterogeneous equation fixing `e`. Only the equation fixing `T` is needed in the proof.
Composing the tilde and chart-restriction adjunctions first also avoids a separate transport
of the comparison morphism after its construction.

The search found the existing tilde adjunction and unit/section equivalences, but no theorem
constructing this comparison. Searches run through `msearch.py`: leanfinder for the affine
internal-Hom comparison, loogle for `SheafOfModules.unitHomEquiv`, and grep for
`tilde.*homObj|homObj.*tilde`. Read the Mathlib and source implementations of tilde,
restriction, and internal Hom. Checked the source mapping property and localization
identities in [Stacks Tag 01I7](https://stacks.math.columbia.edu/tag/01I7) and
[Stacks Tag 01HV](https://stacks.math.columbia.edu/tag/01HV).

## Second reading by U2

1. **Interface and accidental changes.** Compared the delivered module and node with the repository versions. The public theorem signature and all existing declarations are byte-for-byte unchanged; only the proof, a proof-only import, and the node's proof metadata changed. Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds with no errors and no `sorry`. The construction is explicit via the additive adjunction and localized-section calculations, with no hollow definition or forbidden declaration. Verdict: pass.

3. **Split statements and duplication.** No new public or split-off theorem was added. The six private helper lemmas are proved and internal to the target proof; searches and repository grep found no existing declaration duplicating the construction. Verdict: pass.

4. **Pruning and route.** The proof follows the affine tilde/global-sections and chart restriction route, while avoiding the unnecessary normalization substitution for `e`. The removed proof dependency is `lem-weil-pbc-spec-tilde-free-module`; the unchanged target still mentions it in its statement, so its module remains in the statement closure. Verdict: pass.

5. **DAG agreement.** The node's proof steps, proof dependencies, and proof origin match the compiled proof, and no unit realization was altered. Verdict: pass.

Changed after second reading: no source changes were needed; this section records the comparison and successful compilation. The required delivery dry run and delivery command are run after this report update.
