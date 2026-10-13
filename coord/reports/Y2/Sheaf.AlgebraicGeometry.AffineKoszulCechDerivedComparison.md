## What changed

The existing declaration `AlgebraicGeometry.affine_koszul_cech_derived_comparison`
has an unchanged signature, visibility, and docstring. Its proof now establishes
invertibility of the two actual comparison factors and then transports along `e`.
It uses a K-injective resolution, the defining equation of
`principalCechDerivedComparison`, the existing augmentation quasi-isomorphism,
and `IsIso.of_isIso_comp_right`. No definition or existing statement changes.

Two new statement modules contain the remaining mathematical bridges:
`Sheaf.AlgebraicGeometry.KoszulCechComparisonIsIso` and
`Sheaf.AlgebraicGeometry.PrincipalCechResolutionQuasiIso`. Each has a source,
complete proof in words, and matching node. The old generic comparisons remain
proof-plan imports of these new bridges. All new proof-only imports are plain
`import`; the sole public import of the original item is unchanged.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.affine_koszul_cech_derived_comparison`.
The item has one original theorem and no local `sorry` now.

Holes added:
- `AlgebraicGeometry.koszulCechComparison_isIso`, node
  `lem-sc-koszul-cech-comparison-is-iso`.
- `AlgebraicGeometry.principalCech_resolution_quasiIso`, node
  `lem-sc-principal-cech-resolution-quasi-iso`.

This is a decomposition (one hole closed, two added, net -1), not an
axiom-complete proof or a claim of positive sorry-ledger progress. The two
remaining statements concern distinct steps: the explicit chain comparison,
and totalization of a resolution. Neither asserts the final derived composite.
No holes are added inside definitions. The rejected unpublished core hole
`AlgebraicGeometry.affine_koszul_cech_derived_comparison_core` is removed entirely;
it is not counted as an upstream hole closed.

All three modules compile cleanly with lcompile.py. Scratch copies with
`#print axioms` check each delivered theorem; all three show exactly `propext`, `Classical.choice`, `Quot.sound`, and
`sorryAx` from the named open statements and existing dependencies, with no
other axioms.

## No longer needed

Removed from the item's direct imports:
`Sheaf.AlgebraicGeometry.AffineKoszulHomAlternatingCech` and
`Sheaf.AlgebraicGeometry.QCohComplexAlternatingCechDerivedSections`.
Their old proof-dependency nodes
`lem-sc-affine-koszul-hom-alternating-cech` and
`lem-sc-qcoh-complex-alternating-cech-derived-sections` are replaced as direct
proof dependencies by the two narrower bridge nodes. Both old modules and
nodes remain dependencies of the respective bridge proof plans; no upstream
module is pruned from the closure and the mathematical route is preserved.

Removed from the unpublished first-reader candidate:
`AffineKoszulCechDerivedComparisonCore.lean`, its new core node, and its
unnecessary change record. No existing declaration requires a change record.
Removed a redundant public import of `Coherent` from the new resolution module;
quasi-coherence is already exposed through `PrincipalOpenCechTotal`.

## Where the brief, the DAG or earlier work was wrong

The first worker's core statement still asserted the entire Koszul-to-derived
comparison before the final, automatic transport along `e`. It transferred
both substantive steps into one `sorry`; the report incorrectly called that
strictly smaller progress. Its declaration docstring also lacked a complete
proof, and the original node had not been updated to record the new dependency.
The second reader rejected and removed this core rather than relying on the
syntactic restatement guard to find it.

The existing `affineKoszulHomAlternatingCech` interface only supplies existential
complexes and a comparison; it does not directly identify its witnesses with
the specified A-linear diagram and cocone. The general
`qcoh_complex_alternating_cech_derived_sections` interface uses a scheme covering
its whole space and modules over its global-section ring. Our construction is
on a union of principal opens and has coefficients in A. The two new bridges
isolate those identification/localization steps without altering any interface.
A direct application of the generic statements would miss these steps.

## New nodes

`lem-sc-koszul-cech-comparison-is-iso` in
`dag/nodes/sec-picard-framework/lem-sc-koszul-cech-comparison-is-iso.json`
states invertibility of the specified chain map, before derived localization.
It follows Stacks Tag 08D1, including the explicit sign and fraction maps.

`lem-sc-principal-cech-resolution-quasi-iso` in
`dag/nodes/sec-picard-framework/lem-sc-principal-cech-resolution-quasi-iso.json`
states the quasi-isomorphism on Čech totals induced by a K-injective resolution.
Its proof is the affine-intersection comparison and induction on the finitely
many Čech rows from Stacks Tags 08D2 and 08C2. No quasi-coherence of the resolution
or boundedness of either complex is silently assumed.

No change records are needed: no existing signature, definition, or public
import changed. The original node's `proof`, `proof_deps`, and `proof_origin`
now record the actual reduction; its statement and Lean record are unchanged.

## Second reading by Y2

1. **Interfaces: pass after repair.** Read the original and delivered item in
full and compared them with `diff -u`. The entire original declaration signature
through `:= by`, its docstring, universe parameters, and public imports agree
byte for byte. Changes are confined to its proof and plain imports. New modules
only add the two declarations listed above; there are no data constructions or
forced adaptations and no change to `Challenge.lean`.

2. **Proof and axioms: pass, conditional on the recorded holes.** Compiled all
three modules in dependency order with lcompile.py, with no errors or warnings.
Only the two named public theorems have `:= by sorry`. There is no axiom,
unsafe/opaque declaration, extern, implemented_by, skipped kernel checking,
or holed definition. The target really uses the defining Čech comparison equation:
it identifies its composite with three invertible factors with Q(Cech(i)),
then cancels those factors and composes with Q(Koszul) and the image of e.hom.
No arbitrary data are chosen from an unproved existence theorem by this delivery.
The resolution is obtained within a proof; existing chosen construction witnesses
remain the ones pinned by their defining formulas.

3. **Split statements: pass after replacement.** Read the defining transition,
cocone, Čech total, augmentation and comparison modules and the two original
comparison modules. Checked both new signatures against Stacks
[08D1](https://stacks.math.columbia.edu/tag/08D1),
[08D2](https://stacks.math.columbia.edu/tag/08D2), and
[08C2](https://stacks.math.columbia.edu/tag/08C2).
For r=0 the nonempty-subset index is empty and both totals are zero; for r=1
the first theorem is the multiplication-colimit localization and the second
is the affine section comparison. Nilpotent/zero f gives zero localized terms;
the zero coefficient complex is included. K-injectivity of J is needed to
compute derived sections on each open, and quasi-coherence is only imposed on F.
Finite Čech length, not bounded vertical length, justifies totalization.
Each hole has a complete argument in its docstring and a verbatim signature in
its node. Ran LeanSearch (unavailable: Internal Server Error), independent leanfinder,
loogle and grep queries via msearch.py and
rg on both library roots, recorded in the new nodes. Hits included generic
Functor.map_isIso, derived localization of quasi-isomorphisms, and homology-
preserving functors; these justify the formal reduction but do not close the
specific localization or Čech resolution bridges. Neither new statement merely
renames the whole original conclusion. Neither could be closed by a short
application of an existing declaration: their interface identifications remain.

4. **Route and pruning: pass after repair.** The proof proceeds from the original
item downward, first using standard functor/isomorphism facts, then the two
strictly intermediate comparison steps and the already stated augmentation.
Both original comparison nodes remain below the new bridges. Read
`dag/units/sk-thm-picard-duality.json`: its `realized` entries do not name this
item; no unit statement or step is replaced or bypassed. The original 08D1 then
08D2 route stays. The list above names every old direct proof dependency removed;
no library module becomes pruned. The redundant Coherent import is removed.

5. **DAG: pass after repair.** Opened all delivered nodes and matched their Lean
module, declaration, and verbatim signature. The original node now describes
the three proof stages actually used. Each new node has the required source,
proof steps and their union as proof_deps, proof_origin, the required search kinds (including an honest LeanSearch outage record),
created record, blueprint ancestry, chapter/unit, status split, and Lean record.
Original statement/stmt_deps and all maintainer-owned fields remain unchanged.

Changed by the second reading: removed the near-restatement core and its node/
change record, replaced it with two independently sourced bridge statements,
wrote the actual K-injective comparison/cancellation proof, repaired the DAG,
removed redundant imports, and corrected the hole accounting to a decomposition.
