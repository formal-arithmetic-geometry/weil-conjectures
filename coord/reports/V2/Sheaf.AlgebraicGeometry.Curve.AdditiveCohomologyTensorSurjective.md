## What changed

Repaired the returned delivery against the current comparison-square module.
The other landing has already proved
`AlgebraicGeometry.Scheme.Modules.exists_additive_cohomology_baseChange_square`
from `exists_additive_cohomology_pullback_comparison`; its current hypothesis is
`CompactSpace C`. The item already constructs this instance from quasi-compactness
of the curve. Removed the stale sandbox comparison-square module and node rather
than overwrite that landing. Cleared the old sandbox compiled artifacts so the
verification uses the published comparison-square theorem.

The item proves
`AlgebraicGeometry.IsCurve.additive_cohomology_tensor_surjective` by tensor
induction from that current square and
`Scheme.Modules.H.baseChange_bijective_of_isSeparated`. The tensor equivalence
is `id tensor e`; the target equivalence is `e'`. Their commuting identity
transports a preimage of the ordinary base-change map into a preimage of beta.
The original signature, public imports and docstring are unchanged. The only new
imports are proof imports of `AdditiveCohomologyBaseChangeSquare` and
`FlatCohomologySeparated`. Updated the item's proof dependency node and proof
origin to describe use of the current, existing comparison theorem.

## Proved and sorry left

Closed: `AlgebraicGeometry.IsCurve.additive_cohomology_tensor_surjective`
(node `lem-pbc-additive-cohomology-tensor-surjective`): 1 of 1 original sorries.
No sorry remains in the item's module. No new sorry is added, and no theorem is
split off in this repair. Imported dependencies can still depend on existing
sorries; this is a proof from the project's stated lemmas, not a claim that the
entire geometric comparison is now free of sorries.

Compilation uses lcompile.py with no stale sandbox comparison-square artifacts.
The proof handles arbitrary tensors through zero, pure tensors and addition;
linearity and the given hbeta supply the pure-tensor case. The final equality
uses injectivity of e' and cancellation of the tensor equivalence. No definition
or data construction is added, and no arbitrary witness becomes public data.

## No longer needed

Removed the following five direct proof imports from the current repository item:

- `Sheaf.AlgebraicGeometry.Cohomology.AffineCechInverseImage`
  (`lem-pc-affine-cech-inverse-image`).
- `Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyCechBaseChange`
  (`lem-pc-flat-cech-base-change`).
- `Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyCechNaturality`
  (`lem-pc-flat-cech-cohomology-square`).
- `Sheaf.AlgebraicGeometry.EtaleQcoherentSourceComparisonNatural`
  (`lem-sc-etale-qcoherent-source-comparison-natural`).
- `Sheaf.AlgebraicGeometry.EtaleTensorUnitSectionsNatural`
  (`lem-sc-etale-tensor-unit-sections-natural`).

They are unnecessary as direct dependencies of this item. The ordinary separated
flat theorem and the current comparison-square route encapsulate the required
geometric work. Some of these modules remain transitively imported; this report
does not claim they are pruned from the complete target closure.
Removed the obsolete delivered copy of `AdditiveCohomologyBaseChangeSquare` and
its node: both now exist in the repository and need no change in this delivery.
There are no new nodes or forced adaptations.

## Where the brief, the DAG or earlier work was wrong

The return identified a real overlapping-file conflict: the previous delivery
would replace a comparison-square module changed since its base. The repository
version has a complete scalar-upgrade proof and a `CompactSpace C` hypothesis,
whereas the stale copy introduced a sorry and used `QuasiCompact f`.
This repair imports the current version and makes no edit to that module or node.
It therefore preserves the other landing's proof and interface.

The previous report's descriptions of a new comparison node and one added sorry
are obsolete. No new comparison theorem is necessary now. The item's retained
curve/Artin-Schreier route uses the existing separated flat theorem for the finite
affine-cover argument; no realized blueprint unit statement or step is removed.
The report's old second reading described the returned version and was removed;
the second reader must review the repaired delivery.

## Second reading by V2

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof imports and proof body differ as described above. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or warnings. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, and no definition contains postponed data. Verdict: pass.
3. Audited the proof route and DAG node. The proof uses the current additive comparison square, tensor induction, and separated flat base-change theorem; the node's proof, dependencies, and origin match these declarations. No new statement or node is introduced, and the existing unit route is retained. Verdict: pass.
4. Checked for shorter available library or Mathlib routes using repository search and the recorded searches. No direct geometric theorem replaces the comparison-square plus separated-flat route. Verdict: pass.
5. Checked pruning and imports. The five stale direct imports listed above are removed, while required public imports and proof-only imports remain minimal. Verdict: pass.

Changed only the item's proof, proof-only imports, matching DAG proof metadata, and this second-reading report. No statement, definition, or node interface was changed.
