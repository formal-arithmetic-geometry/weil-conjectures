## What changed

The existing theorem `AlgebraicGeometry.Scheme.nonempty_squareZeroRelativeUnitsAdditiveKernelIso`
has its original signature and docstring unchanged. Its proof applies the new, fully proved
`AlgebraicGeometry.Scheme.nonempty_unitsAdditiveKernelIso_of_sections` to the subscheme inclusion,
then discharges the sectionwise hypothesis with `AlgebraicGeometry.Scheme.squareZeroRelativeSectionKernel`.
The comparison lives in the new module `SquareZeroUnitsAdditiveKernelOfSections`; the remaining
geometric calculation lives in `SquareZeroRelativeSectionKernel`. Both new imports in the item
are proof-only. The unused proof import `WeilConjectures.CategoryTheory.Sites.Torsor` was removed.
No existing definition or public signature changed; no change record or forced adaptation is needed.

## Proved and sorry left

Closed existing hole: `AlgebraicGeometry.Scheme.nonempty_squareZeroRelativeUnitsAdditiveKernelIso`
(node `lem-sc-square-zero-relative-units-additive-kernel`). Its body is a genuine reduction,
not an axiom-free completed proof: it still depends on the one geometric hole below.

New proved declaration: `AlgebraicGeometry.Scheme.nonempty_unitsAdditiveKernelIso_of_sections`
(node `lem-sc-square-zero-relative-units-additive-kernel-sections`). The second reader proved
it by explicit natural group maps and categorical kernel lifts. Its axioms are exactly
`propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.

Added hole: `AlgebraicGeometry.Scheme.squareZeroRelativeSectionKernel`
(node `lem-sc-square-zero-relative-section-kernel`). Its proof is exactly `by sorry`, with a
complete affine-chart and sheaf-separation argument in its docstring and matching node.
This is the only sorry in the three delivered modules. The item consequently has `sorryAx`
in its axiom closure, in addition to the three permitted axioms.

Relative to the repository: one existing hole closed, one hole added. This is a decomposition
with net hole change zero, not a completed proof of the original result. The first worker's
unproved `nonempty_squareZeroRelativeUnitsAdditiveKernelIso_of_sections` was removed before
landing and replaced by the proved, more general comparison; it is not an additional ledger gain.

## No longer needed

Removed import: `WeilConjectures.CategoryTheory.Sites.Torsor`; no torsor result is used.
No claim is made that its module is globally pruned from the targets' import closure.

The old direct proof dependencies `def-sbc-ideal-sheaf-powers`,
`def-sc-etale-additive-structure-restriction`, and `def-sc-gm-torsor` are replaced in the item's
node by the two new intermediate nodes. Their definitions are still needed transitively,
and the two public imports that supply the existing signature remain. No old dependency node
or unit realization is discarded. The redundant public import of `EtaleAdditiveStructureSheaf`
in the new section-kernel module was narrowed to `WeilConjectures.AlgebraicGeometry.Sites.Gm`.

## Where the brief, the DAG or earlier work was wrong

The first worker's sectionwise helper retained the original geometric hypotheses, including
`hII`, and its natural-language node merely repeated the original theorem without mentioning
`hsq`. That was not a satisfactory reduction. The helper is now proved for an arbitrary
scheme morphism with just a square-zero section-kernel hypothesis; it requires no ideal sheaves
or closed immersion. The first report also incorrectly said that no import was removed and
omitted the updated original node. Both are repaired.

## New nodes

`lem-sc-square-zero-relative-section-kernel` isolates only the geometric assertion that two
vanishing sections have zero product. Its node and docstring explain the quotient ideal,
base change, affine cover, and sheaf separation. It is strictly smaller than a sheaf isomorphism.

`lem-sc-square-zero-relative-units-additive-kernel-sections` now records the proved general
comparison in `SquareZeroUnitsAdditiveKernelOfSections`, with an exact multiline Lean statement
and a proof following the code. Both nodes have provenance, creation records, and the three
search kinds. No change record is needed because these are new declarations.

## Second reading by G1

1. Compared the delivered item with the repository by diff: the sole existing declaration's
signature is byte for byte unchanged, as are its docstring and the two public imports. All
changes are in its proof and proof-only imports; neither new module changes existing data.
Verdict: pass after removing the redundant first-worker helper.

2. Compiled all three modules locally, in import order, with `lcompile.py`, without errors
or warnings. Checked all delivered code for forbidden declarations and for sorry in data.
Explicit `#print axioms` checks show only the permitted axioms for the proved comparison;
the geometric hole and item additionally have `sorryAx`. No arbitrary existence witness is
used to define data: the unit inverse is explicitly `1-a`. Verdict: pass, with one reported hole.

3. Checked the geometric split on I=J, I=0, empty objects, and arbitrary nonaffine etale
objects via the affine-cover argument. It uses only I*I ≤ J, not nilpotence of I on X.
Checked the general comparison on zero rings and the square-zero quotient example
k[epsilon]/(epsilon^2) → k; a nonzero ring mapping to the zero ring fails its square-zero
hypothesis as expected. Searched Mathlib via leanfinder, loogle, and grep with alternate
queries about closed immersions, base-change kernels, and categorical kernel lifts; also
searched the local library for square-zero comparisons. Found useful infrastructure but
no duplicate of the remaining geometric theorem. Verdict: the one split is true, needed,
and strictly a part of the original argument. The algebraic comparison is now proved.

4. Read downward from the item and checked the shorter sectionwise route. Removed the
unused torsor import, retained the signature imports, and used explicit kernel lifts instead
of leaving the comparison open. The unit `sk-prop-h2` and its `realized` record are unchanged:
this node is below its fixed Kummer/Brauer route, and no unit statement or step is bypassed.
Verdict: pass; dependency replacements and limits on pruning are listed above.

5. Checked the new node statements against the exact Lean signatures, repaired the helper's
statement and module record, expanded both proof plans, removed stale copied review fields
from the new helper node, and updated the original node's `proof`, `proof_deps`, and
`proof_origin` to match the two-step proof. Verdict: pass.

Second reading changed: proved and generalized the comparison in its own module; removed the
restatement helper; restored the original docstring; corrected imports, all three proof-node
records, and the report. Only the geometric section-product theorem remains open.
