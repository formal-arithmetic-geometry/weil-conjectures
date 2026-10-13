## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Proj.gradedModuleChart_principalLocalization` with a complete
Lean proof. The statement and its visibility are unchanged. Its new proof-only
import is `Sheaf.AlgebraicGeometry.ProjChartRestrictionIsLocalized`.

Constructed the whole-chart additive equivalence explicitly with
`Scheme.Modules.restrictAppIso`, transport along `ι_image_top`, and `alpha f`.
Proved that whole-chart restriction, precomposed with this equivalence's inverse,
is linear over the chart ring: `basicOpenToSpec_app_top` identifies the pulled-back
constants with `awayToSection`, and restriction respects scalars.

The new intermediate theorem supplies only `IsLocalizedModule` for this concrete
linear restriction map. The item's proof constructs its comparison using
`IsLocalizedModule.iso`, proves normalization with `iso_symm_apply`, and proves the
full section-ring scalar formula using `linearMap_compatibleSMul`. The supplied
ring equivalence is an algebra equivalence because it preserves constants.

Both modules compile together through `lcompile.py --all`. No existing definitions,
statements, public imports, or other modules were changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.Proj.gradedModuleChart_principalLocalization`
(node `lem-weil-pbc-proj-graded-module-chart-principal-localization`). No `sorry`
remains in the item module.

Added: `AlgebraicGeometry.Proj.gradedModuleChart_restriction_isLocalized`
(node `lem-weil-pbc-proj-chart-restriction-is-localized`). Its entire proof is
`by sorry`, in its own new module, with source and proof in its docstring.

This is a decomposition: one upper hole closed, one lower hole added, net zero.
The new statement isolates the geometric localization universal property; the
whole-chart comparison, restriction linearity, construction of the final
comparison, normalization, and extension to all section-ring scalars are proved.
The remaining statement does not mention the arbitrary ring equivalence `t` or
assert the final existential comparison. Edge cases r=0 and unit r are covered
by the stated universal property and discussed in the docstring.

## No longer needed

No original imports were removed: both public Mathlib imports are needed by the
unchanged statement. No original DAG dependency is pruned from the entire
argument: `lem-weil-pbc-proj-basic-open-intersection` is needed by the intermediate
localization argument. It is now a dependency of the new node rather than a
direct proof dependency of the item. Thus the old direct dependency
`lem-weil-pbc-proj-basic-open-intersection` is no longer needed directly in the
parent proof, but remains in the new node's `proof_deps`; its Mathlib declarations
come from the new module's public Basic import. No module is pruned. No unit statement or unit proof step is
bypassed. No other planned module was imported.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt said restriction-section isomorphisms were absent. Mathlib
provides `Scheme.Modules.restrictAppIso` and the scalar and restriction naturality
lemmas; these were used in the proof. The remaining obstruction can be stated as
the universal property of the concrete restriction map, so it does not prevent a
compiling reduction.

The node's steps described as elementary conceal the geometric scalar comparison
and the change from powers of r^deg(f) to powers of r. Those remain inside the
new named intermediate theorem, with the argument spelled out in its docstring.
No false statement or interface change was found.

## New nodes

`lem-weil-pbc-proj-chart-restriction-is-localized` is attached to
`AlgebraicGeometry.Proj.gradedModuleChart_restriction_isLocalized` in
`lean/Sheaf/AlgebraicGeometry/ProjChartRestrictionIsLocalized.lean`. It inherits
chapter `sec-proper-base-change` and unit `sk-thm-reduction`; its source is Stacks
Constructions Tags 01M4, 01M7 and 01MB. The source pages were read on the Stacks
website because this clone does not contain the downloaded constructions.tex.
Its statement includes the explicit canonical whole-chart equivalence and scalar
restriction, and asks only for the three localization conditions. The original
node's proof and dependencies were updated to the actual Lean assembly. There
are no change records because no existing interface changed.

## Second reading by Y2

1. Interface preservation: compared both delivered modules with the repository.
   `ProjChartRestrictionIsLocalized` is new. In the existing module the only edits
   are its proof-only import, two local elaborator options, and the theorem proof.
   The signature of `gradedModuleChart_principalLocalization`, including every
   hypothesis, both existential comparisons, the arbitrary normalized `t`, the
   scalar identity and restriction normalization, is byte-identical. Its local
   instance and all public imports are unchanged. No change record is needed.
2. Proof: both modules compiled cleanly through `lcompile.py --all` (8.5 s and
   47.5 s). Read the construction of `b`, the `ktop` scalar comparison via
   `basicOpenToSpec_app_top`, and the linearity of restriction via `map_smul`.
   The new lemma is applied to precisely that linear restriction. The inverse of
   `IsLocalizedModule.iso` supplies `c`; `iso_symm_apply` supplies normalization.
   The constant-normalized `t` is an algebra equivalence, so
   `linearMap_compatibleSMul` proves the full section-ring scalar assertion.
   Scratch copies with `#print axioms` for both theorems compiled (9.0 s and
   49.1 s): exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The scratch copies were removed. The sole remaining `sorry` is the reported
   named intermediate. No forbidden
   declaration or hollow definition occurs; all data in this proof is constructed
   explicitly or from the localization universal property, which uniquely
   determines its normalized comparison.
3. Split statement: read [Stacks 01M4](https://stacks.math.columbia.edu/tag/01M4)
   (1)(e),(h), [01M7](https://stacks.math.columbia.edu/tag/01M7) (1)-(3), and the
   chart argument in [01MB](https://stacks.math.columbia.edu/tag/01MB). The new
   statement uses arbitrary submodules with the supplied localization equivalences;
   it does not assume that M is graded or invoke a tilde theorem for arbitrary F.
   For r=a/f^n, g=f*a has degree (n+1)*deg(f)>0, lies inside D_+(f), and hU gives
   U=r^deg(f). hcanonical determines the ring restriction on fractions, and
   hscalar, hrestriction and htheta give the linear equivalence psi described in
   the expanded docstring. The three conditions follow from ordinary module
   localization, including r=0, unit r, a zero module and empty charts. For r=0,
   localization kills the whole module by the denominator zero and sections on
   the empty open vanish; no nonzero-ring hypothesis is used. This is strictly
   the localization-property part of the argument: b, restriction linearity, c,
   normalization and the arbitrary-t scalar formula are proved in the parent.
   It is a decomposition, not a net proof. Independent Loogle, LeanFinder and
   grep searches used different queries (recorded in searches.jsonl and the node).
   Read Mathlib `IsLocalizedModule.of_linearEquiv`, `of_exists_mul_mem`, and
   `Scheme.Modules.IsLocalizing`/`isLocalizing_tilde`; these do not establish the
   given F's chart restriction. The existing `principalOpen_chart` in
   `ProjGradedModuleChartBasisComparisonFixedGenerators` is private and proves
   only the open-set identification. No exact public duplicate or quick closure
   of the geometric intermediate was found.
4. Route and pruning: the reduction takes the direct localization-iso route and
   uses the Mathlib scalar-extension theorem. Both original public imports are
   needed in signatures and the new import is proof-only. The old direct proof
   dependency `lem-weil-pbc-proj-basic-open-intersection` is explicitly relocated
   to the new node, not discarded from the argument. Read
   `dag/units/sk-thm-reduction.json`: neither node realizes a fixed unit statement
   or step, and this chart reduction preserves the symmetric-product/Chow route.
   No module is pruned and no unit realization changes.
5. DAG agreement: parsed comparison shows the existing node changes only in
   `proof`, `proof_deps`, `proof_origin`; its statement, statement dependencies,
   Lean signature, unit and chapter are unchanged. Its three proof steps match
   the explicit linear restriction, localization iso, and scalar extension.
   The new node matches the universal-property theorem, inherits the chapter
   and unit, has its source, creation record, blueprint origin and searches, and
   depends on the chart-intersection Mathlib leaf without a cycle back to the
   item. Its remaining proof is documented as the geometric transport and three
   localization conditions, with no extra assumption.

Second-reading changes: expanded the new theorem's natural-language proof to give
beta, psi, denominator and equality witnesses, and an explicit inverse for the
r-action; expanded the corresponding DAG proof steps; completed the new node's
`mathlib_match` and `lean_audit` fields and stored its Lean statement verbatim;
restored repository formatting for unchanged parent metadata; clarified the old
direct dependency's relocation in `No longer needed`. No Lean proof, signature,
definition or import needed repair.
