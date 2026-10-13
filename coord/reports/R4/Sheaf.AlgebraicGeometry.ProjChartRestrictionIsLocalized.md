## What changed

Proved `AlgebraicGeometry.Proj.gradedModuleChart_restriction_isLocalized` in
`Sheaf.AlgebraicGeometry.ProjChartRestrictionIsLocalized`, preserving its original
signature and visibility. Four private, fully proved helpers handle canonical ring
constants, pullback of constants, the principal homogeneous chart and its transition
power, and additive/scalar transport of module sections. The main proof constructs
the linear equivalence through theta, identifies l with the canonical localization
map followed by its inverse, and transfers localization from r^deg(f) to r.

The DAG proof records these same three steps. All public imports and existing
instances, definitions, options, and docstrings are unchanged. The only new option
is scoped to the private ring-constant helper and controls definitional equality.
No axiom, definition with postponed data, or additional public declaration is added.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Proj.gradedModuleChart_restriction_isLocalized`
(node `lem-weil-pbc-proj-chart-restriction-is-localized`).

No sorry remains in the delivered module; no holes are added or split off.
This is a complete proof, not a decomposition onto unproved statements.
The proof uses only Mathlib and the module's supplied hypotheses.
Second-reader single-file compilation passed without warnings in 49.4 seconds.
A scratch copy with `#print axioms` compiled in 47.3 seconds and reported only
`propext`, `Classical.choice`, and `Quot.sound` for the public theorem.
The delivery dry run runs the compiler and axiom probe; its result is recorded
by the delivery tool.

## No longer needed

None. No imports are added or removed and no planned DAG dependency is pruned.
`lem-weil-pbc-proj-basic-open-intersection` remains used through its Mathlib
chart-membership and basic-open multiplication formulas. The proof needs no
additional Sheaf or WeilConjectures module. The private principal-chart calculation
in `ProjGradedModuleChartBasisComparisonFixedGenerators` was useful to read, but its
module is not imported or needed as a proof dependency.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The DAG's second step was labeled elementary but requires
substantial section transport and comparison of canonical ring maps. These are now
proved directly. Canonical ring-map uniqueness at each projective point avoids an
explicit fraction expansion in that step. Empty charts, zero rings, nilpotent r,
r=0 and unit r require no added assumptions: the pointwise and cofinal-submonoid
arguments cover them uniformly. The unit's route is unchanged.

Searches before proving: Lean Finder returned projective structure-sheaf and tilde
localization maps, but no exact arbitrary-module restriction theorem; Loogle returned
IsLocalizedModule and its universal-property declarations; grep found the private
principal-open chart calculation and Mathlib's of_linearEquiv/of_exists_mul_mem.

## Second reading by R4

1. **Visible declarations: PASS.** Read the repository/sandbox module diff and
   compared the existing theorem signature byte for byte. All hypotheses, the
   conclusion, visibility, local scalar-action instance, original options,
   notations, and public imports are unchanged. Only four private proved helpers
   and the original theorem's proof are added. There are no statement/definition
   changes, change records, or forced adaptations.
2. **Proof and axioms: PASS.** Read the whole proof, compiled the delivered file
   using lcompile.py without errors or warnings, and compiled a scratch copy
   with `#print axioms AlgebraicGeometry.Proj.gradedModuleChart_restriction_isLocalized`.
   Its axioms are exactly propext, Classical.choice, Quot.sound; there is no
   sorryAx. Scanned the delivered Lean for sorry and forbidden declarations:
   none occurs. beta is explicitly constructed from restriction isomorphisms and
   alpha; psi is explicitly constructed from beta and theta. Witnesses from
   homogeneous fraction surjectivity come from a proved Mathlib theorem, not an
   unproved mere-existence assertion.
3. **Split statements: PASS (none).** No theorem is left sorry, and no public
   statement or node is added. The private helpers are proved strict parts of
   the argument. Checked the fraction calculation when n=0 and deg(f)=1:
   g=f*a still has positive degree and U=r^deg(f). Zero rings, empty charts,
   r=0, nilpotent r, and unit r require no cancellation or nonzero hypothesis.
   The final multiplier r^(n*(deg(f)-1)) works also when n=0 or deg(f)=1.
4. **Shortest route, imports, and unit: PASS.** Independently searched Loogle
   with `IsLocalizedModule, LinearEquiv`, read of_linearEquiv and the cofinal
   transfer lemma in Mathlib, and searched the library for localization of
   restrictions and principalOpen_chart. The existing chart helper is private
   and supplies only the open equality, not the required transition power;
   importing its module would add an unnecessary dependency. The proof already
   uses Mathlib's standard localization instances and transfer lemma instead of
   reproving the three universal-property conditions. Both public imports are
   needed by the original public signatures/instance. The sole old proof
   dependency, lem-weil-pbc-proj-basic-open-intersection, remains realized by
   its Mathlib chart-membership and basicOpen_mul formulas; nothing is pruned.
   Read dag/units/sk-thm-reduction.json, including realized: this tool lemma
   changes no unit statement, step, or realizing node, and keeps its three-step
   chart-localization route.
5. **DAG correspondence: PASS.** Compared both node JSON files. Only proof and
   proof_origin differ; proof_deps is unchanged and equals the union of step
   uses. Step 1 matches principalOpen_chart_power; step 2 matches the two
   constant helpers, transport helper, psi and heq; step 3 matches the positive
   degree/cofinal-submonoid argument. The Lean record's statement is unchanged.
   No new-node fields are needed.

Changes by the second reader: corrected the report's compile evidence and
appended this independent review. No Lean or DAG repair was necessary.
One original named hole is closed and zero holes are added: a proof, not a
decomposition. The dry run and delivery are executed with deliver3.py.
