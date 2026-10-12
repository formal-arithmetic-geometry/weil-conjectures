## What changed

Proved `AlgebraicGeometry.Proj.homogeneous_basis_proj_coproduct` with its signature
unchanged. Extract the finite-coproduct charts directly from `finite_twist_coproduct_fractions`, prove
both directions of the numerator-degree comparison under `b.equivFun`, and apply the
new proved chart-comparison theorem.

Added two proved modules: `HomogeneousBasisCoordinates` proves the algebraic forward
implication by internal degree projections and homogeneous polynomial components;
`GradedChartComparison` constructs localized chart equivalences, proves their scalar
and restriction compatibility, and glues them using the existing basis-extension
universal property. Its private `iso_of_basis` helper is fully proved.
Updated the parent node to match this route. No definition or existing statement changed.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.Proj.homogeneous_basis_proj_coproduct`.
Added zero holes; no `sorry` remains in any delivered Lean file.
Also proved `AlgebraicGeometry.Proj.homogeneous_basis_coordinates`
(node `lem-sc-p1-homogeneous-basis-coordinates`) and
`AlgebraicGeometry.Proj.graded_chart_comparison`
(node `lem-sc-proj-graded-chart-comparison`).

The proof uses existing staged declarations: `finite_twist_coproduct_fractions`,
`standardOpenProperties`, and `exists_sheafOfModules_from_basis`.
Their existing transitive holes remain other items; this delivery does not claim an
axiom-free transitive closure for the parent.
Local compiles validate all three modules in import order; explicit scratch-copy
`#print axioms` checks show only the three permitted axioms for the coordinate lemma,
and those plus `sorryAx` for the comparison, its private helper, and the parent.
The latter comes from existing open dependencies. The delivery tool supplies the
final declaration-wide axiom probe and preflight; server compilation is deferred
to the global build under the current tool configuration.

## No longer needed

Removed the parent's direct proof imports of
`Sheaf.AlgebraicGeometry.ProjStandardOpenProperties` and
`Sheaf.Topology.SheafOfModulesFromBasis`; these are still needed transitively by
`GradedChartComparison`, and their nodes are not globally pruned.
Removed `Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist` in favor of the direct
`Sheaf.AlgebraicGeometry.ProjFiniteTwistCoproductFractions` theorem. The old parent
proof dependency `lem-sc-p1-proj-shifted-free-twist` is no longer used by this proof.
The old dependencies `lem-weil-pbc-proj-standard-open-inclusion` and
`lem-weil-pbc-sheaf-of-modules-from-basis` remain used through the comparison lemma.
No globally unreachable module is claimed: other consumers can still use the old route.
No projective-line chart comparison, transported glued twist, stalk chart map, or
`ProjTildeFunctorial` theorem is needed by the comparison argument.
The new comparison module imports only Mathlib scheme-module definitions and the
fraction definition publicly; it does not import `ProjGradedModuleSheafExists`.

## Where the brief, the DAG or earlier work was wrong

The plan is mathematically correct, but its first step and localized chart comparison
were not supplied as ready-to-apply Lean declarations. Both are now formalized and
proved. No statement dispute or change is necessary. The unit's route is unchanged.
The first worker used the larger `proj_shifted_free_is_twist` clause because the
direct coproduct theorem was initially unavailable locally. On second reading its
compiled artifact is available, so the direct theorem replaces that route.
LeanSearch returned HTTP 500; LeanFinder, Loogle and source grep provided the primitives.

## New nodes

`lem-sc-p1-homogeneous-basis-coordinates` records only the algebraic coordinate-degree
implication, in `lean/Sheaf/AlgebraicGeometry/ProjectiveSpace/HomogeneousBasisCoordinates.lean`.
It has no proof dependency outside Mathlib, handles every integer degree and the empty
basis, and is proved without `sorry`.

`lem-sc-proj-graded-chart-comparison` records the general comparison from two given
fraction-chart systems and a numerator-degree-preserving linear equivalence, in
`lean/Sheaf/AlgebraicGeometry/ProjectiveSpace/GradedChartComparison.lean`. It assumes no
basis, twists, internal grading or stalk data, and is proved from the existing standard
open and sheaf-on-basis declarations. No change record is required.

## Second reading by J3

1. Compared the parent with the repository using `diff -u`: its existing declaration
   signature and docstring are byte-for-byte unchanged. Only proof imports and the
   proof body differ. The other two modules and nodes are new; no definitions or
   existing statements were changed, and no change record is needed. Verdict: pass.
2. Compiled all three modules in import order without errors or warnings (comparison
   25.3 s, coordinates 3.8 s, parent 5.7 s before the shorter route; revised parent
   3.9 s). Searched all delivered Lean sources for prohibited declarations and holes:
   none. Explicit axiom checks cover all public theorems and private `iso_of_basis`;
   only permitted axioms and existing-dependency `sorryAx` occur. Verdict: pass.
3. Read both new statements against their proofs: coordinates uses only internality,
   scalar compatibility, and basis expansion; comparison uses range equality in both
   directions, scalar linearity, fraction representatives, and restriction formulas.
   Neither restates the parent. Checked the empty basis, zero vector, negative and
   zero shifted degrees, and the zero-polynomial/empty-open chart: no excluded case
   or extra assumption is needed. Arbitrary numerator sets in the comparison are
   sufficient because its hypotheses supply the chart groups. Repeated LeanFinder
   searches for internal grading/coefficient degrees and basis section isomorphisms,
   Loogle for localized equivalences, and `rg` over Mathlib, upstream, and `lean/`:
   found useful primitives but no exact duplicate. Both new lemmas are proved, with
   complete source/proof docstrings and matching nodes. Verdict: pass.
4. Read from the parent downward. Replaced the larger shifted-free theorem with the
   now-available direct `finite_twist_coproduct_fractions`; this avoids unused chart
   and glued-twist comparisons. All new proof-only imports are plain `import`; the
   new public imports supply signature data. The original two basis/gluing dependencies
   remain transitively needed and are explicitly accounted for above. Read
   `dag/units/sk-thm-picard-duality.json`: neither helper realizes a unit step, and
   the proof retains the homogeneous-coordinate, fraction-chart, and basis-gluing
   route beneath that unit. Its `realized` fields are unchanged. Verdict: pass.
5. Compared node signatures with the Lean and their `proof_deps` with the union of
   proof-step uses. The parent uses the coordinate lemma, direct coproduct charts,
   and comparison lemma; comparison uses standard opens and basis extension;
   coordinates uses Mathlib primitives. Both new nodes carry source, creation,
   blueprint, chapter/unit, search and Lean records. Updated the parent's proof,
   dependencies and origin for the shorter route. Verdict: pass.

Second reading changed the parent's chart-source import and application, its DAG
proof route, and this report. No new holes; the one original hole is closed.
