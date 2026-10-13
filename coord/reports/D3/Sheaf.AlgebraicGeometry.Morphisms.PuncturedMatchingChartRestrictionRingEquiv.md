## What changed

Proved `AlgebraicGeometry.Scheme.CompletionGluingData.puncturedMatching_chart_restriction_ringEquiv`
in `Sheaf.AlgebraicGeometry.Morphisms.PuncturedMatchingChartRestrictionRingEquiv` without
changing its signature or visibility. Added proof-only imports of
`PuncturedCompletionFormalGlueingChart`, `PuncturedMatchingChartPowerLift`,
`FormalGlueingH0Localization` and `Mathlib.RingTheory.AdicCompletion.AsTensorProduct`.

Two proved private helpers identify the principal-open section localization and its image.
A third proved private helper obtains kernel torsion from the injectivity of the H0
localization comparison. It prepends f to a finite generating family, transports a zero
chart coordinate through the geometric H0 equivalences, clears the denominator, and
transports the scalar action back to the matching ring. Kernel torsion and the existing
power lift make both section rings localizations of the same matching ring. The localization
universal property makes the section map bijective; its inverse ring equivalence has the
requested numerator compatibility by `symm_apply_apply`.

Updated the existing node's proof, proof dependencies and proof origin to record this
argument. The unit statement and route are preserved. Sources checked directly:
[Stacks 0BLH](https://stacks.math.columbia.edu/tag/0BLH) and
[Stacks 05ER](https://stacks.math.columbia.edu/tag/05ER).

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.Scheme.CompletionGluingData.puncturedMatching_chart_restriction_ringEquiv`
(node `new-lem-sbc-punctured-matching-chart-restriction-ring-equiv`).
Added 0 holes. No sorry remains in the delivered module. All three private helpers are proved.
No new statements or modules with sorry are introduced; this is a proof from existing
named declarations, not a decomposition. Existing transitive dependencies retain their own
proof status.

The kernel argument uses only numerator injectivity of the localized H0 comparison, and
surjectivity uses the existing independent power-lift theorem. All localization APIs include
zero rings and empty charts. A nilpotent f gives zero localized rings. The generating family
is nonempty after prepending f, even when the maximal ideal is zero. No extra nonvanishing
or nontriviality assumption was added.

## No longer needed

None of the original imports or proof dependencies is removed. The second reading removed
the redundant added proof import `Mathlib.Data.Fin.Tuple.Basic`; its declarations are already
available through the remaining imports. No module is claimed globally pruned. The existing H0-localization dependency is retained. The proof does not import the
following downstream modules, since they depend on this item:
`PuncturedMatchingChartRestrictionLeftInverse`, `PuncturedMatchingChartSectionInjective`,
`PuncturedMatchingChartKernelTorsion`, `PuncturedCompletionMatchingAffineSectionsComparison`,
`PuncturedCompletionMatchingAffineSections`, or `PuncturedCompletionMatchingPuncturedIso`.
Their nodes are respectively `lem-sbc-punctured-matching-chart-restriction-left-inverse`,
`lem-sbc-punctured-matching-chart-kernel-torsion-injectivity`,
`lem-sbc-punctured-matching-chart-kernel-torsion`,
`new-sbc-punctured-completion-matching-affine-sections-comparison`,
`lem-sbc-punctured-completion-matching-affine-sections`, and
`lem-sbc-punctured-completion-matching-punctured-iso`. These remain downstream consumers,
not nodes removed from the target closure.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan omitted the geometric chart realization and the denominator
surjectivity needed to turn the module comparison into the displayed ring equivalence.
Both already exist as named declarations and are now recorded in proof_deps. Applying the
existing affine-section ring equivalence here would create an import cycle through this
item; instead the kernel calculation is proved locally from the acyclic H0 comparison.
No mathematical error or statement change was found. No interface change or forced
adaptation was needed.


## Second reading by D3

1. **Interfaces — PASS.** Diffed the only delivered Lean module against the repository.
   The existing public theorem signature, visibility, docstring, universe and section
   context are byte for byte unchanged. Only its proof, three proved private theorem
   helpers and proof-only imports were added. There are no definition changes, change
   records or forced adaptations. The existing node differs only in proof, proof_deps
   and proof_origin.
2. **Proof and axioms — PASS.** Compiled the complete module locally with lcompile.py
   without errors or warnings (21.3 seconds). A scratch copy printed axioms for all
   four declarations. The principal-open helpers use only propext, Classical.choice
   and Quot.sound. The kernel helper and public theorem additionally use sorryAx
   through existing imported dependencies, as permitted for still-open statements.
   No sorry occurs in this delivered module; no forbidden declaration or kernel
   bypass occurs. The proof introduces no data definition chosen from mere existence:
   the existential chart datum and localized map are eliminated inside a theorem
   proof, and the final ring inverse is obtained from proved bijectivity.
3. **Split statements and small cases — PASS.** There are no split-off statements,
   new public statements or new nodes. Read the three private helper proofs: the
   first transports the standard principal-open localization with its actual algebra
   map; the second computes the open image using hf; the third transports the zero
   chart coordinate through c and uses injectivity of the H0 localization map to
   clear a denominator. Nilpotent f and empty charts require no nontriviality;
   prepending f handles a zero-length original generating family. The resulting
   kernel assertion is precisely what equality clearing on b-c needs.
4. **Shortest route, imports and unit — PASS after import repair.** Read the chart
   realization, chart-power-lift and H0-localization declarations. The localization
   theorem supplies the exact numerator formula and injectivity used here; the
   power-lift supplies denominator surjectivity. Independently searched lean/ for
   localization and chart comparisons, and msearch.py loogle for
   IsLocalization.bijective (one exact generic API hit, already used). Similar
   private principal-open helpers in KernelTorsion and AffineSectionsComparison are
   inaccessible and lie downstream through RestrictionLeftInverse and SectionInjective;
   importing them would create a cycle. No original proof dependency is unused.
   The added Tuple.Basic import was redundant: the full scratch module without it
   compiled (22.1 seconds). The scratch module without AsTensorProduct failed exactly
   at Module.Flat A C, so that import stays. The other proof imports supply the named
   geometric and algebraic comparison theorems. Read sk-prop-input-spreading.json:
   its realized statement and step lists are currently empty; this below-unit
   argument changes none of its statement or steps and bypasses no realized node.
5. **DAG and sources — PASS.** The three new proof steps match, in order, the open
   localization, kernel calculation, and second localization followed by
   IsLocalization.bijective and symm_apply_apply. Their uses have exactly the recorded
   proof_deps union, retain the old H0-localization dependency, and add the actual
   matching-sections, chart-realization and power-lift nodes. No node statement,
   stmt_deps, unit, source, or lean signature record was altered. Read
   [Stacks 0BLH](https://stacks.math.columbia.edu/tag/0BLH), which constructs finite
   principal charts and their formal-gluing datum, and
   [Stacks 05ER](https://stacks.math.columbia.edu/tag/05ER), whose proof identifies
   each chart module with localized H0. These support the recorded local route.

Changed only the redundant added Tuple.Basic proof import and this report. No proof
repair or interface change was needed. One original hole is closed, zero holes are added;
no globally pruned module is claimed. This is a local closure using existing dependencies,
not a claim that the transitive proof is already free of sorryAx.
