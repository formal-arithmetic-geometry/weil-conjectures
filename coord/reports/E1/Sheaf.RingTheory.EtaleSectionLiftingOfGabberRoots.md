## What changed

Replaced the first worker's near-complete decomposition statement with the earlier integral
idempotent localization construction, in the new module
`Sheaf.RingTheory.GabberIntegralSectionFactor`. The existing target now explicitly derives
flatness and finite presentation from étaleness, applies
`RingHom.zariskiPair_flat_integral_finitePresentation_isIso`, inverts the bijective structure
map, and checks the reduction equality using the compatible localized section.
The existing target signature and docstring are byte for byte unchanged. No definitions changed.

## Proved and sorry left

`Algebra.exists_etale_section_lift_of_gabber_roots` is proved from the split construction and
existing library statements (1 of 1 original theorem bodies closed). Its axioms still include
`sorryAx`, so the full mathematical result is not yet closed.
The sole sorry introduced is `Algebra.exists_gabber_integral_section_factor`, node
`lem-weil-pbc-gabber-root-criterion-integral-section-factor`, in its own module. It has a complete
source-based construction proof in its docstring. The rejected
`Algebra.exists_gabber_etale_decomposition` and its undelivered node were removed.

## No longer needed

Removed these direct imports from the target module:
- `Sheaf.Paper.IntegralClosureFiniteFibrePartLocalization`
- `Sheaf.RingTheory.EtaleSectionIdempotentSplitting`
- `Sheaf.RingTheory.FiniteGabberPolynomial`

They remain imported by the split construction module. The old direct proof dependencies
`lem-weil-pbc-etale-ring-base-change`,
`lem-weil-pbc-etale-section-idempotent-splitting`,
`lem-weil-pbc-integral-closure-finite-fibre-part-localization`,
`lem-weil-pbc-finite-of-integral-generators`, and
`lem-weil-pbc-zariski-pair-finite-gabber-polynomial` moved to that node. No original dependency
is pruned from the transitive route. The original finite-presentation/localization, flatness,
and Zariski-pair isomorphism dependencies remain direct dependencies of the target.

## Where the brief, the DAG or earlier work was wrong

The first worker postponed an equivalence with the A-factor whose projection already supplies
the desired lift. This did not isolate a useful strict part of the argument. Its new node had
an empty proof dependency list despite hiding all the original construction, and its short
ordinary comment was not a theorem docstring with a complete proof. The report's claim that
there were eight detailed dependency modules was inaccurate: several dependencies are Mathlib
leaves. The revised split stops before the substantive final Zariski-pair isomorphism step.
The original nine-step mathematical plan is valid and retained, rather than declared too large
and replaced by the same result under a stronger output type.

## Second reading by E1

1. Compared both delivered modules against the repository. Only the target module previously
existed. Its original declaration signature and docstring are byte-identical; only its proof
and plain proof imports changed. The new statement has its own new module and node. No
statement correction or change record is required.
2. Compiled both modules locally in import order. The target has no sorry in its body; the only
new sorry is the named integral-factor construction. No forbidden declaration or hollow
definition occurs. Scratch `#print axioms` checks allow only propext, Classical.choice,
Quot.sound and sorryAx from the remaining construction and existing open dependencies.
3. Checked the split construction against Stacks 09XI (5) implies (2), including the integral
closure, finite subalgebra, polynomial idempotent and compatibility arguments. Checked I=0
(the chosen section already cuts out A), B=A (e=1), product factors, and the zero ring
(I=top is allowed by the Jacobson hypothesis only in the zero ring). The statement does not
assert bijectivity of the structure map before the final theorem. Independent LeanFinder,
Loogle and grep searches found no duplicate; LeanSearch was attempted and returned a service
Internal Server Error, recorded as unavailable without a verdict; existing dependencies provide earlier steps.
4. The target now uses the existing Zariski-pair theorem and Mathlib flatness/localization
instances. The construction retains all earlier dependencies. Imports are public only for
statement requirements and plain for proof requirements. The No longer needed list records
every moved old dependency. Read `dag/units/sk-thm-p1.json`: its realized steps and the
henselian/finite-etale route remain unchanged; no unit step is bypassed.
5. The target node records exactly the integral construction, Zariski-pair isomorphism, and
inversion/reduction steps now written in Lean. The new node records the original construction
steps and their dependency union, source, searches, chapter/unit, blueprint origin, creator,
and verbatim Lean statement. Removed the first worker's inaccurate decomposition node.

Changed in this second reading: replaced the near-restatement by a strict integral-factor
construction, formalized the final isomorphism and lifting steps, supplied the new theorem's
full docstring and node, corrected dependency records and pruning report, and moved the
construction imports to its own module.

## New nodes

`lem-weil-pbc-gabber-root-criterion-integral-section-factor` records
`Algebra.exists_gabber_integral_section_factor` in
`lean/Sheaf/RingTheory/GabberIntegralSectionFactor.lean`. It isolates steps 1–7 of the original
plan and compatible quotient/localization maps, leaving the final rank-one/isomorphism
argument in the target proof. Source checked at https://stacks.math.columbia.edu/tag/09XI.
No change records.
