## What changed

Replaced the `sorry` in
`Algebra.exists_relativeGlobalCompleteIntersection_of_syntomicAtPrime` by a complete
Lean reduction, preserving its signature and existing public imports. Added two new
statement modules, each containing one named obligation with its source and full
natural-language proof. The original node now records the implemented reduction;
the two new nodes retain the relevant steps of its source proof.

The original module proves the remaining combination itself: flatness after principal
localization; extracting a specified Fin-indexed presentation from the intrinsic predicate;
principal localization of that presentation using the existing theorem; extending the
canonical comparison isomorphism to localizations; swapping two principal localizations;
and clearing the final denominator using `IsLocalization.Away.sec` and associated elements.
No new hole is used for this combination. In particular the Option-indexed output of the
existing equation-count theorem is consumed without changing its interface: its intrinsic
predicate supplies a Fin-indexed presentation, and the existing principal-localization
lemma supplies the final specified presentation.

Local compilation uses only the prescribed `lcompile.py`. The initial complete reduction
compiled; a subsequent refinement proved the local-flatness transport directly and removed
that assertion and hypothesis from the first remaining obligation. The completed set is
checked again by the delivery dry run. No target, existing definition, statement, or module
held by another group is changed.

## Proved and sorry left

Closed the original hole:
`Algebra.exists_relativeGlobalCompleteIntersection_of_syntomicAtPrime`
(node `lem-weil-pbc-syntomic-at-prime-relative-global-complete-intersection`).
There are no `sorry`s in the delivered original module or its private helpers.

Added exactly two holes:

- `Algebra.exists_completeIntersection_fibre_away`, in
  `Sheaf.RingTheory.SyntomicPrincipalLocalizationHypotheses`, node
  `lem-weil-pbc-syntomic-principal-localization-hypotheses`.
  This only transports the fibre neighbourhood across a prescribed localization;
  it does not assert a relative complete-intersection presentation and does not
  assume or conclude flatness or finite presentation.
- `Algebra.exists_equationCount_comparison_of_syntomicAtPrime`, in
  `Sheaf.RingTheory.SyntomicEquationCountComparison`, node
  `lem-weil-pbc-syntomic-equation-count-comparison`.
  This constructs the comparison quotient, its canonical local isomorphism, and
  the local equation-count dimension. It assumes actual finite presentation,
  and does not assert the global fibre condition or the final presentation.

This is a decomposition, not an axiom-free proof of the mathematical theorem:
one upper hole closed and two strictly partial lower obligations added. It also uses
existing holed equation-count and relative-principal-localization theorems as intended
by stage 3. No data definition chooses an arbitrary witness from a holed existence theorem.
The equivalence from the holed bijectivity conclusion is the inverse of a specified
canonical map, hence determined uniquely.

Edge cases checked in the new statements: no positive lower bound on n or c is
introduced; n = c = 0 and c = 0 remain allowed. A prime excludes the zero ring,
and its canonical fibre prime makes that fibre nonzero. Localization at g = 1
recovers the original fibre hypothesis. The numerator argument works with exponent
zero and with zero divisors; it uses association and localization, not cancellation
in S. No global flatness assumption on S is introduced.

## No longer needed

Removed the following direct proof imports from the original module:

- `Sheaf.RingTheory.GlobalCompleteIntersectionPrincipalLocalization`
- `Sheaf.RingTheory.LciConormalFreeRankCodimension`
- `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`
- `Sheaf.RingTheory.PolynomialQuotientDimensionAtPointHeightDifference`
- `WeilConjectures.Mathlib.Topology.KrullDimension`

The first four nodes are still needed by the two lower obligations' recorded proofs;
they are not claimed as permanently pruned mathematical work. The dimension definition
is visible through the statement imports of the comparison and equation-count modules,
so it needs no additional direct import. No blueprint unit statement or realized step
was bypassed. No permanently unnecessary node or module was identified.

Added proof-only imports of the two new modules. Retained the existing equation-count
and relative-principal-localization imports because the proof actually applies both.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original eleven-step route is retained, with its
initial fibre transport and comparison construction now exposed as two independent
obligations and its final combination implemented in Lean. Local flatness transport
can be proved directly from Mathlib's flat localization map, localRingHom, composition,
and localRingHom_comp; it needs no additional obligation or residue-field isomorphism.

The local literature checkout does not contain `literature/stacks-project/algebra.tex`.
I read the source proof at https://stacks.math.columbia.edu/tag/00SY instead; its
presentation, conormal basis, flat tensor sequence, Nakayama and further-localization
paragraphs agree with the recorded route. Existing project source identifiers remain
in the node records. LeanSearch returned an Internal Server Error; the searches record
that as unavailable, not as a negative result. LeanFinder, Loogle, local source grep
and blueprint searches were completed; they found tools for smoothness and localization,
but no theorem stating either new obligation.

## New nodes

`lem-weil-pbc-syntomic-principal-localization-hypotheses` records the complete-intersection
fibre transport in original step 1. Its proof identifies the localized prime and residue
fields, tensors the principal localization, interchanges localization at the fibre
witness with localization at 1 tensor g, and applies the existing complete-intersection
principal-localization result. Module:
`lean/Sheaf/RingTheory/SyntomicPrincipalLocalizationHypotheses.lean`.

`lem-weil-pbc-syntomic-equation-count-comparison` records original steps 2–9: presentation
and fibre; conormal rank and choice of equations; flatness and Nakayama for the comparison
kernel; clearing its finitely many generators; and the local fibre dimension via the
height-difference comparison. Module:
`lean/Sheaf/RingTheory/SyntomicEquationCountComparison.lean`.

Both inherit the item's chapter and unit, include three kinds of searches (with the
LeanSearch service failure stated explicitly), and have no relative-global-complete-
intersection conclusion. There are no change records or forced adaptations.

## Second reading by T3

1. **Comparison with the repository.** I diffed the delivered original module against
the repository version. The target signature and every existing declaration signature
are unchanged; the only edits are proof code and proof-only imports. The two additional
modules are new split-off statements, as declared above.
2. **Proof and kernel checks.** I compiled all three modules with `lcompile.py --all`.
The original target module has no `sorry`, axiom, unsafe, opaque, extern, or
implemented-by declaration. The only remaining `sorry`s are the two named split-off
theorems, each with a source docstring and a matching DAG node. Their use is explicit
decomposition of the original proof, not a hollow definition.
3. **Truth and strength of new statements.** I checked the hypotheses and conclusions
of both split-off statements against the source route and their edge cases. The fibre
transport statement adds no flatness or finite-presentation assumption; the comparison
statement assumes finite presentation and concludes only the local quotient comparison
and equation-count identity. Neither restates the target.
4. **Shortest route and pruning.** The target proof uses the existing localization and
relative-principal-localization results, and transports flatness directly through the
localization map. The five direct imports removed from the old proof are no longer used
by the target; the required lower obligations retain their own recorded dependencies.
5. **DAG and unit route.** The original node's proof and proof dependencies match the
Lean reduction, and both new nodes record their declarations, sources, searches, and
partial proof routes. The unit's statement and realized steps remain in use; no chapter
or unit route was bypassed.

I changed only this report after the first reading: added this required second-reader
record. No Lean source or DAG content was altered during the second reading.
