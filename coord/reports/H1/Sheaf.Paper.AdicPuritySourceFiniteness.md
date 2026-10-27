## What changed

Replaced the sorry in `WeilConjectures.purAdicSource_finiteness_reductions` by a complete
Lean assembly from the library's finite/integral pullback and twist preservation
results, shift comparisons, and two strictly smaller compatibility statements.
The supplied cohomological and Tor intervals remain separate, with the exact -2d shift.
The canonical twist reduction is identified with an inverse mate along twist
equivalences, rather than replaced by an unspecified isomorphism.

Moved the ten existing normalization declarations, including the already proved
`purAdicFiniteSourceNormalization_existsUnique`, verbatim into
`Sheaf.Paper.AdicPuritySourceNormalization` and publicly re-exported that module.
This permits the transition-square lemma to depend on the normalization data without
an import cycle. The main theorem's signature, every moved definition, and every
consumer signature remain unchanged. Change record:
`coord/changes/H1-adic-source-normalization-module.md`.

Earlier validation: the main theorem compiled cleanly in 47.7 seconds after profiling and
limiting unfolding of derived scalar packages locally. Text comparison confirmed the
main theorem signature and all moved declaration bodies are verbatim. Both new step
statements compile; their edge cases include equal indices, d = 0, f = id, K = 0,
the empty scheme, and arbitrary ramification of E. No flatness of a quotient map is
assumed. Repair validation: restriction coherence compiled in 1.6 seconds and the proved
transition-cocycle module compiled cleanly in 5.2 seconds. The full packet is checked
again in dependency order and by delivery preflight.

## Proved and sorry left

Original delivery: one original hole closed,
`WeilConjectures.purAdicSource_finiteness_reductions`.
The refreshed item already contains that proof and has zero holes.
This repair closes the prior split hole
`WeilConjectures.integralReductionTransition_cocycles` and adds one smaller hole
`WeilConjectures.integralReductionRestriction_coherence`; the whole packet still has two holes.
Its finiteness, exact bounds, reduction invertibility, adjunction transposition, and
transfer of identity/composition equations are assembled in Lean.

Two holes remain in the whole packet, both public named theorems in separate modules:

- `WeilConjectures.purAdicSourceReduction_transition_square`, node
  `lem-pur-adic-source-transition-square`: only compatibility of the specified
  source comparison with a single arbitrary quotient.
- `WeilConjectures.integralReductionRestriction_coherence`, node
  `lem-pur-integral-reduction-restriction-coherence`: identity and composition of
  finite-to-completed restriction comparisons on arbitrary finite-coefficient objects.

The previously split `WeilConjectures.integralReductionTransition_cocycles` is now
proved from this strictly smaller restriction identity using adjunction naturality.
It contains zero sorry.

The item, normalization, and transition-cocycle modules contain zero sorry. This is a decomposition
of one original hole into two strict step lemmas, not a complete proof from closed
premises and not a claimed net reduction in the sorry ledger. No definition contains
sorry; all chosen data retain their original uniquely determining theorem.

## No longer needed

No module is withdrawn. The transport unit and its realized source-object step stay.
The main proof does not directly need the old private imports
`SemilinearDerivedSections`, `IntegralLineDerivedComparisons`,
`IntegralLineReductionRestriction`, `IntegralOperationRoosEffectivity`,
`IntegralOperationsPreserveConstructible`, `PurTwistSheafLocallyFree`,
`PullbackTorAmplitude`, `SuccessiveDerivedQuotientNormalization`,
`NormalizedDVREffectivity`, `AdicPurityFiniteTensor`, `AdicPurityRootComparisons`,
`DerivedScalarExtensionRestrictionAdjunction`, `ProEtaleConstantExact`, or Mathlib's
`ShortComplex.PreservesHomology`. Necessary declarations from some of these remain
available through public imports of the actual dependencies.
The transition-square split retains the needed line/Roos/balancing facts in its DAG
proof; those facts are not claimed globally pruned. The shorter inverse-mate argument
avoids a second construction of the integral twist comparison. Public dependencies
remain available through the original module's re-exports.

Obsolete direct tool approvals removed from the item node (some remain needed below
the split):

- `lem-sf-pullback-tor-amplitude`
- `lem-pur-integral-operations-preserve-constructible`
- `lem-pur-twist-sheaf-locally-free`
- `lem-pur-integral-line-reduction-restriction`
- `lem-pur-integral-line-derived-comparisons`
- `lem-weil-derived-scalar-extension-restriction-adjunction`
- `lem-sfb-successive-derived-quotient-normalization`
- `lem-coef-semilinear-derived-sections`
- `lem-coef-normalized-dvr-effectivity`
- `lem-pur-integral-operation-roos-effectivity`

## Where the brief, the DAG or earlier work was wrong

The planned compatibility argument had no published declaration of the complete
semilinear square for the actual independently specified finite-source normalization.
It is now a precise strict step, with the original counit, tensor, root-quotient and
scalar-adjunction argument recorded in its docstring and node. The general integral
transition cocycle also lacked a published theorem in the required coordinates.
These are not renamed copies of the original six-conjunct conclusion.

Repair of return 500b4fda934: the shared Lean sources refreshed during the repair
and now contain the previous packet, explaining the same-text return. Compared
against those current sources, the substantive change proves the formerly split
transition-cocycle theorem, replacing its obligation by the strict restriction-
comparison step. The item proof consumes its two equations explicitly. This is not
an unchanged re-push or a rebase alone; the previous decomposition is retained.

The newest blueprint places the relevant compatibility in transport Step 1 and the
integral coefficients in Step 2; the retained source-object argument in the existing
node supplies the detailed split sources. No assertion is marked disputed.

## New nodes

`lem-pur-adic-source-transition-square` owns
`Sheaf.Paper.AdicPuritySourceTransitionSquare`. It is just the semilinear quotient
square; no finiteness, invertibility, or cocycle conclusion is included.

`lem-pur-integral-reduction-transition-cocycles` owns
`Sheaf.Paper.IntegralReductionTransitionCocycles`. Its theorem is now proved by
adjunction transposition from the restriction-comparison coherence statement.

`lem-pur-integral-reduction-restriction-coherence` owns
`Sheaf.Paper.IntegralReductionRestrictionCoherence`. It states just the identity and
composition comparison equations on finite-coefficient objects, without integral
objects, adjunction units, or reduction transitions. Equal indices reduce to identity
comparisons, zero objects to zero morphisms, and all coefficient ramification is
allowed because no flatness is used.

All split statements were searched using LeanSearch, LeanFinder, and Mathlib grep through msearch;
no matching derived sheaf statement was found. The existing normalization definition
node's Lean attachment moves to the new dependency module; no new duplicate definition
node is introduced. Generic tool uses in the assembly are all-stage pullback finiteness,
finite ctf triangulated shift bounds, completed pullback counits, and inverse-mate
invertibility, serving the unchanged unit route.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
