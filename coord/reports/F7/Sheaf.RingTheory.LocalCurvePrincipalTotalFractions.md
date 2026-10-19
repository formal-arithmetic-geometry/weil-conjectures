## What changed

Proved `IsLocalRing.exists_parameter_principal_total_fractions` in
`Sheaf.RingTheory.LocalCurvePrincipalTotalFractions`, preserving its signature and docstring.
The existing six-step argument is realized entirely using Mathlib:

1. `Ideal.exists_finset_card_eq_height_of_isNoetherianRing` and
   `IsLocalRing.maximalIdeal_height_eq_ringKrullDim` give a singleton parameter set.
   Minimality over its span and the local-ring prime bound give its radical.
2. Strict monotonicity of prime heights shows that every nonmaximal prime is minimal;
   the maximal ideal has height one and therefore is not minimal.
3. `Ideal.iUnion_minimalPrimes`, reducedness, and avoidance show that the parameter is regular.
4. The map is exactly the canonical `IsLocalization.Away.liftAlgHom` in the statement.
5. A prime containing a regular denominator cannot be minimal, so it must be the maximal
   ideal. `Ideal.radical_eq_sInf` puts the parameter in the denominator's radical and
   therefore gives divisibility of some parameter power. This works for units as well,
   without needing a separate unit case.
6. `IsLocalization.of_le_of_exists_dvd` equips the principal localization with the
   total-fraction localization property. `IsLocalization.bijective` proves bijectivity
   of the stated map; its compatibility with the base-ring maps is `AlgHom.commutes`.

Read Stacks `varieties.tex`, `lemma-pre-pre-delta-invariant` (Tag 0C3R), and the Mathlib
signatures recorded by the four stated proof-dependency leaves. The unit route is unchanged.
Searches through msearch LeanFinder, Loogle, and grep found no whole-item shortcut; Loogle
and grep identified the localization comparison API used for the existing final step.
Rechecked the retained proof against the current source and dependency signatures on
2026-10-19. The current single-file lcompile run succeeded without warnings in 2.0 seconds.

## Proved and sorry left

Closed the one original hole:
`IsLocalRing.exists_parameter_principal_total_fractions`
(node `lem-exc-local-curve-principal-total-fractions`).

Holes closed: 1. Holes added: 0. Sorries left in the delivery: 0. No split-offs.
The proof uses Mathlib only; it imports no project theorem containing an admitted proof.

## No longer needed

Removed the unused proof imports `Mathlib.RingTheory.LocalRing.Quotient` and
`Mathlib.RingTheory.Spectrum.Prime.Topology`.

No declared dependency nodes or project modules are pruned. All stated mathematical
proof dependencies remain used, through their Mathlib leaf declarations and localization
constructions. No finite-product decomposition or auxiliary project module is required.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The parameter, prime-height, reducedness,
radical, and localization arguments in the DAG suffice without new nodes or repairs.
An initial compile-server request received no answer within 218 seconds; retrying
returned normal Lean diagnostics, and the final compile succeeded.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
