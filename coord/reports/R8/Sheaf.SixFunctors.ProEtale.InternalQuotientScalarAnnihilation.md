## What changed

Replaced the proof of `AlgebraicGeometry.ProEtale.InternalCompletionTransport.quotient_scalar_annihilation` in `Sheaf.SixFunctors.ProEtale.InternalQuotientScalarAnnihilation`. The statement and all public imports are unchanged. Proof imports supply the discrete quotient comparisons, the existing principal-kernel calculation, scalar restriction under section reconstruction, and tensor-section calculus.

The argument first proves that a residue-zero section has zero positive power in the actual discrete finite quotient. It constructs the finite quotient module structure on each transported tensor term by extension of scalars and the commuting constant-to-continuous coefficient square. The scalar therefore kills the entire quotient term. Naturality of the unit-endomorphism action and an explicit degreewise tensor-unitor calculation give the claimed composite.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.InternalCompletionTransport.quotient_scalar_annihilation` (one original hole).

Added: none. Remaining in the item: none. All supporting helpers are private and proved.

Validation: `lcompile.py` compiled the complete proof in 38.0 seconds. Profiling commands were removed before delivery.

## No longer needed

The proof does not invoke `ProEtaleIntegralCoefficientLimit.sfb_integral_coefficient_limit` (`det-prop-sfb-qlbar-colimit-x-integral-limit`): the coefficient square follows directly from the point comparison on constants and the sheafification adjunction. It also needs no Koszul cone comparison theorem: the public `RingedSingletonKoszulCone` import remains necessary for the definition of `ringedSingletonKoszulPower`, while its cone theorem is unused. No existing module is withdrawn and no public import is removed.

## Where the brief, the DAG or earlier work was wrong

No statement correction is required. The planned local divisibility argument can use the existing sectionwise kernel equality directly. Killing the entire finite quotient term avoids any calculation with the particular quotient-unit map and does not require flatness, boundedness, regularity, or a noetherian scheme hypothesis.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
