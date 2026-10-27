## What changed

Proved `AlgebraicGeometry.ProEtale.coefficientFixed_closed_unit_epi` without changing
its statement or either public adjunction definition. All new helpers are private and
proved. No adopted source-library file is changed.

The existing open-closed exact-sequence theorem and module detection theorem fix the
coefficient universe to `u+1`, so they cannot simply be instantiated here. The proof
reuses their existing arguments in `max v (u+1)`: construct original-site sheafification
by transport from AsSmall, use the affine closed-site adjunction to prove the closed
counit invertible, and prove finite quasi-compact joint detection directly from filtered
module colimits and sheaf separatedness. Open restriction of a closed direct image
vanishes by evaluation on empty base changes. Cancellation then proves the unit epic.
Transport the adjunction to the coefficient-sized sites and use uniqueness of left
adjoints, including its unit identity, to obtain the exact canonical unit in the goal.

Mathlib leanfinder, loogle, and grep searches found generic categorical epimorphism
criteria but no theorem for this coefficient-sized closed unit. The adopted source
arguments above supply the geometric content. Both added proof imports are private;
the original public import is unchanged.

The unit's constructible-comparison route is preserved. This establishes its required
epimorphism; it does not replace the unit's induction or extension-by-zero steps.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.ProEtale.coefficientFixed_closed_unit_epi`
(node `lem-pe-coefficient-fixed-closed-unit-epi`). Added 0 holes. There are no remaining
`sorry` declarations in the delivered Lean module and no split-off modules.

Validation: the complete module compiled through `lcompile.py` without errors or
warnings in 23.1 seconds, below the 60-second delivery limit. The original theorem
signature and both public adjunction definitions were compared verbatim and are unchanged.

## No longer needed

The proof does not need `lem-sf-proetale-open-closed-sequence` or its module
`Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequence`: epimorphy alone follows by
cancellation and joint detection, without constructing the full exact sequence.
Removed this proof-dependency edge from the item's node. That module was not imported
in the original item, so there is no corresponding Lean import to delete. Other users
of that theorem remain unchanged. No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original node cites the smaller-universe open-closed sequence as if it applied
directly to the independent coefficient universe. Its mathematical argument remains
valid, but the existing Lean declaration is not universe-polymorphic enough for that
application. The delivered private proofs supply that universe generalization with no
new unproved interface. The full exact sequence and the principal-open/closed-localization
cover are unnecessary for proving just epimorphy.

Edge cases checked in the argument: no nonempty scheme, nonempty open, reducedness,
or splitting of the closed immersion is assumed. The empty-open and empty-closed cases
use the same finite-family detection and empty-cover calculation. No finiteness of the
coefficient ring is used.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
