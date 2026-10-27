## What changed

Proved `AlgebraicGeometry.isNoetherianRing_stalk_and_depth_eq_ringKrullDim_of_lci`
in `Sheaf.AlgebraicGeometry.LCICohenMacaulayStalks`, preserving its statement and all
public imports. No other library module is changed.

The proof follows all six steps of `lem-sfb-lci-cohen-macaulay-stalks`: choose an
lci affine chart through the arbitrary point; pass from S_p to (S_g)_q; present S_g
as a polynomial quotient; apply the stated regular-sequence theorem at the
contracted polynomial prime; establish the ambient regular-local depth equality
from a regular system of parameters; and induct over the regular defining list
using `IsLocalRing.depth_quotient_nonzerodivisor`. The induction explicitly
identifies module quotients with ring quotients and iterated quotients with the
quotient by the whole list. The support-dimension bound gives equality at each
step. Private proved helpers transport depth and the depth-dimension equality
through ring equivalences. Mathlib supplies the localization and stalk
isomorphisms and transports Noetherianity.

Added the proof import `Mathlib.RingTheory.Localization.LocalizationLocalization`
for localization of the chosen principal localization at its extended prime.
The mathematical dependency plan and unit route are unchanged; no node update,
interface change, consumer adaptation, or change record is needed.

Sources read: Stacks Algebra, Tag 00SB (`lemma-lci-CM`), Tag 02JN
(`lemma-reformulate-CM`), and the recorded declarations for every dependency in
the existing six-step node. The existing proof of the polynomial-ring
Cohen-Macaulay lemma supplied a reusable private argument for the regular-local
base case, without importing that unrelated theorem or its extra dependencies.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.isNoetherianRing_stalk_and_depth_eq_ringKrullDim_of_lci`
(node `lem-sfb-lci-cohen-macaulay-stalks`).

Validation: the final module compiled through `lcompile.py` with exit code 0 in
8.9 seconds, with no errors or warnings. Its public statement was compared
verbatim with the current source, and all lines satisfy the 100-character limit.
The import-direction check accepted the regular-sequence dependency.

Holes added: zero. Holes left in the delivered module: zero. Split off: zero.
Every added helper is private and completely proved. The induction includes the
empty defining list and dimension-zero regular-local base case; the stalk point
is arbitrary, with no closedness hypothesis. Empty schemes need no special case,
since the statement is quantified over a point.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`: this proof uses Mathlib's ring-level
  regular-local predicate, not scheme regularity.
- `Mathlib.RingTheory.Localization.Away.Basic`
- `Mathlib.RingTheory.Localization.AtPrime.Basic`
- `Mathlib.RingTheory.LocalRing.Quotient`
- `Mathlib.RingTheory.Regular.RegularSequence`

The four removed Mathlib imports are redundant through the retained imports.
All existing mathematical proof-dependency nodes are still used. In particular,
`def-weil-regular-scheme` supplies its Mathlib ring clause; removing the scheme
module import does not remove that ring-level dependency. No declaration or
module is withdrawn and no upstream declaration is changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The existing plan is sufficient, including its
arbitrary-prime regular-sequence input. No new intermediate result with an
unfinished proof was required. The legacy scheme-regularity proof import was
unnecessary for the ring-level argument.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
