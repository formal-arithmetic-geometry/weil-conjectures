## What changed

Filled `WeilConjectures.PurityFiniteSetting.finiteComparedInvertibleExponent`
in `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`. The witness is
`P.coefficients.l ^ P.level`. The coefficient prime belongs to the chosen DVR
maximal ideal, so this power vanishes in the quotient by the corresponding power
of the uniformizer ideal. The base field has characteristic `P.field.p`, distinct
from the coefficient prime, so the witness is a unit in the base field and hence
in the global sections of every scheme over it.

The argument is the one already specified in the theorem's docstring and also
implemented in `WeilConjectures.PurityFiniteSetting.Dnc.invertibleExponent`.
It is replayed here without importing the unrelated deformation-to-normal-cone
module, in accordance with this node's existing reviewed interface. Added only
proof imports `Mathlib.Algebra.CharP.CharAndCard` and
`Mathlib.Algebra.CharP.Algebra`. All existing signatures, definitions, instances,
and public imports are unchanged. No change to the unit route or node proof plan
is needed: the existing definition node has an empty proof plan and already owns
this helper and its complete natural-language proof.

Validation: the entire module compiled through `lcompile.py` on the remote
compiler in 43.0 seconds with exit code 0 and no diagnostics.
The proof allows arbitrary schemes, including the empty scheme, and uses neither
finite type nor separatedness nor divisibility of the level by the ramification
index. Positivity follows from primality of the coefficient prime.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.PurityFiniteSetting.finiteComparedInvertibleExponent`
(node `def-pur-co-smoothness`). Added 0 holes and split off 0 statements.
There are no `sorry`s left in the delivered module. Existing imported dependency
proofs are used through their published declarations.

## No longer needed

None. No original imports were removed and no nodes or modules were withdrawn.
The two added proof imports supply the characteristic/cardinality and algebraic
extension characteristic lemmas actually used in the proof. The original public
imports continue to support the existing statements and constructions.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy. The proof and its edge cases agree with the existing
source, docstring, and reviewed node. The complete proof follows the existing arithmetic argument without importing
the unrelated DNC module. No new mathematical statements are needed.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
