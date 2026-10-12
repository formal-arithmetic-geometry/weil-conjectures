## What changed

Proved `AlgebraicGeometry.Scheme.Hom.exists_principal_divisor_open_extension` with its
signature and original docstring unchanged. Constructed the function-field equivalence from
`genericPoint_eq_of_isOpenImmersion`, `stalkCongr`, and the generic stalk isomorphism; transported
the unit with `Units.map` of its inverse. Proved the commuting local-ring/function-field square
using stalk-specialization naturality and used preservation of coheight under an open embedding.
Four proved private helpers establish ring order, fraction order, and scheme order invariance
from Mathlib module lengths and fraction-field presentations. Updated the existing node's proof
and proof dependencies to describe this complete argument. No other existing module was adapted.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Hom.exists_principal_divisor_open_extension`
(node `lem-sc-principal-divisor-open-extension`). Holes closed: 1; holes added: 0.
No `sorry` remains in the delivered module. All four private helpers are proved:
`ring_ord_equiv`, `ring_ordMonoid_equiv`, `ring_ordFrac_equiv`, and
`AlgebraicGeometry.ord_eq_of_stalk_equiv`. This is a complete proof, not a decomposition.

The single-file compile passes without warnings. The argument handles zero in the general
order helper, nonzero constant units, points with coheight different from one, and an empty
boundary. No chosen data comes from an unproved theorem.

## No longer needed

Removed the proof-only imports `Sheaf.AlgebraicGeometry.DivisorModule` and
`Sheaf.AlgebraicGeometry.FunctionField`. The former's construction of the associated divisor
module and the latter's componentwise function-field product are unused. The actual divisor
and integral function-field definitions come from the retained source imports and Mathlib.
Removed the proof-dependency edges to `def-sc-divisor` and `def-sc-function-field`; their
statement-dependency edges remain, because the original statement still uses these notions.
Neither node is claimed to be globally unreachable: other targets or modules may need it.
There are no new modules or unproved dependencies. No blueprint unit statement or step is
bypassed; its `realized` arrays are empty, and the principal-divisor correction route is retained.

## Where the brief, the DAG or earlier work was wrong

The original planned generic-stalk and valuation identifications are valid. No statement
correction was necessary. A direct invariant of module length replaces the suggested
uniformizer argument and works for integral locally Noetherian schemes without regularity.
The original smoothness binder `hsm` is kept and explicitly referenced to preserve the
signature while satisfying the unused-variable linter.

## Second reading by P2

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are unchanged byte for byte; only proof helpers and proof-only imports were changed. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no warnings. The target has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The private helpers are fully proved. Verdict: pass.
3. Checked the proof route and edge cases. The construction transports the unit through an explicit ring equivalence; order invariance follows from module-length and fraction-ring identities, with zero, non-unit coheight, constant units, and empty boundary covered. No new statements or split-off holes were added. Verdict: pass.
4. Checked pruning and imports. The removed DivisorModule and FunctionField imports are proof-only and unused; the retained public imports provide every statement definition. The unit route remains the generic-stalk and order-transport route, and the node records no obsolete proof dependencies. Verdict: pass.
5. Checked the DAG node against the Lean proof and statement. The target statement is unchanged, proof steps describe the implemented argument, and proof dependencies match the declarations used. Verdict: pass.

Changed only the proof implementation and proof-only imports; no repair was necessary.
