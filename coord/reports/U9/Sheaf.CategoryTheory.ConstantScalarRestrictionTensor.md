## What changed

Completed `CategoryTheory.ConstantScalarRestriction.ordinary_exists` on the existing
literal restriction functor. Presheaf scalar restriction, module-sheaf inclusion and
fixed-coefficient sheafification give its lax braided structure. Local scalar-unit
surjectivity makes compatible pairings ring-sheaf bilinear; the existing tensor
universal property constructs the inverse tensorator. Pure tensors detect both inverse
identities. Essential surjectivity and lax unitality prove the unit comparison invertible.
The resulting monoidal identification proves the prescribed generator normalization.

Repaired repeated unfolding in the full module: named canonical complex and derived
tensor instances keep their terms compact; the ringed tensor instances are cached before
the generator formulas. `onDerived` is now a regular definition with exactly its former
body. Generic flat-resolution transport avoids repeatedly elaborating the concrete
coefficient categories. The derived comparison uses the existing normalized braided
localization theorem, native K-flat tensor/unit comparisons and canonical cochain braiding.
Every original public import and mathematical statement is retained. No target statement
changes, no source-library module changes, and no consumer source is adapted.

The two node copies describe these actual arguments and dependencies. All additional
proof imports are private. Definition changes and all downstream users are recorded in
`coord/changes/u9-constant-scalar-ordinary-proof-scope.md`; definitions used by targets
remain subject to the independent statement review.

Validation: the complete repaired module compiled with zero holes through `lcompile.py`
in 57.8 seconds (`scratchpad/RepairFlatBeforeTensorInstances.lean`). Its delivery copy
removes two unused private imports and is being checked separately. No compiler limit
was changed; the library module and its proof have not been split to meet that limit.

## Proved and sorry left

Closed one of one original holes:
`CategoryTheory.ConstantScalarRestriction.ordinary_exists`, realizing
`lem-sfb-constant-restriction-ordinary-monoidal` and step 1 of
`lem-sfb-constant-scalar-restriction-tensor`.

Holes added: zero. Holes split off: zero. Holes left in the delivered module: zero.
All private helpers are proved. The tensor lift is chosen using a proved unique
universal property, which determines it by its pure-tensor equation. No data are chosen
from a holed existence theorem.

## No longer needed

Removed the private proof imports
`Sheaf.CategoryTheory.DerivedCategory.ExactTensorFunctorBraiding` and
`WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare`.

The ordinary node no longer directly needs
`lem-pc-sites-module-sheafification-bilinear-extension` or
`lem-pc-sites-sheafification-underlying-sets`. It does need the tensor bilinear universal
property, using its existing independently-universe-polymorphic private formulation
in `Sheaf.SecSmoothPurity.CochainInverseComparison`.
Accordingly the ordinary node's `tool_uses` drops only
`lem-pc-sites-module-sheafification-bilinear-extension`; the still-used
`lem-pc-sites-sheaf-tensor-bilinear-universal` is kept (reviewer correction).

The parent node no longer directly invokes
`lem-sfb-multivariable-derived-calculus`, `lem-sfb-oplax-monoidal-of-lax-square`, or
`lem-sfb-exact-tensor-functor-derived-braiding`: existing normalized braided localization
and native derived tensor comparisons replace those local proof steps. Such dependencies
may remain inside the imported localization theorem or other consumers; their declarations
are preserved. No entire module is withdrawn and no whole-library pruning is claimed.
The blueprint unit's statement and realized steps remain in the route.

## Where the brief, the DAG or earlier work was wrong

The direct unit construction proposed for the ordinary node is unnecessary: tensorator
invertibility, lax unitality and essential surjectivity imply unit invertibility. The
planned tensor universal declaration identifies the site universes; its existing private
generalization in `CochainInverseComparison` handles this module's independent universes.

The earlier zero-hole proof still exceeded the delivery file gate. Repeated elaboration
of canonical tensor instances and unfolding of the `onDerived` abbreviation were material
costs. The named canonical definitions and the existing normalized localization API
repair the full file, preserving the mathematical definitions and all compatibility laws.
The earlier failed delivery pushed nothing and is superseded by this repair.

Process incident during this repair session: an incorrectly scoped process-selection command
intended to stop obsolete U9 diagnostic compiles terminated other workers' local
`lcompile.py` client processes as well. The cleanup was stopped immediately. No source
files, launcher files, compiler limits, or compiled artifacts were modified by it.
Affected clients need their ordinary compile retry; server-side queued jobs were not canceled.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
