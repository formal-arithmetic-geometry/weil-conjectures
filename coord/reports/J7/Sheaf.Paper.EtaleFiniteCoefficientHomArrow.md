## What changed

Proved `WeilConjectures.finiteHomEtaleData_existsUnique` in
`Sheaf.Paper.EtaleFiniteCoefficientHomArrow`. The witness combines the existing
canonical closed structures with the published scalar tensor isomorphisms,
transported along equality of their tensor functors. Private generic helpers
identify native tensor with uncurried tensor and prove record uniqueness from
pointwise equality of its closed and tensor fields. Explicit equality of the
implicitly indexed tensor families retains both indices.

Proof-local transparency and irreducibility keep the chosen closed structures
abstract during specialization. No public declaration signatures, definition
bodies, public imports, or target statements change. The retained candidate compiled through the delivery tool in 53.2 seconds,
with profiler-option warnings. Removed those diagnostics and scoped the new
local irreducibility attributes to the proof section. A subsequent diagnostic
run reached the 60-second file limit; no limit was changed. The delivery tool
performs the final clean compile and axiom probe.

## Proved and sorry left

Closed 1 of the 3 original holes:
`WeilConjectures.finiteHomEtaleData_existsUnique`.

The two unchanged original holes remain:

- `WeilConjectures.finiteHomEtaleClosed_existsUnique`.
- `WeilConjectures.finiteHomEtaleRepresentativeData_existsUnique`.

All three declarations belong to `def-sf-etale-finite-coefficient-hom-arrow`.
Added 0 holes; split off 0 statements. This is a proof from the existing canonical
closed normalization theorem, not a new decomposition or a moved hole.

## No longer needed

None. Every original import supports the unchanged statements and constructions.
The definition node has no planned proof dependencies to prune, and its proof
route remains the canonical normalization described in the existing docstring.
The unit route is unchanged. No new modules or nodes are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The tensor functor of a monoidal category
and the uncurrying of its curried tensor agree by functor extensionality and
`MonoidalCategory.tensorHom_def`; using this generic equality avoids expanding
the specialized derived-category monoidal data. The closed record chosen at each
level is fixed by its existing normalization, including identity quotients.

Candidates for the other two original holes remain experimental and are not
part of the delivery. Their specialized dependent comparisons exceeded the file
limit. No definition repair, diagnostic option, changed limit, or new assumption
is included in this packet.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
