# CategoryTheory.coefficientRealizationTransport

## Reason

The main theorem uses the existing composition, operation, and tensor transport
lemmas. Move their entire FormalTransport section before Systems so those lemmas
are available to its proof. The static preflight treats reordered variable commands
as a possible interface change and requires this record. The same declarations
retain exactly their original sections, variable contexts, signatures, visibility,
and definitions. No new declaration, variable command, or import is introduced.

## Old

The section order was SuppliedDomains, FormalTransport object/arrow definitions,
Systems, FormalTransport, then the finite path definitions and theorem. In particular,
the following existing section occurred immediately after `end Systems`:

```lean
section FormalTransport

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]
```

It contains coefficientRealizationTransport_comp, _map, _tensor, _successive,
_identity, and _eq_of_eq. Each originally had its proof omitted.

## New

The identical FormalTransport section, with all six original theorem signatures,
now immediately precedes `section Systems`. Systems itself is unchanged apart
from the proof of coefficientRealizationTransport. The section header remains:

```lean
section FormalTransport

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]
```

All eight original theorem holes are proved. There are no private helpers, no
new nodes, and no changes to target statements or definitions.

## Users

`tools/downstream.py Sheaf.Paper.CoefficientRealizationTransport --uses
coefficientRealizationTransport` lists the two downstream modules below and
finds no external use of that theorem name. The direct importer imports this
module only for proof dependencies; the other is an indirect importer. Their
statements and proofs are unaffected by declaration order because all existing
declaration names, types, visibility, and definition bodies are unchanged.
Neither consumer requires an adaptation. The local claims scan found neither
consumer listed in coord/claims* at the time of this check.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientRealizationTransport | B3 | Eight proofs completed; FormalTransport moved before Systems. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed in local claims snapshot | Identical imported interface; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed in local claims snapshot | Identical transitive interface; no adaptation. |

## Status

landed 20261019T160417-L-3354970 2026-10-19 (merge of deliver/B3/Sheaf.Paper.CoefficientRealizationTransport)
