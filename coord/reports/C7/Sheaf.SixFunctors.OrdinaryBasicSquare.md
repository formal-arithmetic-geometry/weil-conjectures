## What changed

Proved `ordinaryBasicSquare` by all eleven `BasicPair` cases. Canonical
isomorphisms use `ordinaryCanonicalIsoSquare` and cancellation. Proper and open
units/counits use the generic mate identities and `fixedOpenReduction_isIso`.
The remaining cases apply the stated proper/open, exchange, projection and
compactification component squares.

Repaired the returned import cycle by replacing the circular parent applications
in `ordinaryExchangeSquare` and `ordinaryCompactificationExchangeSquare` with
independent complete proofs. Proved private categorical helpers transpose the
pullback boundary, insert arbitrary coefficients by naturality, prove the open
beta coefficient square, and paste the prescribed compactification exchange.
Whole-transformation equations identify the recorded system and ringed maps
with their exact associator composites. The generic pasting lemma then takes
components in abstract categories. An inferred proof function and explicit
congruence proofs, following the private method in
`IntegralOrdinaryProperOpenSquare`, normalize the derived-category presentations
without changing definitions. The public theorems specialize the resulting identities by
`exact`, avoiding expensive conversion through derived-category definitions.

Both component modules no longer import `OrdinaryBasicSquare`. Existing theorem
signatures, visibility, global attributes and public imports are unchanged.
Updated all three DAG proof records and the change record
`coord/changes/C7-ordinary-exchange-independent-proof.md`.

Validated the affected chain one file at a time in import order, with no warnings:
compactification exchange (19.5 s), primitive exchange (4.5 s), the unchanged
exchange/projection wrapper (6.9 s), the unchanged compactification wrapper
(25.7 s), and OrdinaryBasicSquare (7.4 s). Removed the unchanged wrapper copies
after checking them. All three public theorem signatures match current main
verbatim.

## Proved and sorry left

Closed 1 of 1 item holes:
`WeilConjectures.IntegralSystemRealization.ordinaryBasicSquare`
(`lem-sf-integral-ordinary-basic-square`).

Added zero holes; split off zero statements. All three delivered Lean modules
have zero `sorry`. The independent replacements of `ordinaryExchangeSquare` and
`ordinaryCompactificationExchangeSquare` preserve their existing complete
proofs and are not counted as additional holes closed.

## No longer needed

Removed the proof import `Sheaf.SixFunctors.OrdinaryBasicSquare` from both
`Sheaf.SixFunctors.IntegralOrdinaryExchangeSquare` and
`Sheaf.SixFunctors.IntegralOrdinaryCompactificationExchangeSquare`. Neither
component proof now uses `lem-sf-integral-ordinary-basic-square`.

Removed the obsolete direct DAG proof dependency
`lem-weil-pbc-ringed-exchange-tensor-coherence` from the item and exchange nodes:
the needed boundary and mate identities are proved directly from the canonical
coefficient squares. The exchange node also drops its unused direct dependency on
`lem-sf-tensor-adjunction-reduction-squares`: its primitive mate calculation uses
the canonical boundary and Mathlib. These nodes remain needed elsewhere and
are not withdrawn.

The conjunction wrapper `IntegralOrdinaryExchangeProjectionSquares` is not
needed for the two direct exchange/projection cases, which use their component
theorems. It remains needed by `IntegralOrdinaryCompactificationSquares`. No
module is withdrawn; all remaining proof imports supply a case lemma or a
private helper used in the proof.

## Where the brief, the DAG or earlier work was wrong

The existing exchange and compactification-exchange proofs applied
`ordinaryBasicSquare`, while the case proof of that parent needs those component
squares. The previous delivery removed only the exchange-to-parent import, but
its new helper import still reached the parent through the compactification
component. Replacing both circular applications with independent proofs removes
the full cycle reported by the landing tools.

The unit's realized lists are empty. This proof follows the stated generator
route and does not bypass a blueprint unit.

## Forced adaptations

The landing failure was the source import cycle
`IntegralOrdinaryExchangeSquare -> IntegralOrdinaryCompactificationExchangeSquare
-> OrdinaryBasicSquare -> IntegralOrdinaryCompactificationSquares ->
IntegralOrdinaryExchangeProjectionSquares -> IntegralOrdinaryExchangeSquare`.

`IntegralOrdinaryExchangeSquare` (unclaimed) replaces its parent import and
parent application with the private primitive mate calculation from
`IntegralOrdinaryCompactificationExchangeSquare`.

`IntegralOrdinaryCompactificationExchangeSquare` (unclaimed) replaces its parent
import with the canonical, open-reconstruction and adjunction helper modules,
and replaces its parent application with complete proper/open pasting. Every
added helper is private and proved. Both public signatures remain verbatim.
The two direct wrapper consumers require no source adaptation.


## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralOrdinaryCompactificationExchangeSquare": "f27fd02fa69c33e9bda91ce9e3ed8e858809180b", "Sheaf.SixFunctors.IntegralOrdinaryExchangeSquare": "766f3e258b38ddca540fad348d2a99aa8e4e7842", "Sheaf.SixFunctors.OrdinaryBasicSquare": "e6df8dde0c841ea68b007dfe0a44e62627449c4e"}, "results": {"Sheaf.SixFunctors.IntegralOrdinaryCompactificationSquares": {"hash": "8b89f269177bdb75db7085017ff39c046c316186", "status": "OK"}, "Sheaf.SixFunctors.IntegralOrdinaryExchangeProjectionSquares": {"hash": "70262e517d2b5ef75dbd07b19bcac239bff5a686", "status": "OK"}}, "seconds": 27, "time": "2026-10-28T11:40:01+0800", "transitive": 0, "version": 1}
```

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
