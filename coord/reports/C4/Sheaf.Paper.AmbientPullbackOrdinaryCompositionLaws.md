## What changed

Proved both remaining unit laws in
`Sheaf.Paper.AmbientPullbackOrdinaryCompositionLaws`, preserving every public signature.
The private site unit calculations apply the existing fibre-product unit laws to
both finite sites and the product sequence site. Sectionwise extensionality gives
the corresponding pushforward comparison laws, and Mathlib's
`Adjunction.leftAdjointCompIso_id_comp` and `leftAdjointCompIso_comp_id` give the
pullback unit laws. Endpoint equality transports are included throughout.
The existing associativity proof and the three-clause assembly are preserved.
Updated the three attached nodes to record the actual argument and dependencies.

Searches through `msearch.py` (Lean Finder, Loogle and grep) found the generic
adjunction unit laws used here. The source library's
`MorphismProperty.Over.pullbackComp_id_left` and `pullbackComp_id_right` supply
the site equations. These avoid any further decomposition.

## Proved and sorry left

Closed 2 of 2 existing holes:
- `WeilConjectures.AmbientPullbackTensor.ordinary_pullback_rightUnit`
  (`new-lem-sf-ambient-pullback-ordinary-right-unit`).
- `WeilConjectures.AmbientPullbackTensor.ordinary_pullback_leftUnit`
  (`new-lem-sf-ambient-pullback-ordinary-left-unit`).

Added zero holes and zero split-off statements. No `sorry` remains in the module.
`ordinary_pullback_compositionLaws` now assembles three proved clauses.
The complete module compiled in 20.7 seconds before removal of the unused proof
import; the delivery checks validate the final source and its axiom probe.

## No longer needed

Removed the private proof import `Sheaf.Paper.AmbientPushforwardIdentitySections`.
Its node `lem-sf-ambient-pushforward-identity-inverse-sections` is unnecessary for
this proof: the unit calculation uses the forward `pushId_existsUnique`
specification directly. This does not withdraw that module or affect its other users.

Removed `lem-weil-pbc-conjugate-iso-unit-equation` from the parent node's explicit
proof dependencies. The implemented proof uses the adjunction composition
coherence API directly, rather than separately re-proving its unit characterization.
The existing associativity dependencies remain, with the inverse-composition
section formula and the two proved unit declarations recorded explicitly.
No other modules or unit-route nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement needed correction. The previous split left the two
unit laws open; the existing generic adjunction and fibre-product APIs suffice
to close them. The parent's earlier dependency list omitted the inverse-section
formula actually used by its existing associativity proof and the two named unit
clauses actually used by its assembly; the updated node records those uses.
The blueprint unit route is unchanged. No existing shared definition, statement,
instance, attribute, or public import was changed, and no consumer adaptation is needed.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.AmbientPullbackOrdinaryCompositionLaws": "35a3061be8af040a28374e27bd43ffc6d63a84ee"}, "results": {"Sheaf.Paper.AmbientPullbackCompositionLaws": {"hash": "7f16387c2823c52b71d11566fc319662f47ef068", "status": "OK"}, "Sheaf.Paper.AmbientPullbackDerivedCompositionLaws": {"hash": "b386cbb58546039dfe7650451e079041616aa8d0", "status": "OK"}}, "seconds": 43, "time": "2026-10-28T11:52:46+0800", "transitive": 0, "version": 1}
```

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
