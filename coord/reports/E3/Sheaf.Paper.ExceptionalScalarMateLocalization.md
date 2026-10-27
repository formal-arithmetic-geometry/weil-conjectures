## What changed

Repair: replaced the unavailable private `sfLocalization_isLocalization` reference with
`integralLocalization l E T`, the localization theorem provided by the imported
`ExceptionalIntegralAdjunctionLocalization` module. This preserves the proof route and
avoids depending on a private declaration from an unrelated module.

Proved `WeilConjectures.ConstructibleExceptionalCoefficients.exists_integral_scalar_mate_localization`
by categorical localization of the supplied integral comparison. The proof identifies
the scalar localization squares from the published object and tensor formulas,
transports categorical localization through the full-subcategory equivalence,
descends both invertible comparisons by fully faithful precomposition, and verifies
the counit equation and integer-shift equations. The normalized q component is the
localization of the supplied integral q component.

Corrected the owning `scalarShiftLocalization` predicate to express the exact scalar
localization square with its canonical endpoint rationalization comparisons retained.
Its comparison is identity-normalized on integral representatives and commutes with
all integer shifts. This is an explicit definition correction, not a proof of the old
literal HEq condition. The theorem retains its original parameters and normalized
q conclusion. Explicit universes and equality-binder types avoid expensive universe
inference. See `coord/changes/E3-scalar-localization-shift-square.md`.

Added only private, proved helpers and proof imports. No consumer source is changed.
The node's statement correction and proof record describe the delivered argument.
The final source compiles on the server in 40.4 seconds. Its unchanged direct
importer `Sheaf.Paper.ExceptionalRationalStageLocalization` compiles against it in
31.0 seconds. The temporary unchanged importer copy was removed from the delivery.
No debug profiler or trace option remains.

## Proved and sorry left

One original hole:
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_integral_scalar_mate_localization`
(node `lem-sf-integral-scalar-mate-localization`). The delivery supplies its complete
proof for the explicitly corrected endpoint-shift predicate. No original hole remains;
no hole is added or split off. This counts as a proof together with a documented
definition correction, not as a proof of the former strict predicate.

The five private helpers `full_hom_heq`, `shift_of_whisker`, `iso_map_conjugate`,
`scalar_factor`, and `rationalization_isLocalization` are proved. No definition
contains sorry and no axiom is introduced. Existing assumed/proved category constructions retain their source
axiom dependencies, which this delivery does not alter.

## No longer needed

No existing import, module, or node is withdrawn. The proof avoids independently
constructing tensor naturality, inverse laws, and semilinear exact-comparison descent:
fully faithful precomposition through categorical localization supplies them.
`lem-pur-semilinear-scalar-localization` remains needed for the proved categorical
localization interface used by `sfLocalization_isLocalization`.
`def-weil-rationalization-karoubi` supplies the actual scalar object and arrow formulas.
`lem-sf-integral-adjunction-raw-localization` supplies the representative equivalence,
raw functors and fixed endpoint shifts. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The snapshot's old global bad-import record is historical: the current server queue
lists this module as a one-hole proof item, its dependency has been restored, and
its current source agrees with the source used for the proof.

The old `scalarShiftLocalization` required a literal HEq formula at every integer
shift after dropping both endpoint rationalization comparisons. The published chosen
rational triangulation specifies its literal tensor functor and identity localization
component only at shift one. Coherence determines the other shift functors up to
natural isomorphism; it does not force a literal presentation of their objects and
arrows. Thus that all-integer strictness was not the exactness assertion in Zheng,
Constructions 6.1 and 6.2. The repaired predicate expresses the actual comparison
square using `NatTrans.CommShift` for every integer and retains the fixed canonical
endpoint rationalization shifts.

The sole DAG citer `lem-sf-rational-stage-localization` continues to hold. Its Lean
module `Sheaf.Paper.ExceptionalRationalStageLocalization` uses the comparison and
q normalization and discards both endpoint shift proof fields. A textual scan finds
no other occurrence of the repaired predicate outside its owning module. The change
record lists the one direct importer and all 902 transitive importers, with holders
as recorded in the shared snapshot. No theorem from Challenge is edited.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalScalarMateLocalization": "fabe60b6b9bda5ff0c71336d12ba64475c1c4b81"}, "results": {"Sheaf.Paper.ExceptionalRationalStageLocalization": {"hash": "5a1473e034a5464bde19333cfcaa7507cef91aa2", "status": "OK"}}, "seconds": 24, "time": "2026-10-28T05:59:18+0800", "transitive": 0, "version": 1}
```
