## What changed

Restored `lean/Sheaf/Paper/ContinuousIntegralExchangeSourceAdjunct.lean` from the authoritative
quarantine source named by the current rework row. This repairs an absent theorem interface;
it is not a rebase or a no-op. All six existing proofs and all signatures are preserved.
Added a proof-only import of
`Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`
to make the post-sync `derivedPushSource` helper available during simplification. Wrapped
archived long lines to at most 100 characters. Public imports, declarations, attributes,
docstrings, coefficient and geometric assumptions, and all DAG attachments are preserved.
Change record: `coord/changes/T2-restore-continuous-integral-source-adjunct.md`.

## Proved and sorry left

Actual item hole count: zero before restoration in the archive and zero in the delivery.
Holes closed: none (0). Holes added: none (0). Holes split off: none (0).
The restored public theorem is
`AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_exchange_source_adjunct`
(node `lem-weil-pbc-continuous-integral-exchange-source-adjunct`). Its five private helper
lemmas `coefficient_counit`, `source_normal_form`, `baseChange_adjunct`,
`bounded_counit_hom` and `integral_push_counit` are all proved. There are no retained
`sorry` declarations and no new modules or obligations. This is restoration of the existing
complete proof, not a claim of six newly closed holes.

Validation: the final formatted proof compiles without warnings in 33.1 seconds. A temporary
`#print axioms` probe reports `propext`, `Classical.choice`, `Quot.sound` and inherited
`sorryAx` from existing imported theory. Thus the item has no local proof holes, but its
transitive foundations are not claimed to be completely proved. The probe is removed from
the delivered module. A token comparison with the archive confirms that the explicit proof
import is the only non-whitespace change; every declaration and proof body is preserved.

## No longer needed

None. No imports, declarations, nodes, modules or dependencies are pruned. The parent
`lem-weil-pbc-continuous-integral-exchange-equality` still needs this theorem, and the
quarantined `ContinuousIntegralExchangeEquality` retains its import and application.
All declared proof dependencies remain appropriate: integral comparisons and scalar
exactness, the condensed coefficient operations, the adjunction mate identities and the
square exchange API are used by the restored proof or its specialized constructions.
The unit route is unchanged. The quarantine archive is preserved.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole quarantine restoration rather than a theorem containing an open
`sorry`. The current rework row, its preserved archive and DAG parent establish the required
restoration. The archived file requires the explicit post-sync proof import described above:
without it, compilation reports unknown constant
`AlgebraicGeometry.ProEtale.CondensedRing.derivedPushSource` in `integral_push_counit`.
The proof compiles once this declaration is available, without changing its mathematics.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
