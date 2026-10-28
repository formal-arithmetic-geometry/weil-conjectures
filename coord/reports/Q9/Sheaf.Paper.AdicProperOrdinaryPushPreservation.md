## What changed

Proved `WeilConjectures.AdicQbarRealization.Proper.adic_proper_ordinary_push_preservation`
in `Sheaf.Paper.AdicProperOrdinaryPushPreservation`, with its signature unchanged.
Added one private proof import, `Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization`.
No public imports, definitions, instances, declaration names or other existing modules changed.
Updated the item's DAG proof to the four steps actually implemented.

Apply the existing compact-support realization to `(identity,p)`. Its `C.preserves` clause
already concerns the native bounded constructible predicate. Identify the coefficient maps
by evaluating their adjuncts on functions, and identify the two ordinary module pushforwards.
Identity extension is identity by uniqueness of left adjoints. The existing `properTransport`
and `rightDerivedFunctorNatIso` give the required ordinary derived-image comparison.
Unpack the input predicate and compose the output comparison with the image of its witnessing
isomorphism. This constructs precisely the output bounded-constructibility witness.
All local construction data are explicit compositions of existing isomorphisms; no arbitrary
object is chosen from a new existence statement.

Validation: the final module compiled through lcompile.py in 6.9 seconds with no errors
or warnings. Delivery runs the required preflight and axiom checks. The argument covers identity maps, empty schemes and the zero
complex through the same native preservation clause and isomorphisms.

## Proved and sorry left

Closed 1 of 1 existing holes:
`WeilConjectures.AdicQbarRealization.Proper.adic_proper_ordinary_push_preservation`
(node `lem-sf-adic-proper-ordinary-push-preservation`).

There are zero holes left in the delivered Lean module, zero new holes, and zero split-offs.
The existing lemmas imported by the proof retain their own library status; this delivery
closes the assigned declaration from them, as required by stage 3.

## No longer needed

No existing import was removed and no Lean module was withdrawn.
The direct proof dependency `def-weil-finite-tor-amplitude` is unnecessary: the already stated
compact-support preservation clause accepts native bounded constructible inputs directly.
Its use below the compact-support theorem is unaffected.
The existence theorem `lem-sf-adic-qbar-constructible-realization` is not invoked: the Family
is given, and `boundedConstructible` is defined by a native object with a presentation
isomorphism. The old proof's re-choice of realizations, common-stage finite-Tor argument,
and transport via uniqueness of derived right adjoints are not needed. We instead use the
existing `properTransport` from `def-sf-locally-finite-adic-compact-support-data` and equality
of coefficient maps. The original realization theorem remains in the existing public import
closure; this is removal of a direct DAG proof edge, not withdrawal of that module.

The DAG now explicitly records the coefficient-construction theorem and the native
compact-support data and realization data definitions used by the implementation.
The unit `sk-prop-sf-biduality-general` has no realized statement or proof-step attachment
for this node; its route and the parent's use of this node remain intact.

## Where the brief, the DAG or earlier work was wrong

The recorded global-build failure was a bad dependency import, whereas the current server
queue lists this item as a proof item, not rework. The dependency is available in the
published compilation environment: the completed proof imports it successfully.

The prior plan described a longer comparison than necessary. The native bounded predicate
is already the input to `C.preserves`, and the fixed section presentation is independent of
the realization's proposition-valued structure by proof irrelevance. Thus no new comparison
existence theorem or Family essential-image theorem is needed. The previous docstring's
right-adjoint uniqueness argument is replaced in Lean by equality of the sectionwise
pushforward definitions and the canonical derived `properTransport` comparison.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AdicProperOrdinaryPushPreservation": "796b46fca8fcc78dff5f4b776bdb4b9eb47166b1"}, "results": {}, "time": "2026-10-28T15:44:12+0800", "transitive": 0, "version": 1}
```

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
