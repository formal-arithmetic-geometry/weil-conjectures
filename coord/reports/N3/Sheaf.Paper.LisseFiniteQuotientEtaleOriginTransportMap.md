## What changed

Proved `AlgebraicGeometry.Scheme.lisse_finite_quotient_etale_origin_transport_map`
by constructing an isomorphism and taking its hom. No additional proof obligation
was split off.

The essential repair is in `Sheaf.Paper.LisseFiniteQuotientEtaleOriginCore`:
`LisseFiniteQuotientEtaleOriginCore` now retains the actual comparison between its
level and the fixed-coefficient pullback of K. Its existing constructor already
produced the required origin isomorphism eL. The added constructor branch transports
that isomorphism through the scalar restriction counit and inverse-image comparisons.
The concrete public `finiteQuotientOriginEncoding` and `finiteQuotientOriginPullback`
provide an API for expressing this field without private definitions in a public
signature. Their data is constructed explicitly. The encoding equivalence reuses
the already proved private scalarRestriction equivalence.

In the assigned module, `targetEncodingIso` proves compatibility of the actual
ring-sheaf pullback with the fixed-coefficient realization. `constantEncodingIso`
cancels the forward and inverse coefficient restrictions in the specified constant
realization. The main proof restricts hE to the finite coefficient ring, pulls its
constant model through the factorization W to Z to V, and composes with the retained
core comparison. The two resulting fixed-coefficient isomorphisms lift through the
fully faithful equivalence of coefficient encodings. The hom of the lifted
isomorphism is both monic and epic.

The parent module `Sheaf.Paper.LisseFiniteQuotientEtaleOriginTransport` has only
its obsolete STATEMENT-DISPUTED comment removed; its theorem statement and proof
are unchanged. No adopted `WeilConjectures` source module was changed.

The change record is `coord/changes/N3-finite-quotient-origin-comparison.md`.
Both the core and assigned DAG nodes follow the delivered argument, and the core
node records its statement correction and all three citers. The proper-base-change
unit statement and its realized proof steps are preserved.

The shorter-route search found the existing constant-sheaf, scalar-restriction,
fully faithful preimageIso, and inverse-image comparison APIs. These close the
obligation directly once the discarded origin comparison is retained. The source
read was Stacks proetale.tex, Tags 09AL and 09B1 for derived origin, and Tag 09C6,
whose proof explicitly retains K_n = epsilon^(-1)L_n before transporting local models.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.lisse_finite_quotient_etale_origin_transport_map`
(node `lem-weil-pbc-lisse-finite-quotient-etale-origin-transport-map`).

The changed core constructor
`AlgebraicGeometry.Scheme.lisse_finite_quotient_etale_origin_core`
(node `lem-weil-pbc-lisse-finite-quotient-etale-origin-core`) has zero holes before
and after this delivery; its additional comparison field is fully proved.
The added public encoding instances and private proof helpers are also fully proved.

Holes closed: 1. Holes added: 0. Split off: 0. Sorries remaining in the delivered
Lean files: 0. Existing imported proof dependencies retain their own proof status;
this report does not claim their transitive axiom closure has been discharged.

Validation: the repaired core and assigned module compile without errors or warnings
(39.7 s and 52.0 s). All direct consumers are compiled against the repaired core;
the unchanged final-origin consumer is removed from the sandbox after that check.
The delivery tool performs consumer checks. The definition repair and change record
are submitted for independent review.

## No longer needed

No module is withdrawn and no original import is removed. Both originally stated
proof dependencies, constant finite-quotient scalar comparison and comparison-pullback,
remain used. The proof additionally uses the existing core and finite fixed-coefficient
encoding APIs, including the proved constantEncodingNatIso from
`Sheaf.Paper.AdicLisseRelativeRestriction`.

The old plan's local mono/epi detection step is unnecessary. The map is the hom of
an explicitly constructed isomorphism; no sheaf-level mono/epi detection argument
in the derived category is needed. The assigned proof does not use C.lisse,
C.vanishing, or C.refinementLisse. Those fields remain needed by the final origin
and are preserved, so their supporting modules and nodes are not pruned.

## Where the brief, the DAG or earlier work was wrong

The old core's definition discarded the isomorphism between its level and K.
Its docstring and the assigned node's first proof step referred to a core comparison
which did not exist. The parent transport theorem had already marked precisely
this issue as STATEMENT-DISPUTED, but the split-off map theorem inherited it.

For a nonzero bounded constant complex K on a nonempty point, level=0 satisfies
the old lissity and vanishing fields; refinementLisse depends only on K. With
identity charts and E=0, the old transport theorem would incorrectly force the
nonzero pullback of K to be isomorphic to zero. Finiteness alone cannot supply
the missing comparison.

The repair retains the genuine origin comparison already produced by the existing
constructor, and proves the new field. It does not assume the transport conclusion,
change a target signature, weaken a conclusion, or introduce a new holed theorem.
The final origin's definition is unchanged. All three DAG citers of the core remain
valid: the map proof uses the new comparison, the transport parent uses that map,
and the final origin continues to use the existing constructor and transport.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.LisseFiniteQuotientEtaleOriginCore": "bc3873571e2a0afc3b4ec1f96dbe1fa37b04a286", "Sheaf.Paper.LisseFiniteQuotientEtaleOriginTransport": "b615180772e86e1f1323c09fc2dad5fa6a70edd0", "Sheaf.Paper.LisseFiniteQuotientEtaleOriginTransportMap": "797d61eaf01061587e338c1808171afce54f6706"}, "results": {"Sheaf.Paper.LisseFiniteQuotientEtaleOrigin": {"hash": "cf194cfc144c76044546ae2873a5578cc30d42e8", "status": "OK"}}, "seconds": 19, "time": "2026-10-28T06:32:46+0800", "transitive": 0, "version": 1}
```

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
