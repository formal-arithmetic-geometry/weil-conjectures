## What changed

Proved the unchanged `WeilConjectures.finiteHomSiteHomInvertible` in its item
module. The existing public import is retained. The new imports of
`Sheaf.SixFunctors.FiniteDualitySiteComparison`,
`Sheaf.Paper.FiniteComparisonFaithful` and
`Sheaf.Paper.IntrinsicSiteHomTransport` are used only by the proof.

Ordinary finite duality and the existing intrinsic Hom transport give an object
isomorphism from the source of the specified comparison to its target. The exact
derived inverse image is fully faithful by the existing unbounded finite-primary
comparison theorem, composed with the coefficient-realization equivalence. The
coefficient nilpotence and invertibility of the coefficient prime in the base
field are proved directly from the extension DVR and finite-field data.

The private categorical lemmas prove that postcomposition by the specified
`coefficientBaseChangeHom` is a bijection on Hom sets from inverse images. The
proof uses the two tensor-Hom adjunctions, full faithfulness and the invertible
tensor comparison. At the source object, surjectivity applied to the object
isomorphism supplies a right inverse; injectivity gives a left inverse. Thus the
actual evaluation-defined arrow is invertible. No evaluation compatibility of
the object isomorphism is needed.

Only the item module and its own node are changed. No existing public signature,
public import, definition, instance, attribute, target, or adopted-source file
changes. The node records the actual proof and dependencies.

## Proved and sorry left

Closed: `WeilConjectures.finiteHomSiteHomInvertible`, node
`lem-coef-finite-hom-site-hom-invertible`: 1 of 1 original holes.

The item has zero textual holes. All private categorical lemmas are proved.
No new holes or nodes are added. Existing imported statements are used as
recorded in their own modules and nodes.

Validation: the final module compiled cleanly through `lcompile.py` in 43.2 s,
within the 60 s limit. Development profiler options were removed. The public
theorem signature and its node attachment were checked verbatim against the
original; only the node proof, proof dependencies and proof origin are updated.

## No longer needed

No existing import was removed and no existing module is withdrawn. The old
plan's evaluation-normalized intrinsic presentation isomorphism, including the
representative-level compatibility of its evaluation with `finiteHomNuTensor`,
is unnecessary: full faithfulness and an object isomorphism suffice. No new
transport obligation is delivered.

The scalar-arrow and etale-arrow definition nodes remain needed for the actual
closed structures and tensor comparison; they are not claimed globally pruned.
The proof does not use coefficient quotient coherence, scalar-Hom invertibility,
or scalar reduction descent. The unit route through finite-duality site
comparison is retained.

## Where the brief, the DAG or earlier work was wrong

The earlier plan required matching a chosen intrinsic Hom presentation to the
normalized evaluations. The existing `intrinsicSiteHom_transport` supplies only
an object isomorphism. Directly equating the specified arrow with the transported
ordinary comparison would need further normalization. The proved categorical
argument avoids that extra requirement: it uses the object isomorphism only to
turn a Hom-set bijection into an inverse to the actual specified comparison.

`lem-ctf-finite-comparison-ordinary-fully-faithful`, in unit
`sk-prop-ctf-finite-comparison`, is used as an existing proved tool; the current
unit's finite-duality result supplies invertibility but does not state ordinary
unbounded full faithfulness. No maintainer tool approval is edited.

The current server queue was checked: this is a one-hole proof item, not a
zero-hole repair. Small cases of the categorical argument include zero objects
and the empty category/site. The coefficient argument uses exponent `n + 1`,
so `n = 0` is included. The bounded-constructible second input is preserved.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteHomSiteHomInvertible": "b26f92afc7fb4557bc518a86bea66e2eb501483f"}, "results": {"Sheaf.Paper.CoefFiniteHomSiteDescent": {"hash": "9ff436f0b1d6dc4ddb9c634bdd3c73cfc7c9f0b6", "status": "OK"}}, "seconds": 128, "time": "2026-10-28T10:34:32+0800", "transitive": 0, "version": 1}
```

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
