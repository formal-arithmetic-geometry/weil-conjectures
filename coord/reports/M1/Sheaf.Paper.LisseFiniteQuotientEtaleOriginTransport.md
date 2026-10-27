## What changed

Added the proof-only module `Sheaf.Paper.LisseFiniteQuotientEtaleOriginTransportMap`.
It states the geometric comparison-morphism step separately: the transported constant
model admits a morphism to the pulled-back complex that is both monic and epic. The
assigned theorem now obtains this morphism and applies
`CategoryTheory.isIso_of_mono_of_epi` in the balanced derived module category, then
returns `asIso f`.

The item's existing public statement and binders are unchanged. The item imports the
new module privately. The target node's proof and `proof_deps` now record this route.
The new node is `lem-weil-pbc-lisse-finite-quotient-etale-origin-transport-map`.

## Proved and sorry left

The original theorem
`AlgebraicGeometry.Scheme.lisse_finite_quotient_etale_origin_transport` is closed
syntactically: its proof is a complete Lean assembly from the monic-and-epic
comparison-morphism statement, with no `sorry` in the item module.

One split-off theorem remains sorry:

- `AlgebraicGeometry.Scheme.lisse_finite_quotient_etale_origin_transport_map`, node
  `lem-weil-pbc-lisse-finite-quotient-etale-origin-transport-map`, in the new module.
  It is exactly `:= by sorry`; its docstring records the Tag 09C6 construction and
  the proof of monicity and epicity by local finite models.

Holes closed: 1. Holes added: 1. This is a decomposition, not an axiom-free proof of
the original geometric transport assertion. No definition contains `sorry`.

## No longer needed

No existing import was removed. The original item's direct proof dependencies
`lem-weil-pbc-constant-adic-quotient-scalar-comparison` and
`lem-weil-pbc-comparison-pullback` are no longer used directly by the item's combining
proof; they remain the declared proof dependencies of the split-off comparison-morphism
node and remain transitively needed by the route. No module is withdrawn or claimed
unneeded from the target closure.

## Where the brief, the DAG or earlier work was wrong

The original target statement is marked `STATEMENT-DISPUTED` in the item module. The
structure `LisseFiniteQuotientEtaleOriginCore` supplies only a sheaf `level`, its
finite-local-constancy and vanishing properties, and finite-lisse properties for
homology sheaves of the pullback of `K`. It does not supply any comparison between
`level` (or its restriction to `Z`) and the pullback of `K`. The hypothesis `hE` only
identifies the restriction of `level` with a constant model `E`; it cannot bridge that
missing comparison. Thus the displayed derived-category isomorphism does not follow
from the current core data in general. A concrete counterexample pattern is obtained
on a point by choosing a nonzero `K` with locally constant homology and a different
rank constant `level`: all recorded lissity conditions can hold while the requested
isomorphism fails.

The split-off morphism statement isolates the missing Tag 09C6 geometric content in a
strictly smaller conclusion (existence of a morphism with `Mono` and `Epi`), and the
item's remaining Lean proof is the valid balanced-category assembly. The unit route is
not bypassed; this node remains below `sk-thm-properbasechange`.

## New nodes

`lem-weil-pbc-lisse-finite-quotient-etale-origin-transport-map` records the missing
comparison-morphism construction in
`lean/Sheaf/Paper/LisseFiniteQuotientEtaleOriginTransportMap.lean`. Its statement is
strictly the morphism, monomorphism, and epimorphism part of the target, rather than the
final `Nonempty` isomorphism. The node records the Stacks Tag 09C6 source, the
comparison-pullback and scalar-comparison dependencies, and the three Mathlib/library
searches. No change record is needed because no existing declaration or public import
was changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.LisseFiniteQuotientEtaleOriginTransport": "67d3062513dae6954c133324ac0cf0166e6de5fb", "Sheaf.Paper.LisseFiniteQuotientEtaleOriginTransportMap": "7423e48a078356617885d1a80e35dfef2168d5ad"}, "results": {"Sheaf.Paper.LisseFiniteQuotientEtaleOrigin": {"hash": "cf194cfc144c76044546ae2873a5578cc30d42e8", "status": "OK"}}, "seconds": 78, "time": "2026-10-28T04:13:18+0800", "transitive": 0, "version": 1}
```

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
