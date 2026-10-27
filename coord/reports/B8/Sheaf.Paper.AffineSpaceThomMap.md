## What changed

Closed four of the ten existing proof obligations without changing any public statement.
The recursive support is closed by list induction, since each successor is a pullback of a
closed coordinate immersion followed by a closed immersion. The general classSource equation
and target_succ use their defining equations. Exact closed pushforward follows from the quasi-compact complementary open in the
Noetherian tower, proving zero_exact.

The existing Thom construction is retained; its exceptional Hom equivalence receives
explicit source and target arguments to avoid expensive inference. The original transparency settings are retained.
The node copy records the completed arguments and identifies the six open obligations.

Validation: larger proof packets compiled through lcompile.py but their delivery
recompiles exceeded the fixed limit. The four-proof packet additionally retains the
original unit_origin obligation to avoid its costly specialized derived conversion.

## Proved and sorry left

Original holes: 10. Closed holes, all in namespace
`AlgebraicGeometry.ProEtale.AffineZeroPurity`:

- `support_closed`
- `classSource_eq`
- `target_succ`
- `zero_exact`

Six existing holes remain, each a named theorem with its source and proof in words:

- `unit_origin`
- `classSource_nil`
- `classSource_cons`
- `target_plus`
- `boundary_plus`
- `supportIso_existsUnique`

No holes added and no new split-off declarations. This is a partial proof delivery.

## No longer needed

None. All four original public imports are retained for the construction interface.
No node, module or unit step is withdrawn or bypassed. The experimental private comparison
proof import was removed because the delivered four proofs do not use it.

## Where the brief, the DAG or earlier work was wrong

The definition node had no proof steps despite ten named proof obligations in its Lean
module. The node copy now records the completed proofs and the remaining obligations.

A fuller attempt at the two boundedness obligations used flatness of the ordinary finite
Tate line, its shifted Tor amplitude, exact comparison and induction. A support-isomorphism
attempt used recursive lifts through coordinate zero loci and tower coordinate
extensionality. The complete attempt exceeded the fixed 60-second module compile limit,
and coordinate extensionality additionally encountered non-exposed limit-cone conversion
issues. Those experimental proofs and private helpers are not part of this delivery.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
