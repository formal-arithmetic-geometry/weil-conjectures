## What changed

Filled `WeilConjectures.DncCoefficientTransport.section_scalar_base_change` in
`Sheaf.SecSmoothPurity.SectionScalarBaseChange`, without changing its signature.
All supporting declarations are proved private helpers in the item module.
The proof uses the existing unbounded proper scalar mate, open scalar exchange,
proper-refinement transpose normalization, and abstract coefficient-exchange mate
identity. It first proves a general compact-support scalar cube, passes to its
exceptional mate, evaluates at the unit, and then pulls back to compatible sections.
The final section argument transports the existing exact scalar compositor to
left-derived pullbacks and uses precisely the composition arrows in sectionMap.
Updated the node's proof, proof_deps and proof_origin to describe this argument.
LeanFinder, Loogle (Adjunction.homEquiv), Mathlib grep, and local source searches
found the constituent categorical results rather than an existing theorem with the
whole assigned signature. The blueprint unit route and all shared interfaces stay intact.
After profiling a successful type-check that exceeded 60 seconds, enabled the
existing private instance caches and local irreducibility attributes for derived
functor matching. These attributes are local to this file; no shared definition
or exported attribute is changed. The resulting full module compiled in 33.1 seconds
with zero holes; profiling options were then removed before delivery.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.DncCoefficientTransport.section_scalar_base_change`
(`lem-pur-section-scalar-base-change`). No holes added or split off; no sorry remains
in the delivered module. All private helper theorems and the private natural
isomorphism construction are complete.

## No longer needed

The proof does not use `det-sp-mixed-base-change`
(`Sheaf.SecSmoothPurity.MixedBaseChange`): its pro-etale finite-type-over-a-field
setting is unnecessary. The ordinary etale proper/open cube gives the required
canonical arrows directly, with no Noetherian or boundedness condition on the
primed input. Removed this node from proof_deps and proof-step uses. This is pruning
of this proof route only; the module is not withdrawn and other consumers remain.
No original Lean import is removed: the original sole public import supplies the
statement's definitions. All added imports are private proof imports. The temporary explicit import of
`Sheaf.Paper.ExceptionalCoefficientComparison` was redundant and was removed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan proposed restriction to an affine cover for the locally
Noetherian primed base. Equality of derived morphisms is not in general detected by
such restrictions, so that assertion is not used. The proof instead works globally
on arbitrary schemes. Several existing public coherence theorems impose Noetherian
or bounded-below hypotheses, but their proved internal normalization, open-adjunction
and mate equations are unrestricted. Reusing those equations and proving the
unbounded proper-refinement compatibility avoids strengthening any hypothesis or
changing any shared interface. The stale quarantined import failure recorded in
rework is absent from the current live item, which compiled before proof work;
the current server queue assigns the proof route.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.SecSmoothPurity.SectionScalarBaseChange": "f085b4a7302e0cbb0f06bb643037a4f5b48e1e66"}, "own_failed": ["Sheaf.SecSmoothPurity.SectionScalarBaseChange"], "results": {}, "time": "2026-10-28T00:59:30+0800", "transitive": 0, "version": 1}
```

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
