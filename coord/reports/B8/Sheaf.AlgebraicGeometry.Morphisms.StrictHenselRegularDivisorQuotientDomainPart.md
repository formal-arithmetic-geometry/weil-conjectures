## What changed

Completed the listed zero-hole retirement of
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientDomainPart`.
The upstream domain theorem is retained verbatim. In its sole direct consumer,
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular`, replace
the proof import with the upstream owner and transport its result across the existing
canonical principal-quotient ring equivalence using `MulEquiv.isDomain_iff`.
The consumer shares the comparison between its regularity and domain proofs, keeping
its public signature, visibility, public imports and docstring unchanged.

The domain node now points to the existing upstream declaration; both node proof
records describe the actual argument. Every mathematical dependency and the unit
route is retained. Change record:
`coord/changes/B8-retire-strict-hensel-regular-divisor-quotient-domain-part.md`.

## Proved and sorry left

The item already contained zero holes. Holes closed: zero. Holes added: zero.
No declaration in this delivery is left with `sorry`; no theorem is split off.
The existing upstream
`AlgebraicGeometry.Scheme.strictHenselizationRing_divisor_quotient_domain_part`
provides the domain result for the full colimit. The adapted
`AlgebraicGeometry.Scheme.strictHenselizationRing_regular_divisor_quotient`
proves the original conjunction for the small colimit by genuine ring-isomorphism
transport. This is a duplicate retirement, not a claimed new theorem proof.

Validation: the original consumer fails against the empty item with an unknown
identifier at line 91; the adapted consumer compiles. All ten downstream modules
are compiled individually against the retirement before the unchanged verification
copies are removed. The final delivery runs its compiler and axiom probes.

## No longer needed

Withdraw the duplicate module
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientDomainPart`.
Its consumer removes the proof import of that module and imports the proved upstream
owner instead. The withdrawn module's imports disappear with it:
`WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`,
`Mathlib.RingTheory.RegularLocalRing.Defs`,
`Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`,
`WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart`,
and `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`.
These theories remain available where needed elsewhere; no claim is made that their
modules are globally unused. No mathematical dependency node is pruned: the domain
node remains attached to the upstream theorem, and its parent keeps both component
edges. The redundant copy of the colimit-comparison argument disappears with the item.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a proof obligation, but the current source is already
proved and the exact item is explicitly listed for retirement in `coord/retire-items.tsv`.
There is no open B8 return and no active rework row for the item. The old rework
completed on 2026-10-20; the current item is present and is not quarantined.
The upstream twin uses the full colimit, so an import substitution alone would not
prove the consumer's small-colimit statement. The canonical colimit comparison and
its induced quotient equivalence supply the required transport. No statement is
disputed or weakened, and no adopted source declaration is removed or modified.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
