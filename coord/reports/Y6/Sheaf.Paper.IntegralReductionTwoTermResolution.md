## What changed

Proved `WeilConjectures.IntegralHom.integralReduction_twoTerm_resolution` in
`Sheaf.Paper.IntegralReductionTwoTermResolution`, with its statement unchanged.
The proof uses the already proved `PrincipalKoszulStrictReplacement.completed_exact`
for the exact row of actual completed and restricted finite coefficient modules.
It constructs a mapping cone, identifies its two terms with the unit by the
zero-summand biproduct isomorphisms, proves the remaining terms vanish, and applies
the independent-universe bounded-flat K-flat criterion. Mathlib's short-exact
mapping-cone augmentation is composed with the canonical restriction/single
comparison, giving precisely the target complex in the original statement.

Added only private proof imports of `Sheaf.Paper.PrincipalKoszulStrictReplacement`,
`Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`, and
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`. Updated the item's DAG
proof and proof dependencies to match. No other existing module, signature,
definition, instance, attribute, or public import changes.

Validation: the final module compiled cleanly through `lcompile.py` in 6.5 seconds,
with no warnings and within the 60-second limit. The delivery tool runs the
remaining mechanical checks before pushing.
The construction keeps independent universes d,t,u, allows n=0, and never
assumes that Y is nonempty. No arbitrary resolution data are chosen from an
unproved existence theorem.

## Proved and sorry left

Closed the only original hole:
`WeilConjectures.IntegralHom.integralReduction_twoTerm_resolution`
(node `lem-sf-integral-reduction-two-term-resolution`).

Original holes: 1. Holes closed: 1. Holes added: 0. Holes left: 0.
No split-off statements or modules.

## No longer needed

No existing imports were removed. The planned direct dependencies on
`lem-weil-l-adic-extension-integers-dvr`,
`lem-weil-pbc-standard-quotients-perfect`,
`lem-weil-pbc-completed-constant-sheaf-reduction`, and
`lem-pc-bounded-above-flat-kflat-site` are superseded by the existing exact-row
API and the independent-universe bounded-flat criterion. Their modules were
not imported directly. This does not withdraw those nodes or their modules:
the existing principal-Koszul theory still uses arithmetic and completion
dependencies transitively, and other consumers may need them.

The replacement generic tools are
`lem-a1-principal-koszul-strict-replacement` (its public exact-row clause),
`lem-weil-pbc-independent-sheaf-tensor-colimits` (the site/monoidal tensor comparison),
`lem-weil-pbc-independent-bounded-flat-kflat`, and
`lem-weil-derived-scalar-extension-restriction-adjunction` (ordinary restriction
exactness and the actual restriction functor). These keep the unit route:
the finite-free coefficient resolution in paragraph 1 is constructed explicitly.

## Where the brief, the DAG or earlier work was wrong

The old proof plan did not notice that the needed completed short exact row was
already proved in `PrincipalKoszulStrictReplacement.completed_exact` at the
required independent universes. The older bounded-flat site theorem identifies
the site and coefficient universes, whereas the independent-coefficient version
fits the statement directly. Neither issue requires changing any statement.

Searches: LeanFinder found Mathlib's
`CochainComplex.mappingCone.quasiIso_descShortComplex`; Loogle on
`ShortComplex.ShortExact` returned no match; the launcher grep query
`double.*quasiIso|quasiIso.*double|isKFlat_of_boundedAbove` returned no hits.
Repository searches for two-term coefficient resolutions and uniformizer
exactness found `PrincipalKoszulStrictReplacement` and its completed exact row.
No new mathematical statement was introduced.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralReductionTwoTermResolution": "f3b916285cd1901ba57a1a47bfa46ce080760692"}, "results": {}, "time": "2026-10-28T10:31:20+0800", "transitive": 0, "version": 1}
```

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
