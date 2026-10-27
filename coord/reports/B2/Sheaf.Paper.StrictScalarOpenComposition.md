## What changed

Proved `WeilConjectures.PurStrictScalar.strictScalarOpenComposition` in
`Sheaf.Paper.StrictScalarOpenComposition` by formal mate pasting. Ordinary open
balancing supplies invertibility, and `strictScalarOpenUnit` identifies its
inverse as the open-adjunction mate of `strictScalarPull.hom`. The existing
`strictScalarPullComposition` supplies the geometric composition equation.
Mathlib's horizontal mate-pasting and conjugate-whiskering identities identify
the pasted inverse open map with the specified composite inverse open map.
Cancellation gives exactly the original forward equation.

Added private proof imports of `Sheaf.Paper.StrictScalarOpenUnit`,
`Sheaf.Paper.StrictScalarPullComposition`, and
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`.
Updated the item's node proof, proof dependencies and proof origin.
Validation: the proof's standalone compile passed without warnings or errors in
10.5 seconds. A first delivery probe was rejected at 69 seconds; profiling the
same proof with the exact axiom probe then passed in 9.7 seconds, with no slow
declaration. The compositor normalization was subsequently simplified from a
simp proof to the direct apply-symmetry identity for conjugateIsoEquiv. The theorem signature and original
public import were checked unchanged, and every added proof import is used.

All helpers are private and proved. The only auxiliary definition packages the
existing open scalar map as an isomorphism using its proved invertibility.

## Proved and sorry left

Closed 1 original hole:
`WeilConjectures.PurStrictScalar.strictScalarOpenComposition`
(`lem-pur-strict-scalar-open-composition`).

Added 0 holes and split off 0 statements. No `sorry` remains in the delivery.
The proof uses the existing statement
`WeilConjectures.PurStrictScalar.strictScalarPullComposition`, whose proof remains
an existing dependency obligation in its own module. This is a proof from stated
dependencies, not a claim that its complete axiom closure is already sorry-free.

## No longer needed

The direct planned proof dependency `lem-sf-open-tensor-normalization` is not
needed: no additional sectionwise or localization equality is required after the
published strict open-unit and pullback-composition interfaces are available.
It was not imported in the original item, so no Lean import was removed.
No module or declaration is withdrawn, and no global unreachability is claimed.
The existing compact-support strict scalar mate and strict open-extension nodes
remain dependencies for invertibility and the normalization of `jComp`.

## Where the brief, the DAG or earlier work was wrong

The original plan repeated the ordinary tensor-summand and exact-localization
calculation. The shorter formal route uses already stated normalized maps and
adjunction mate laws. No statement, definition, target, hypothesis or unit-level
route needed correction. The proof works uniformly for identity maps, empty
schemes and zero complexes; it adds no geometric or finiteness assumptions.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
