## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.rationalClosedSupportConstructible`
with its original signature and public imports. The proof supplies the Noetherian,
quasi-compact and standing-field instances for the open complement. Private proved
helpers transport finite constant models through isomorphisms, lift the existing
pullback theorem to derived complexes using boundedness and homology comparisons,
and combine the formal support localization triangle with rational open direct-image
preservation and triangulated two-out-of-three. The two coefficient cases then instantiate
this argument. No arbitrary existence witness is used to define data.

Repaired the unclaimed module `Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction`:
`formal_closed_support_adjunction` now allows an independent derived-category Hom
universe `w`, instead of hardcoding `u + 2`. Its old specialization remains available.
This is needed for the already existing `u + 1` derived-category models used by the
item; no definition or mathematical assertion changes. No existing declaration-level
consumer uses this theorem, so no forced adaptations are needed. The change record is
`coord/changes/C1-formal-closed-support-derived-universe.md` and lists every downstream
import consumer and holder. The DAG route now records the actual existing pullback and
formal support inputs used by the proof.

The earlier attempt's unsubmitted whole-argument core wrapper and its draft node/report
are retained under `scratchpad/earlier-attempt/` for provenance and excluded from the
delivery. They are not library modules and no tombstone is needed.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`AlgebraicGeometry.ProEtale.CondensedRing.rationalClosedSupportConstructible`, node
`lem-sfb-rational-closed-support-constructible`. The item now has zero `sorry`.
Added zero holes and split off zero theorems. Every new private helper is proved.

The adapted dependency retains its single pre-existing hole:
`AlgebraicGeometry.ProEtale.CondensedRing.formal_closed_support_adjunction`, covered by
`det-lem-formal-closed-support-adjunction` in its source and proof docstring. This is an
existing formal localization input, not a new split-off or a proof of that input.
The external pullback, rational open-image and triangulated-closure theorems are used as
stated, including their existing proof holes; their modules are unchanged.

Validation: the adapted dependency and item compile together in dependency order;
the item also compiles after pruning the unused proof imports. The delivery preflight
performs the declaration and axiom checks. On resuming this sandbox on 2026-10-19,
both modules compiled again against the current build, and a source comparison confirmed
that the item's signature and public imports are unchanged. Edge cases are inherited from
the formal localization and pullback inputs: empty schemes, empty complement, identity closed
immersion, zero complex and arbitrary bounded cohomological intervals require no
additional hypothesis.

## No longer needed

Removed these direct proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.RingTheory.Noetherian.Defs`
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.Paper.FormalClosedSupportDerived`
- `WeilConjectures.ConstructibleSheaf.Pullback`

The item no longer directly needs these old proof-dependency nodes:

- `def-pc-scheme`
- `def-weil-pbc-noetherian-ring`
- `det-def-sfb-constructible-local-model`
- `det-lem-formal-closed-support-derived`
- `lem-weil-pbc-site-pullback-abelian-exact`
- `lemma-constructible-pullback-stratification`
- `pqf-def-locnoeth`
- `sk-def-sfb-dc-setting`
- `sk-prop-sfb-cartesian-coefficients`

Their scalar-presentation, exactness and stratification work is encapsulated by the
already stated `lem-sfb-pullback-constant-model-constructible`; the formal support
triangle/fiber is supplied directly by `det-lem-formal-closed-support-adjunction`.
These are pruned edges at this item, not claims that no other target branch uses those
modules. Public statement imports remain unchanged.

The unsubmitted draft `Sheaf.Paper.RationalClosedSupportConstructibleGeneral` and
`lem-sfb-rational-closed-support-constructible-core` are unnecessary: the original item
is proved from the existing declared inputs without this wrapper.

## Where the brief, the DAG or earlier work was wrong

The retained attempt moved the full obligation to a coefficient-uniform theorem. That
was not a genuine reduction and is replaced by the complete localization proof.
The original plan's `formal_closed_support_derived` interface uses another support
construction and presents its fiber on a K-injective mapping cone. The existing formal
adjunction interface directly matches `formalClosedSupport` and gives an isomorphism
for every distinguished fiber triangle. Its hardcoded Hom universe prevented applying
it to the target's existing derived-category models; the recorded universe repair fixes
that interface without changing any target or coefficient construction.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
