## What changed

Completed `AlgebraicGeometry.reduced_algebraic_normalization_field_change` with its exact original
signature and all six clauses. The proof supplies finiteness, surjectivity, the precise dense
normal locus, unique open-restriction comparisons, unique separable-field comparisons with both
projection equations, and the algebraically closed case. All added helpers are private and proved.

The local normal-point argument uses a germ-injective affine neighborhood, the unique component
meeting that integral neighborhood, a dominant lift of the normal stalk to its normalization,
and Mathlib spreading. The resulting local section is a dense closed immersion into a reduced
scheme, hence an isomorphism. This replaces the affine product/total-fraction dictionary and the
finite-cokernel normal-locus calculation. The maximal isomorphism open is then exactly the normal
locus; generic stalks are fields, giving density. Restriction and scalar extension follow from
finite normal comparison on a dense open, with separatedness providing uniqueness.

The only changed Lean module is the assigned module. No other existing module is adapted,
and no declaration signature, definition, attribute or public import changes. The existing
component-integrality declaration is used as stated.

Updated the assigned node's proof, proof dependencies and proof origin to the implemented route.
Withdrew its obsolete `lem-sbc-integral-closure-finite-normal-product` tool approval entry.
The source affine argument remains in the theorem's docstring, explicitly distinguished from
the implemented Lean route.

Server validation: `lcompile.py --all` compiled the assigned module without warnings or errors; its initial
complete compilation took 8.9 seconds and the subsequent verification also passed. Checked exact equality of the original public
statement and unchanged definitions. No new assumptions, axioms, definitions or public helpers.

## Proved and sorry left

Closed the assigned module's only hole:
`AlgebraicGeometry.reduced_algebraic_normalization_field_change`
(node `lem-weil-pbc-reduced-algebraic-normalization-field-change`).
All clauses are proved from the existing declarations; no part is split off.

Actual holes in the delivered module: **zero**. Holes closed: **one**. Holes added: **zero**.
No new intermediate theorem with `sorry` is introduced. Existing dependency declarations,
including `AlgebraicGeometry.Scheme.isIntegral_reducedNormalizationComponent`
(node `def-weil-pbc-reduced-normalization`) and
`Algebra.isNormal_tensorProduct_of_separableExtension`
(node `lem-weil-pbc-normal-algebra-separable-scalar-extension`), remain imported and unmodified.
This delivery does not claim those dependencies or the whole target closure are sorry-free.

Edge cases checked in the argument: empty schemes and empty opens, arbitrary reduced reducible
schemes, normal points on a single component, and arbitrary possibly transcendental extensions.
No claim that components stay integral after separable scalar extension is used.

## No longer needed

The following private proof imports were removed from the assigned module:

- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.ResidueField`
- `Mathlib.RingTheory.Ideal.MinimalPrime.Localization`
- `Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`
- `Mathlib.RingTheory.Localization.Integral`
- `Mathlib.RingTheory.RingHom.Flat`
- `Sheaf.RingTheory.IntegralClosureFiniteNormalProduct`
- `Sheaf.RingTheory.ReducedNoetherianTotalRingFractions`
- `Sheaf.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`

The Noetherian, flat-ring-map and integral-normalization APIs are still used through necessary
imports; those three redundant import removals do not prune the underlying results.
All three removed `Sheaf.RingTheory` modules are unnecessary as direct dependencies of this proof.
A static import traversal confirms that `IntegralClosureFiniteNormalProduct` is no longer
reachable from this module. The other two remain transitively needed by the retained
`NormalAlgebraSeparableScalarExtension` dependency; their redundant direct imports were removed.
Global pruning is for the maintainer's import-closure ledger; shared uses elsewhere are unaffected.

The old affine route's following proof dependencies are no longer needed by this item's proof
and have been removed from its node:

- `lem-weil-pbc-reduced-noetherian-total-ring-fractions`
- `lem-weil-pbc-integral-closure-commutes-localization`
- `lem-sbc-integral-closure-finite-normal-product`
- `lem-weil-pbc-reduced-zerodivisors-union-minimal-primes`
- `lem-weil-pbc-primes-of-localization`
- `lem-weil-pbc-affine-open-section-vanishing-prime`
- `lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions`
- `lem-weil-pbc-finite-algebra-is-integral`
- `lem-weil-pbc-noetherian-finitely-many-minimal-primes`

They served the explicit affine integral-closure, denominator and localization/gluing route.
The local spreading proof and finite-normal dense-open comparison avoid that route. No unit's
own statement or realized proof step is bypassed: the changed node is below unit `sk-thm-p1`,
and its original statement remains the input to the normalization exact-sequence step.

## Where the brief, the DAG or earlier work was wrong

The original statement and sources were correct. The original proof plan was usable in principle,
but its affine descriptions require substantial scheme/ring identification glue not supplied by
the listed ring statements alone. Existing normalization lifting, spreading and finite normal
comparison give a shorter proof with no new holes. Search queries for normalization/field change
found relative-normalization APIs rather than the whole result; the successful additional search
was `AlgebraicGeometry.spread_out_of_isGermInjective'` (one Loogle hit, Mathlib SpreadingOut).

New uses of existing generic tools, for independent review and maintainer approval:
`lem-sbc-normalization-dominant-lift` and `lem-sbc-finite-normal-dense-open-iso`
(unit `sk-prop-input-spreading`), plus `def-nagata-maximal-isomorphism-open` and
`lemma-nagata-maximal-isomorphism-open` (unit `sk-lem-nagata-sketch-near-closure`).
These are respectively the universal property of integral normalization, uniqueness of finite
normal extensions on a dense open, and a union-of-opens construction for a target-local property.
Their use invokes no spreading proposition, Nagata compactification theorem or alternative
proper-base-change route. Import-direction checks found no cycle. Their node ids are recorded
in `proof_deps`; the worker has not added maintainer-owned `tool_uses` approvals.

The queue snapshot showed `ReducedNormalization` as unclaimed, but the live delivery guard
rejected its optional proof completion as an unforced adaptation of a held module. That change
and its change record were removed from the delivery. The assigned theorem is proved from the
existing component-integrality declaration, as the brief permits for stated dependencies.

No statements are disputed and no target statement, public signature, object construction or
visibility has changed. There are no new nodes and no forced adaptations of another group's work.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
