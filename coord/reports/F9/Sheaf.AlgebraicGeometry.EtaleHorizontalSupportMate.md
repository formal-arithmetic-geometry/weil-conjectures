## What changed

Repair of return bf6cc6581: removed the unnecessary file-level warning-suppression
option from the item. The hole ledger matched the option name as an unattributed
hole at line 28. The actual proof and all public declaration signatures are retained.
The remaining hole is the named public tower theorem recorded below.

`Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate` now proves
`AlgebraicGeometry.Etale.etaleHorizontalSupportMate` from a separately stated geometric
tower normalization. All three existing definitions and the theorem signature are unchanged.
The proof first proves that the sheaf and homotopy normalization equations force every
comparison in `N` to equal the explicitly constructed canonical graph comparison. It
then expands the specified compact-support exchange into proper and open factors,
proves the open factor's mate identity by exact derived descent and iterated mates, and
performs the remaining counit calculation using naturality and triangle identities.
In particular the generic interchange calculation does not assume an invertible unit
for an étale adjunction. The horizontal adjunctions used throughout are the actual
localized adjunctions appearing in the unchanged target statement.

Added `Sheaf.AlgebraicGeometry.EtaleHorizontalSupportTower`, containing the single
geometric statement `AlgebraicGeometry.Etale.etaleHorizontalSupport_tower` before
application of either horizontal counit. It gives a compactification normal form for
the specified composition comparison. It uses canonical graph comparisons, with no
normalization family as an argument.
Its proper factor is the right-adjoint mate of inverse étale sum exchange. The item
proves the rotation identifying that factor with inverse proper exchange. Its source
is the proper/open tower in [Stacks 0F7J](https://stacks.math.columbia.edu/tag/0F7J)
and the proper/quasi-finite interchange construction of
[0F7B](https://stacks.math.columbia.edu/tag/0F7B), with compatibility from
[0F7F](https://stacks.math.columbia.edu/tag/0F7F), used in item (3) of 0F7L.
The original node's proof and dependency list now follow this route.

Replaced the two old proof imports with the new tower module and private proof imports
of proper base change, derived mates, and the open-extension proper-support range.
Existing public imports are preserved. Proved private helpers reproduce the needed
adjunction transport APIs, which are private in their existing modules; no source-library
module or existing public interface is changed. For proper exchange, invertibility alone
is transported across isomorphic left adjoints; this avoids a stronger equality of
adjunctions and the corresponding compatibility import.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.etaleHorizontalSupportMate`
(node `lem-pur-etale-horizontal-support-mate`). Its entire categorical proof compiles.
There are zero holes in the item module.

Added one hole, in
`AlgebraicGeometry.Etale.etaleHorizontalSupport_tower`
(node `lem-pur-etale-horizontal-support-tower`), in its own new module.
This is a decomposition: one original hole closed, one geometric hole added, net zero.
It is not reported as a complete proof of the original result without assumptions.
The geometric lemma concerns arbitrary input on X' before applying counits; the item
separately proves how its proper and open factors give inverse compact-support exchange
under the horizontal adjunction. No definition contains a hole.

Both modules have been compiled together through `lcompile.py --all`. The item also
compiled independently against the compiled new module. A separate temporary import
probe successfully ran `#print axioms` on both declarations: only `propext`,
`Classical.choice`, `Quot.sound`, and the expected `sorryAx` were reported. The probe
was removed from the delivery. The new statement was checked
mathematically on identity squares, the open-horizontal specialization, split finite
étale sheets, empty fibres and zero coefficients. Identity morphisms use the specified
unit normalizations; on split finite étale sheets the units are summand inclusions and
the counits evaluate and add the summands. The open specialization has the displayed
inverse-mate orientation, and empty or zero summands contribute zero. These are
mathematical edge-case checks, not claims of additional Lean test theorems.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint`;
- `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility`;
- the explored proof import
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat`.

The old diagonal/self-product route is unused. Accordingly these old direct proof
dependencies and their corresponding top-level `tool_uses` approvals were removed:
`lem-pur-etale-support-map-compatibility`,
`lem-sfb-quasifinite-compact-support-exact`,
`lem-weil-pbc-etale-base-change-finite-limits`,
`lem-pod-separated-finite-type-base-change`,
`lem-weil-pbc-etale-section-clopen-immersion`, and `pqf-lem-locnoeth-lft`.
The remaining old direct proof dependencies removed from the parent are
`def-weil-pbc-etale-sum-extension`, `lem-amb-shriek-open-exchange-adjoint`,
`lem-weil-pbc-open-immersion-base-change`, and `lem-weil-pbc-proper-base-change`.
The parent still uses the sum functor and normalization in its unchanged statement;
its statement dependencies and public imports have not been removed. The geometric
normalization node may use graph constructions below those existing normalization
interfaces. Thus these are removals from this item's direct proof route, not claims
that all those declarations or modules are globally unused.

No module or declaration is withdrawn. No source-library declaration is removed or
replaced by a hole. The blueprint unit and ancestor composition-compatibility route
are retained.

## Where the brief, the DAG or earlier work was wrong

The returned delivery retained a warning-suppression option from the original item.
Although valid Lean, its name was recognized as an unattributed hole by the landing
ledger. The option is unnecessary once the item proof is complete and is removed.
No landing tool was changed.

The old plan's instruction to use the composition normalization of
`quasifiniteCompactSupportExact` does not directly identify that theorem's existential
comparison family with the fixed family `N`: its statement lacks a derived graph
normalization equation for the existential compact-support comparisons. The original
Lean attachment already notes that its existence theorem is not usable comparison
data. Applying it as though it normalized `N` would leave a gap.

The geometric bridge is therefore exposed as the new canonical graph tower lemma.
Expanding the two composition maps using `unboundedEtaleLowerShriekCompIso_tower`
compiles for the common composite compactification and its two `ofComp` towers.
The declarations for graph refinement/base change do not themselves identify the
proper/quasi-finite interchange factor of those two different composition towers.
That geometric comparison, including its K-injective resolution normalization, is
the retained source result. It is not obtained by postulating the parent counit equality under a second name:
it identifies the composition tower before either evaluation and before mentioning the full exchange
for f. The parent contains the actual formal mate and transport calculation.

A direct comparison between the localized étale derived adjunction and the generic
exact-derived adjunction elaborated poorly. The final proof avoids that comparison:
only the open adjunctions are descended by the general mapped-adjunction mate theorem;
iterated mates then use the localized étale adjunctions directly. No timeout limit was
raised and no definition or public statement was changed to address elaboration.

## New nodes

`lem-pur-etale-horizontal-support-tower`, in
`dag/nodes/sec-smooth-purity/lem-pur-etale-horizontal-support-tower.json`, records the
separate compactification normalization. Its Lean signature is recorded verbatim; its
source, complete proof in words, search evidence, dependency list, original blueprint
ancestor and original unit are included. It contains the sole added hole. The parent
node records the proved categorical reduction from this normalization.

The added node is a decomposition, not a claimed net decrease of holes.

Change record: `coord/changes/etale-horizontal-support-mate-local-proof-attributes.md`.
It records the explicitly local irreducibility commands flagged by the interface detector
and the new tower statement. Existing definitions and statement signatures are unchanged;
the downstream list is recorded and there are no forced consumer adaptations.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
