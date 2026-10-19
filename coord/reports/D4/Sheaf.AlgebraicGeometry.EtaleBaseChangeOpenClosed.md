## What changed

Proved `AlgebraicGeometry.Etale.isIso_baseChangeMap_app_of_isOpenImmersion_of_isClosedImmersion`
in `Sheaf.AlgebraicGeometry.EtaleBaseChangeOpenClosed` without changing its signature.
A closed immersion is finite (`AlgebraicGeometry.IsFinite.instOfIsClosedImmersion`).
The chosen pullback identification gives `IsPullback` by
`CategoryTheory.IsPullback.of_iso_pullback`; the existing proved theorem
`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite` then makes the canonical
exchange natural transformation invertible, and Lean supplies the isomorphism of its
component at `F`. Added its proof-only import
`WeilConjectures.SixFunctors.Finite.BaseChange` and updated the proof docstring and
DAG route accordingly. The public imports are unchanged.

The finite exchange is already recorded by `lemma-weil-pbc-finite-exchange` (its
`lean.others` records the underived theorem). Its coefficient-category assumptions
are provided by existing instances for `AddCommGrpCat.{u + 1}`. The proof is valid
for empty source or base, and for the identity immersion, since it introduces no
nonemptiness or torsion assumption. The open-immersion hypothesis stays in the
original signature but is unnecessary for this specialization.

The unit `sk-prop-sf-kunneth-ordinary` has no realized statement/steps assigned to
this node; this replacement is below unit level and uses an existing closed tool.
Import-direction checking reports no cycle. The single-file server compile passes
without warnings. An explicit `#print axioms` check reports exactly `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`. The temporary checking command was removed.

Searches: repository `rg` found the finite exchange theorem and Mathlib's finite
closed-immersion instance. LeanFinder returned etale stability and scheme-module
results, without an exact sheaf-exchange match; Loogle's query
`"IsClosedImmersion", "IsFinite"` returned the exact instance and characterization;
the logged grep query confirmed `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Etale.isIso_baseChangeMap_app_of_isOpenImmersion_of_isClosedImmersion`
(node `lem-kun-base-change-open-closed`).

Original holes: 1. Proved: 1. Holes added: 0. Holes remaining: 0. No decomposition
or split-off theorem was introduced.

## No longer needed

Removed these direct proof imports:

- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm` (both duplicate occurrences).
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `Sheaf.AlgebraicGeometry.OpenImmersionRestriction`.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`.
- `WeilConjectures.SixFunctors.BaseChange.Square`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

The last two interfaces remain available through the unchanged public imports;
finite base change also uses stalk theory internally. These removals are direct
import pruning, not a claim that all these modules leave the whole target closure.

The new proof does not separately use the old inside/outside stalk argument or
these old proof dependencies:
`def-weil-open-immersion`, `lem-weil-pbc-open-immersion-base-change`,
`lem-weil-pbc-inverse-image-stalk-germ`, `lem-kun-open-immersion-restriction`,
`def-weil-pbc-direct-image`, `def-weil-pbc-geometric-stalks`,
`def-weil-pbc-underived-exchange`, `lem-weil-pbc-open-immersion-etale`,
`def-weil-pbc-etale-site`, `def-weil-pbc-abelian-etale-sheaves`, and
`lemma-weil-pbc-geometric-stalk-conservative`. Some remain statement notions or
internal dependencies of finite exchange; none is separately invoked here.
The retained direct proof dependencies are `def-weil-closed-immersion` and
`def-weil-pbc-cartesian-square`, together with the finite-exchange tool.
Removed the obsolete top-level `tool_uses` approval for
`lem-weil-pbc-inverse-image-stalk-germ`; no new approval is added by this delivery.

## Where the brief, the DAG or earlier work was wrong

The old five-step stalk argument is mathematically valid but unnecessary once the
existing proved finite exchange theorem is used. No statement, definition, unit
route, or consumer repair was needed. No new nodes.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
