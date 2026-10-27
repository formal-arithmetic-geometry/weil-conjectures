## Worker report

The module `Sheaf.AlgebraicGeometry.RelativelyClosedConstantsUnitsFG` states
`AlgebraicGeometry.Scheme.relatively_closed_constants_units_fg`, with proof `sorry`.
It is exactly Stacks Project, Varieties, Tag 04L7, alternative (1), read in
`literature/stacks-project/varieties.tex`, lines 5348–5403. No node statement,
accepted proof split, or dependency list is changed. No new notion is defined.
The docstring reproduces the node's five-step proof, including the two still
unstated geometric/valuation inputs.

Hypothesis and conclusion correspondence:

- A field `k`: `(k : Type u) [Field k]`.
- A scheme `X` over `k`: `(X : Scheme.{u})` and
  `[X.Over (Spec (CommRingCat.of k))]`. Its structure morphism is
  `X ↘ Spec (CommRingCat.of k)`.
- Nonempty and connected: `[ConnectedSpace X]`. The recorded Mathlib class
  includes `toNonempty`; a redundant separate nonemptiness hypothesis is unnecessary.
- Reduced: `[IsReduced X]`, the recorded sectionwise definition, equivalent to
  reduced stalks. No irreducibility or integrality of `X` is assumed.
- Locally of finite type over `k`:
  `[LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]`.
  Neither quasi-compactness nor separatedness is assumed.
- Finitely many irreducible components:
  `hcomponents : (irreducibleComponents X).Finite`.
- `A = Γ(X, O_X)`: the actual section ring `Γ(X, ⊤)` throughout.
- The induced inclusion of constants is the ring homomorphism
  `((ΓSpecIso (CommRingCat.of k)).inv ≫
  (X ↘ Spec (CommRingCat.of k)).appTop).hom`.
  The Spec/global-section isomorphism identifies `k` with its canonical global
  sections, and the structure map pulls them back to `X`. It is not an arbitrary
  algebra map.
- Constants form an integrally closed subfield of `A`: `hclosed` is
  `@IsIntegrallyClosedIn k Γ(X, ⊤) _ _ scalarMap.toAlgebra`, with that exact
  scalar map written in place. Mathlib's `IsIntegralClosure` includes injectivity
  of the algebra map and the condition that its image equals the integral elements.
  Thus the node's inclusion and relative integral closedness are both retained.
- `Aˣ` is `Γ(X, ⊤)ˣ`; its subgroup `kˣ` is the `.range` of `Units.map`
  applied to the same scalar map. Every nonzero scalar is a unit in the field,
  and its image is precisely an invertible constant.
- The conclusion is `Group.FG (Γ(X, ⊤)ˣ ⧸ constantUnits.range)`.
  The units of a commutative ring and this quotient carry their existing
  `CommGroup` instances, so abelianness is part of the type. `Group.fg_iff`
  identifies the conclusion with finitely many generating classes; surjectivity
  of the quotient map lets these classes be represented by finitely many units.
  No additional freeness or finite cardinality conclusion is asserted.

Recorded statement-dependency declarations, all read with their source definitions:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  Mathlib.AlgebraicGeometry.Scheme. The same module provides `Scheme.ΓSpecIso`.
- `def-weil-connected-scheme`: `ConnectedSpace`, Mathlib.Topology.Connected.Basic.
- `def-pc-reduced-scheme`: `AlgebraicGeometry.IsReduced`,
  Mathlib.AlgebraicGeometry.Properties.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType. The node's quasi-compact and
  finite-type notions are not hypotheses of this item.
- `def-weil-irreducible-components`: `irreducibleComponents`,
  Mathlib.Topology.Irreducible, whose carrier is maximal irreducible subsets.
- `def-weil-pbc-integral-closure`: `integralClosure` and `IsIntegral`,
  Mathlib.RingTheory.IntegralClosure.Algebra.Basic and IsIntegral.Defs;
  `IsIntegrallyClosedIn`, Mathlib.RingTheory.IntegralClosure.IntegrallyClosed.
  The latter is the exact relative-closedness clause used here, not the
  absolute predicate `IsIntegrallyClosed` on the section ring.

Statement dependency modules are public imports. Stated proof dependencies have
plain imports: `AlgebraicClosure` from Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure;
`Scheme.residueField` and `Scheme.Hom.residueFieldMap` from
Mathlib.AlgebraicGeometry.ResidueField;
`Scheme.IdealSheafData.reduced_induced_closed_subscheme` from the recorded upstream
WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme; and
`Submodule.basisOfPid` from Mathlib.LinearAlgebra.FreeModule.PID.
The integral-scheme notion is already in the public Properties import. The two
proof nodes `lem-sfb-geometric-connected-component-surjective` and
`lem-sfb-integral-units-finite-valuation-map` currently have no Lean attachment;
they are named in the proof docstring, and no duplicate statement is introduced.

Edge cases checked mathematically before writing:

- The empty scheme is excluded by the node and by `ConnectedSpace`, consistently.
- `Spec k` gives the trivial quotient, finitely generated with an empty set.
- The multiplicative group scheme gives quotient isomorphic to the integers,
  showing that finite generation must not be replaced by finiteness.
- Affine space has only constant units, hence trivial quotient.
- Connected reducible schemes remain allowed; the finite intersection-graph
  argument in the docstring applies without an `IsIntegral X` hypothesis.
- Arbitrary characteristic, imperfect fields and nonseparated schemes are allowed.
- Locally finite type is retained without adding global finite type or compactness.
- Universes are explicitly declared, and `autoImplicit false` is set. The common
  universe is Mathlib's scheme/morphism universe; any smaller field and scheme
  can be placed together in a common universe without a mathematical restriction.

Searches made on 2026-10-23 UTC using the prescribed `msearch.py` wrapper:

- LeanFinder: "Global units modulo constant units of a connected reduced scheme
  locally of finite type over a relatively integrally closed field form a finitely
  generated group". Eight hits concerned class groups, number-field units,
  Selmer groups and function fields, none this theorem.
- Loogle: `Group.FG, Units.map, IsIntegrallyClosedIn`. Zero hits.
- Mathlib grep: `units.*(FG|finitely)|Rosenlicht|relativelyClosed`. Five hits,
  concerning inequalities, differential integration, factorization and localization;
  none states this scheme theorem.
- LeanSearch: "A reduced connected scheme locally of finite type over a field
  has finitely generated group of units modulo relatively integrally closed constants".
  Eight hits included number-field unit theorems, reducedness, and
  `finite_appTop_of_universallyClosed`. The latter assumes an integral source and
  universal closedness and concludes a finite ring map, so is not a match.
- `rg` searches in `lean/WeilConjectures` and `lean/Sheaf` for
  `IsIntegrallyClosedIn`, `Units.map.*appTop`, `Group.FG.*Γ`,
  `relatively.closed`, and units/finiteness phrases, plus the exact node id in
  WeilConjectures, found no exact statement. Curve unit quotients modulo powers
  concern different quotients and stronger curve hypotheses. A name-clash search
  for `relatively_closed_constants_units_fg` also found nothing.

No `STATEMENT-DISPUTED` issue, statement correction, dependency repair, or new node.

## Assignment handoff

The inherited BLOCKED ending concerned an already reviewed stage-1 split. The
current queue explicitly lists this item at stage 2, and its node has no `lean`
record. There is no repair note. The stage-2 brief section 0 explicitly directs
continuing under these circumstances with `deliver2.py`, preserving the accepted
split. This delivery adds only its Lean attachment, module and worker report.

The dispatcher brief requires direct delivery and forbids spawning other agents.
The maintainer supplies the independent review; no independent worker reading
is claimed here.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
