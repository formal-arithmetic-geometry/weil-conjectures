## What changed

Proved the existing theorem
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange_app_mono`
in `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono`.
Its signature is byte-for-byte unchanged. The ordinary abelian-sheaf base-change isomorphism
puts the pullback of extension by zero in the essential image of extension by zero. Forgetting
module structure detects invertibility of the linear counit, and scalar transport gives the
module counit. Exact derivation and restriction to bounded constructible objects preserve this
invertibility. The unit, square comparison and counit in the given formula are therefore
isomorphisms, so the exchange component is monic.

Reuse the existing private `openUnitIsIso` with the proof-only
`import all Sheaf.Paper.CondensedOpenClosedRecollement`; the earlier copied helper was rejected
by the duplicate check and is absent. The other proof-only imports supply ordinary abelian
base change and its fully faithful extension-by-zero functor. The public import is unchanged.
The node `stage3-sfb-open-base-change-component-mono` records this route and its dependencies.
No other source module, definition, existing statement or visibility changes.

## Proved and sorry left

One existing hole closed:
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange_app_mono`
(node `stage3-sfb-open-base-change-component-mono`). Zero holes added; zero local `sorry`s left;
zero statements split off. This is one proof closure, not a decomposition. Relative to the
first worker's already completed sandbox proof, the second reading closes no additional hole.

Remote compilation succeeds. Scratch `#print axioms` checks for every retained private helper
and the item theorem show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from
upstream open declarations. This is a local proof closure, not a claim that the entire import
closure is already sorry-free. No data witness is chosen from an unproved existence statement.

## No longer needed

The old direct proof import
`WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale` is replaced by the used ordinary
abelian `FiniteCoefficient.LowerShriek.Open.BaseChange` module; its weakly-etale dependency
node remains used through that construction. The second reading removes the redundant direct
`Sheaf.Paper.ProfinitePointPullback` import: its comparison remains available through
`import all Sheaf.Paper.CondensedOpenClosedRecollement` and is still used.

The copied `openUnitIsIso` is absent. The second reading also removes the private
`boundedOpenUnit` declaration and places its short derivation at its single use: the existing
`boundedOpenUnitIsIso` in `ModuleObject.Derived.ShriekComposition` has the same statement, but
importing that module here would cycle through `LowerShriek.MorphismDefs` and this item.
No old proof-dependency node or whole module is pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery duplicated the private `openUnitIsIso` already proved in
`Sheaf.Paper.CondensedOpenClosedRecollement`. Reuse through `import all` repairs that fault.
The inherited docstring describes a stronger comparison-of-exchange-maps argument; the actual
proof needs only essential-image support and the actual adjunction counit, as the updated node
explains. No linear comparison of the two exchange transformations is assumed or needed.

The previous report described only the duplicate-helper repair and omitted the proof closure
relative to the repository's remaining `sorry`; this report now states both baselines explicitly.

## Second reading by C3

1. Compared the whole delivered module against the read-only repository and compared the
   existing theorem signature programmatically, byte for byte: identical. The condensed ring,
   prime and characteristic assumptions, four separated finite-type schemes, open immersions,
   cartesian square, equality to the exact exchange composite, and monomorphism conclusion
   all remain unchanged. No construction body or public import changed; no change record is
   needed. Only the item module and its existing node are delivered.
2. Compiled the module remotely through `lcompile.py` without errors or warnings. Inspected
   all five retained private helpers and the public proof. There is no local `sorry`, axiom,
   unsafe/opaque/external declaration or skipped kernel check. Scratch axiom checks give only
   the permitted axioms and inherited `sorryAx`. The linear counit is detected by `Mod.forget`;
   the scalar adjunction counit is invertible because its right adjoint is fully faithful.
   The derived essential-image argument uses a natural isomorphism, not chosen witnesses.
3. No new statement or hole was split off. Searched `lean/Sheaf` and the upstream Lean tree
   for counit, cartesian support and bounded-unit alternatives, and queried Loogle through
   `msearch.py` for `CategoryTheory.Adjunction.isIso_counit_app_of_iso`; it confirms the generic
   Mathlib theorem already used. Found the duplicate bounded-unit helper downstream and
   inlined its single-use argument to avoid a duplicate declaration and an import cycle.
   The support argument also covers identity opens, the empty open and the zero complex;
   it needs no nonemptiness, stalk choice or extra coefficient hypothesis.
4. Read the blueprint `thm-sfb-dc-open-base-change-iso.md`, the unit `_section.md`, and
   `dag/units/sk-def-sfb-open-base-change.json`. The unit--square--counit route is retained
   exactly by rewriting `hα`; no unit-level step is bypassed. The ordinary abelian exchange
   proves support, the derived/restricted counit and open unit are isomorphisms, and their
   displayed composite is consequently invertible. Removing each of the three retained
   proof imports causes a compiler error (missing helper, missing base-change isomorphism,
   or missing fully faithful instance). Removing the direct profinite-point import compiles,
   so it is removed. Every old proof dependency remains used; no whole module is pruned.
5. Read the changed node and its four dependency records against the proof. The five proof
   steps match abelian support, module counit transport, exact derivation, full-subcategory
   restriction, and the final exchange composite. `proof_deps` is precisely the union of
   their cited dependencies; the weakly-etale result remains behind the ordinary exchange.
   The profinite comparison and recollement helper are existing proved declarations of
   their cited modules. Only `proof`, `proof_deps`, and `proof_origin` differ in the node;
   its statement, Lean signature, chapter and unit are unchanged. The unit's `realized`
   record is unchanged.

Second-reading changes: removed the redundant profinite-point import; removed the duplicate
private bounded-unit declaration by inlining its single use; corrected the report to describe
the full proof, its closure count, pruning and inherited axiom limitation. No mathematical
statement or definition was repaired or weakened.
