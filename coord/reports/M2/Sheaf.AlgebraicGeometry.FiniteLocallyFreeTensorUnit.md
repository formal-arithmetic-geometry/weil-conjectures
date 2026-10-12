## What changed

The proof of `AlgebraicGeometry.Scheme.isIso_tensorPullback_unit_of_finiteLocallyFree`
in `Sheaf.AlgebraicGeometry.FiniteLocallyFreeTensorUnit` now extracts a finite free
cover, localizes the unit, proves its invertibility on finite coproducts by
naturality, transports through the local generator isomorphisms, and descends
invertibility using Mathlib's `Sheaf.isIso_of_coversTop`.

Added proof-only imports of `Sheaf.AlgebraicGeometry.TensorUnitOpenLocalization`
and `Mathlib.CategoryTheory.Sites.LocalProperties`. The private, fully proved
`isIso_app_coproduct` supplies the finite-free calculation. Existing signatures,
visibility, public imports, and docstrings are unchanged. The node proof now
records this reduction.

## Proved and sorry left

Closed the item's one textual hole:
`AlgebraicGeometry.Scheme.isIso_tensorPullback_unit_of_finiteLocallyFree`
(node `lem-sc-finite-locally-free-tensor-unit`). No sorry remains in that module.

Added exactly one hole:
`AlgebraicGeometry.Scheme.tensorPullback_unit_open_localization`
(node `lem-sc-tensor-unit-open-localization`), in the new module
`Sheaf.AlgebraicGeometry.TensorUnitOpenLocalization`.

This is a decomposition: one hole closed, one added, net zero. The theorem still
rests on sorry through localization. Finite-coproduct propagation, the
isomorphism transport, and descent are proved; localization has no finite-local-
freeness or invertibility hypotheses and does not assert the item's conclusion.
Its only remaining task is the restriction comparison and compatibility of units.
No definition is added, and no data definition chooses an arbitrary existence witness.

Both modules compile through lcompile.py without warnings. The generic coproduct
argument permits an empty finite index set. The local lemma permits an empty
open; the cover descent also permits the empty scheme. No rank constancy,
properness, flatness, or quasi-coherence assumption is added.

## No longer needed

None. Both original public imports and both original proof-dependency nodes
remain used. No existing module or node is pruned. No separate finite-free-unit
lemma, projection-formula theorem, or gluing theorem is needed: finite sums and
descent are proved using Mathlib directly.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan is mathematically correct, but its two dependencies do
not state the comparison between restriction and the pullback-pushforward unit.
That missing interface is made precise by the new localization node. The source
Tag 01E8 explicitly omits the local details; these are written out in the new
node and declaration docstring. No existing statement is disputed or changed.
The unit route is retained, and no unit or chapter record is changed.

Mathlib/source searches found the abstract pullback adjunction, slice restriction
functors, and a private object restriction comparison in
`RingedSpaceTensorPullbackPresentation`; none supplies the needed natural unit
comparison. LeanSearch was unavailable and is recorded as unavailable. LeanFinder
and source grep were run. Blueprint searches for 01E8, finite frame, and pullback
restriction found no matching existing localization statement.

## New nodes

`lem-sc-tensor-unit-open-localization`:
`dag/nodes/sec-abelian-varieties/lem-sc-tensor-unit-open-localization.json`,
with module `lean/Sheaf/AlgebraicGeometry/TensorUnitOpenLocalization.lean`.
It isolates localization of the additive pullback-pushforward functor and its
canonical unit on one open slice. The construction and the unit comparison are
spelled out from Stacks Tags 0096 and 01E8. This holds for arbitrary modules and
opens independently of the finite-free argument. No change record is required:
no existing statement, definition, or public interface changes.

## Second reading by M2

1. **Interfaces: pass.** Compared the entire existing module with the repository
   using `diff -u`. The existing theorem signature is byte for byte unchanged,
   including `hO`, finite local freeness, universes, and conclusion. Its visibility,
   docstring, and public imports are unchanged. The additions are proof-only
   imports, a private proved helper, scoped elaboration options, and the proof.
   The additional public theorem is in its own new module. There is no existing
   definition change, forced adaptation, or change record to review.

2. **Proof and trust: pass as a decomposition.** Independently compiled both
   modules in import order through `lcompile.py --all`: 2.8 s and 14.8 s, without
   warnings. A scratch copy with explicit `#print axioms` compiled successfully.
   The private coproduct helper uses only `propext`, `Classical.choice`, and
   `Quot.sound`. Both public theorems use those three and `sorryAx`, as expected
   from the named localization hole. Source scanning found exactly that one
   `sorry`, with body `:= by sorry`, and no forbidden declarations or attributes.
   There are no new data definitions or arbitrary witnesses chosen into data.
   The scratch copy was removed before delivery.

3. **Split statement: pass.** Read the localization theorem, its complete
   construction proof in words, and its matching node. Its comparison has the
   correct direction: restricted modules first enter H, then theta maps them to
   the restricted global pullback-pushforward. The chosen adjunction's existence
   theorem pins its unit to the canonical section formula; it is not an
   arbitrary adjunction. The restricted morphism on p^{-1}U gives the stated
   additive functor. Restricting inverse-image neighbourhoods by intersection
   with U gives the cofinal system, and restricted sheafification has the same
   associated-sheaf universal property. These comparisons preserve the unit
   formula and are natural. Checked U = top (the global comparison), U = empty
   (the zero module category), p = identity, and zero modules. No finite-free
   or invertibility hypothesis is hidden in this statement. It is a strictly
   separate restriction step, not a restatement of the item.

   Repeated searches with different wording through msearch: LeanFinder query
   "restriction to an open subset commutes with the unit of pullback pushforward
   adjunction for sheaves of modules"; Loogle query
   "CategoryTheory.NatTrans, CategoryTheory.IsIso"; targeted Mathlib grep query
   "overFunctor|overPushforwardOverAdj|pullbackPushforwardAdjunction" in
   Algebra/Category/ModuleCat/Sheaf. These searches are in searches.jsonl.
   Also searched both local Lean roots, inspected the private slice comparison
   in RingedSpaceTensorPullbackPresentation, and inspected the open-immersion
   comparison in AffineKFlatPullbackChartComparison. None states the required
   natural comparison together with its unit compatibility. The first exploratory
   Loogle query used an unqualified name and was superseded by the qualified one.
   The localization step cannot be closed in a few minutes from these interfaces.
   Checked the sources directly: [Stacks 01E8](https://stacks.math.columbia.edu/tag/01E8)
   uses the finite-free calculation locally on Y, and
   [Stacks 0096](https://stacks.math.columbia.edu/tag/0096) supplies the canonical
   tensor adjunction. The new docstring spells out the intervening restriction
   argument that the projection-formula source leaves implicit.

4. **Route and pruning: pass.** Read the proof from its conclusion downward:
   reflect invertibility from abelian sheaves, descend from the covering opens,
   transport through the local generator isomorphisms, and use finite-coproduct
   naturality after localization. The helper works even for an empty index set;
   additivity supplies preservation of finite coproducts. The reflection and
   cover steps use Mathlib directly and add no gluing hole. Both original
   dependencies remain used, so `No longer needed: None` is complete. The two
   added imports in the item serve only its proof and are plain `import`.
   The new module's public imports supply the names in its public statement.
   No shorter existing complete route was found. The unit record sk-prop-av-cube
   is unchanged; its existing realized arrays are empty, and this delivery does
   not bypass or alter its stated route.

5. **DAG: pass.** Compared the old node against the repository: only `proof`,
   `proof_deps`, and `proof_origin` change. The dependency union matches the
   written proof, and no original proof dependency is omitted. The new node
   has its source, steps, dependency union, search records, split status,
   provenance, blueprint ancestry, chapter, unit, and Lean record. Its stored
   Lean signature matches the new theorem. The new hole is named in the report
   and node, and has a source and complete natural-language construction proof.

**Changes by the second reader:** Added this independent review and logged the
additional searches. No Lean or DAG repair was necessary. One original textual
hole is closed and one localization hole is added: decomposition, net zero;
no module is pruned. The public theorem remains dependent on `sorryAx`.
