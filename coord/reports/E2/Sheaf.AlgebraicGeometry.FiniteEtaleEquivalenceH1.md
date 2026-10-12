## What changed

Proved the sole theorem of `Sheaf.AlgebraicGeometry.FiniteEtaleEquivalenceH1`,
`AlgebraicGeometry.Etale.bijective_cohomologyMap_one_of_finiteEtale_equivalence`,
with its signature unchanged. The proof chooses inverse-image sheaf torsors using the
existing `Sheaf.Torsor.etale_torsor_h1_functoriality`, uses the two new geometric
statements, and performs the injectivity/surjectivity argument with the existing
canonical `Sheaf.Torsor.classH1` equivalences. Quotient induction and quotient
soundness/exactness supply the passage between torsors and their classes.

Added proof-only imports of `Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality`,
`Sheaf.AlgebraicGeometry.FiniteEtaleTorsorReflection`, and
`Sheaf.AlgebraicGeometry.FiniteEtaleTorsorLifting`. Added those last two modules and
matching nodes, and updated the item's proof, dependencies and proof origin.
No existing definition, declaration signature, or public import changed.

## Proved and sorry left

The item's sole theorem now contains no `sorry`; its reduction compiles. It still
transitively relies on the existing inverse-image torsor functoriality theorem and
on the following two newly separated geometric statements:

- `AlgebraicGeometry.Etale.finiteEtale_reflects_torsor_transport`
  (`lem-weil-pbc-finite-etale-torsor-reflection`): a transported torsor isomorphism
  reflects to a source torsor isomorphism.
- `AlgebraicGeometry.Etale.finiteEtale_lifts_torsor_transport`
  (`lem-weil-pbc-finite-etale-torsor-lifting`): every torsor for the inverse-image
  constant coefficient is isomorphic to a transported torsor.

Each has exactly `:= by sorry`, a source and a complete proof in words, in its own
module. These statements concern torsors, not cohomology; neither alone proves the
item. The item's Lean proof combines both with classification and naturality.

Edge cases checked mathematically: empty source and target schemes, the trivial
finite group, disconnected bases, and a base morphism not assumed surjective.
The lifting proof uses the clopen image and reflection of isomorphisms, rather than
an assumption that restriction detects points. The target coefficient in the Lean
proof is always `(upperStar AddCommGrpCat i).obj G`.

## No longer needed

No original public import was removed: all three support the unchanged statement.
The repository refresh during second reading added proof-only imports of
`WeilConjectures.CategoryTheory.Sites.Torsor` and `WeilConjectures.ConstructibleSheaf.Defs`
to the item. These direct imports are redundant through the new proof dependencies
and are removed in this delivery; their declarations are still used and are still
reachable through the proof imports.
No globally redundant module is claimed.

The original direct proof dependencies
`thm-galois-lc-etale`, `lemma-constructible-pullback-constant`,
`def-weil-pbc-cohomology-pullback`, `def-weil-pbc-finite-etale-category`,
`lem-weil-pbc-flat-lfp-open`, and `lem-weil-pbc-finite-proper` are no longer direct
proof dependencies of the item. The geometric ingredients remain in the new
nodes' plans where needed. In particular, the general FEt/FLC equivalence module
`Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence` is not needed
for this route: the helpers use the independent representability statement
`Sheaf.AlgebraicGeometry.FiniteLocallyConstantSetsRepresentability` instead.
The full cohomology classification
`WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent` is not imported;
the already proved sheaf-torsor classification suffices.

## Where the brief, the DAG or earlier work was wrong

The recorded `thm-galois-lc-etale` module cannot be imported by this item:
`LocallyConstantEquivalence` imports `EtaleTorsorDescent`, which imports
`HenselianFiniteEtale`, which imports this item. The import-direction tool also
explicitly rejected importing `EtaleTorsorDescent`. This is a dependency/interface
cycle in the proposed proof route, not a mathematical counterexample. The delivery
avoids it with sheaf torsors and independent geometric substatements, keeping the
unit route (torsor lifting for the henselian H¹ comparison).

The local `literature/stacks-project/` mirror is absent. The sources were read at
[Tag 0A5G](https://stacks.math.columbia.edu/tag/0A5G),
[Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ), and
[Tag 03RV](https://stacks.math.columbia.edu/tag/03RV).
WANTED: the local Stacks `etale-cohomology.tex` and `sites-cohomology.tex` mirror,
Tags 0A5G, 03RV, 03Q1 and 03AJ, for the two new geometric nodes.
The extra action and clopen-image arguments are marked agent-written in their
proof origins. LeanSearch was unavailable (Internal Server Error); LeanFinder and
Mathlib/blueprint grep supplied the other search checks.

## New nodes

`lem-weil-pbc-finite-etale-torsor-reflection`, in
`lean/Sheaf/AlgebraicGeometry/FiniteEtaleTorsorReflection.lean`, isolates the
full-faithfulness argument. It quantifies over arbitrary torsor transports equipped
with an underlying inverse-image sheaf isomorphism and explicit equivariance on
adjunction-unit sections; its conclusion is reflection of torsor isomorphisms.

`lem-weil-pbc-finite-etale-torsor-lifting`, in
`lean/Sheaf/AlgebraicGeometry/FiniteEtaleTorsorLifting.lean`, isolates essential
surjectivity, the lifted action and simple-transitivity map, and the clopen-image
surjectivity argument for the same explicitly specified transports.

No change record is needed: no existing statement or definition changed.

## Second reading by E2

1. **Visible contract — pass.** Compared the delivered item with the repository by
   `diff`. Its sole existing theorem's signature is byte for byte identical, including
   the base-change stability instance, arbitrary scheme morphism, equivalence hypothesis,
   finite abelian coefficient type, and actual inverse-image coefficient codomain.
   No existing definition or public import changes. Restored the original theorem
   docstring; the report describes the assembly instead. The other two modules are new.

2. **Proof and trust — pass for a reduction, not a closed target.** Read both quotient
   inductions. Injectivity uses naturality, target `classH1.injective`, `Quotient.exact`,
   geometric reflection, and `Quotient.sound`. Surjectivity chooses a target torsor,
   lifts it, and uses naturality and quotient soundness. There is no replacement of the
   canonical class map by an arbitrary bijection. All three files compile locally.
   The only delivered sorries are the two named geometric theorems listed above; no
   definition contains sorry and there is no forbidden declaration or trust escape.
   Explicit scratch `#print axioms` checks returned exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx` for the item and both helpers. `classH1` returned only
   `propext`, `Classical.choice`, and `Quot.sound`. The remaining `sorryAx` comes from
   open dependencies; the target is not claimed axiom-free.

3. **Split statements — pass.** Read Stacks Tags [0A5G](https://stacks.math.columbia.edu/tag/0A5G),
   [03RV](https://stacks.math.columbia.edu/tag/03RV), and
   [03AJ](https://stacks.math.columbia.edu/tag/03AJ) and each helper's Lean statement.
   0A5G supplies the finite-etale/torsor route; the helpers isolate its full-faithfulness
   and essential-surjectivity arguments, rather than restating H1 comparison.
   For each helper the arbitrary transport is constrained by an underlying inverse-image
   isomorphism and its action equation. The equation determines translation by every
   constant m via the adjunction bijection; locally constant coefficient sections and
   the sheaf condition then determine the full action. Added this explanation to the
   new docstrings and plans. Reflection lifts an isomorphism and its inverse; lifting
   reflects both simple transitivity and the clopen-image inclusion, so it does not
   assume i is surjective. Checked the identity morphism, trivial group, disconnected
   schemes, and empty schemes. In particular an empty target of pullback cannot conceal
   a nonempty source scheme under an equivalence: the empty finite-etale object and
   the terminal one would become isomorphic and reflection would make them so upstairs.
   Queried LeanFinder independently for fully faithful base change on equivariant
   sheaf torsors and for lifting finite group actions on finite-etale covers, and ran
   Mathlib grep for reflection/lifting/transport and finiteEtale equivalences. The
   results concern condensed sheaves, abstract Galois categories, or finite-etale
   algebras over separably closed fields; none supplies these statements. Searched
   `lean/` for alternate torsor equivalence routes and read the existing representable
   torsor and classH1 APIs. The geometric torsor descent API imports HenselianFiniteEtale
   and hence this item, so it cannot close these helpers without a cycle. Neither
   helper has a short existing acyclic proof available from these interfaces.

4. **Route and pruning — pass.** Read `dag/units/sk-thm-p1.json` and the ancestor
   `lemma-weil-pbc-h1-torsor-comparison` with its blueprint sketch. This remains the
   torsor lifting argument of the strictly henselian comparison step, below the unit
   level; none of the unit's realized statement or steps is replaced. The exact six
   old direct dependencies absent from the new proof are all named under
   `## No longer needed`. They are pruned as direct dependencies, not declared globally
   unreachable. Compared again after the repository refresh and reported both redundant new
   direct proof imports as removed. Kept the existing statement imports; all three new imports in the
   item are proof-only. Removed the new helpers' redundant public imports of
   TopologicalInvariance and OverAdjunction: the needed adjunction API is already
   public through EtaleSheaves. Their remaining imports supply finite morphisms,
   set-sheaf inverse image, and sheaf torsors.

5. **DAG agreement — pass after repair.** The existing node changes only `proof`,
   `proof_deps`, and `proof_origin`, and its three steps match the Lean assembly.
   The new nodes carry the source, creation, blueprint ancestry, chapter/unit,
   search records, Lean declaration, and complete mathematical proof plan.
   Checked the statements of the representability, inverse-image representability,
   pullback-constant, openness, and finite-proper dependencies: they provide the
   ingredients claimed, with Yoneda and the adjunction explaining the action argument.
   Added the missing pullback-constant dependency to reflection, which needs the
   same constant-coefficient identification as lifting. Made each new `lean.statement`
   the verbatim multiline Lean signature, and removed a stray Lean comment terminator
   from each JSON proof text. The source is recorded as agent-written elaboration of
   0A5G, rather than pretending that its clopen-image details are printed in Stacks.

Changes in this reading: restored the existing docstring; clarified action determination
in both new proof docstrings/plans; removed redundant helper imports; repaired the two
verbatim signature records and JSON proof text; added the reflection plan's missing
constant-pullback citation. No theorem statement or proof term was changed.
