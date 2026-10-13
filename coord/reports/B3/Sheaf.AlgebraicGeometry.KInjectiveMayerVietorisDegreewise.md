## What changed

In `Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisDegreewise`, replaced the whole-proof
`sorry` of `AlgebraicGeometry.schemeMayerVietorisComplex_degreewise_shortExact` with a
compiling reduction. Its signature and existing docstrings are unchanged.

Three proved private helpers establish epicity of the ordinary open-restriction unit,
the transported unit, and the nested-open image restriction. The ordinary unit is
sectionwise surjective by the already proved `injective_restriction_surjective` and
Mathlib's `Scheme.Modules.restrictAdjunction_unit_app_app`. Epicity passes through the
comparison isomorphism. The proved `schemeOpenModuleImage_unit_restriction` identity
then gives epicity of the nested-open arrow by cancellation. Composing the difference
map with the left biproduct inclusion gives precisely that epic arrow. Thus the right
map's epicity is proved here without a new hole or a sectionwise mate calculation.

The remaining sheaf-gluing argument is isolated in the new module
`Sheaf.AlgebraicGeometry.OpenModuleImageGluing`. Its theorem states a pullback for an
arbitrary module sheaf, with no injectivity or cochain-complex hypotheses. Applying it
to `I.X n` gives exactness and monicity through Mathlib's kernel-fork API. An explicit
short-complex isomorphism uses `HomologicalComplex.biprodXIso`; both unit components and
both restriction components, including the negative V component, are checked in Lean.
Short exactness is transported along this isomorphism.

Added proof-only imports of `Sheaf.AlgebraicGeometry.OpenModuleImageGluing`,
`Mathlib.CategoryTheory.Abelian.CommSq`, and
`Mathlib.Algebra.Homology.HomologicalComplexBiprod`. The existing public import stays.
Updated the item's node proof, proof dependencies, and proof origin to match this route.
No existing statement, definition, instance, visibility, or public import changed.
No forced adaptations are needed.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.schemeMayerVietorisComplex_degreewise_shortExact`
(node `lem-pc-kinjective-mayer-vietoris-degreewise`). No `sorry` remains in the item.
The three private helpers `schemeRestrictUnit_epi`, `schemeOpenModuleUnit_epi`, and
`schemeOpenModuleImageRestriction_epi` have complete proofs.

Added one hole:
`AlgebraicGeometry.schemeOpenModuleImage_isPullback`
(node `lem-pc-open-module-image-gluing`, module
`Sheaf.AlgebraicGeometry.OpenModuleImageGluing`). Its whole proof is `:= by sorry` and
its docstring contains the source and full natural-language argument.

This is a decomposition: one existing hole closed, one new hole added, net zero holes.
The lower statement is only the kernel/gluing part for a single arbitrary module sheaf.
It does not assert short exactness or epicity and is not the original theorem renamed.
The injectivity-dependent epicity argument and the degreewise biproduct/sign comparison
are completed in the item.

Validation: the resumed worker independently compiled both delivery modules through
`lcompile.py --all` (exit code 0). All delivered Lean lines are at most 100 characters.
`deliver3.py B3 Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisDegreewise --no-push`
printed `OK (dry run)`: the delivery compiles and passes the preflight except for the
second reading, which the independent second reader must write. Nothing was pushed.

## No longer needed

Removed the redundant direct proof import
`Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps` from the item. Its definitions are
still available through the unchanged public import of `KInjectiveMayerVietorisData`;
the new gluing lemma also uses its canonical comparison. The definition node
`def-pc-derived-open-restriction-maps` is therefore no longer a direct proof dependency
of the item, but remains needed transitively.

No entire existing node or module is claimed to leave the targets' closure. In
particular `InjectiveRestrictionSurjective` and `KInjectiveMayerVietorisData` remain
needed. No blueprint unit statement or realized proof step is bypassed. The unit record
`sk-thm-picard-duality` has no realized nodes for this item.

## Where the brief, the DAG or earlier work was wrong

The original node's two steps marked the entire sectionwise identification and sheaf
kernel construction elementary. The stated dependencies supplied concrete definitions
and restriction-surjectivity, but did not supply a pullback/kernel theorem for these
transported direct-image objects. This delivery makes that missing part an explicit,
strictly smaller statement with its own node. The remaining comparison inside the new
lemma still needs a Lean proof; it is not presented as already established by Mathlib.

The surjectivity part can be shorter than the original plan: it follows from epicity of
the adjunction unit and the existing unit-composition identity. There is no need to
compute the mate on sections for that part.

The cited local Stacks source and unit `_section.md` files are absent in this read-only
checkout. Read the complete unit JSON and the primary Stacks pages for
[08BV](https://stacks.math.columbia.edu/tag/08BV) and
[01EB](https://stacks.math.columbia.edu/tag/01EB). These support the degreewise sequence
and its sheaf-gluing kernel. `blueprint_refs.py ancestor` returned `None` for the item
because its immediate recorded ancestor is a newly created node. Tracing that node's
record reaches the existing blueprint ancestor `lem-sc-finite-duality`; the new node
records this ancestor and the intermediate route explicitly.

The shortest-route searches found Mathlib's free-abelian-sheaf Mayer--Vietoris complex,
which is a different diagram, and `TopCat.Sheaf.isLimitPullbackCone`, which gives the
section pullback once the concrete maps have been identified. LeanSearch returned an
Internal Server Error; the recorded search is unavailable, not a claimed no-match.

## New nodes

`lem-pc-open-module-image-gluing` in
`dag/nodes/sec-picard-framework/lem-pc-open-module-image-gluing.json` states the pullback
of the actual transported restriction units and overlap arrows. It has one public
statement in `lean/Sheaf/AlgebraicGeometry/OpenModuleImageGluing.lean`, the same universe
as the item, no added hypotheses on the scheme, and a proof plan sourced to 08BV and
the sheaf-condition part of 01EB. Three kinds of actual searches are recorded in the
sandbox search log; Mathlib provides a section-gluing ingredient, not the full
transported scheme-module statement. Local searches found no duplicate node or theorem.

Edge cases checked mathematically: if U is empty and V is the whole scheme, the empty
image terms have unique zero sections and the pullback recovers M; if U=V=the whole
scheme, the square is the identity square under the canonical comparisons. On an empty
scheme every test-open section is uniquely zero. Arbitrary noninjective module sheaves
still have unique compatible-section amalgamations; no surjectivity of their section
restrictions is used in this new statement. A noncover by two empty opens on a nonempty
scheme would fail to recover a nonzero module sheaf, which confirms why the cover
hypothesis is retained. No change records are required because no existing interface
was changed.

## Second reading by B3

1. **Unchanged interface: PASS.** Read the repository/sandbox module diff and
   compared the entire existing theorem signature byte for byte up to `:=`.
   The scheme universe, two arbitrary opens, cover equality, arbitrary cochain
   complex, integer degree, and injectivity of only that degree are identical;
   the conclusion is the same evaluated short exact sequence. Its existing
   docstring, public import, options, and visibility are unchanged. There are
   no definitions or instances added or altered, and no forced adaptations or
   change records. The new module contains only the named pullback theorem.
2. **Proof and trust: PASS as a decomposition.** Independently compiled both
   modules with `lcompile.py --all`. In a scratch copy, printed axioms of all
   three private epicity helpers, the item, and the gluing theorem. The helpers
   use only `propext`, `Classical.choice`, and `Quot.sound`; the item and gluing
   theorem additionally use `sorryAx`, precisely because gluing remains open.
   The only textual hole is the whole proof of
   `AlgebraicGeometry.schemeOpenModuleImage_isPullback`. No axiom, unsafe code,
   opaque declaration, external implementation, hollow definition, or arbitrary
   witness selection occurs. The proof's epic cancellation is in the correct
   direction: the epic smaller unit factors through the overlap arrow; the
   epic overlap arrow factors through the difference map. The short-complex
   isomorphism checks both units and both signed overlap components.
3. **Split statement: PASS.** Read Stacks Tags
   [08BV](https://stacks.math.columbia.edu/tag/08BV) and
   [01EB](https://stacks.math.columbia.edu/tag/01EB), the new node, its complete
   proof docstring, and the actual definitions in `KInjectiveMayerVietorisData`
   and `DerivedOpenRestrictionMaps`. The new statement retains the necessary
   two-open cover, has no injectivity hypothesis, and asserts only the gluing
   pullback. It is strictly the kernel/monicity part, not short exactness under
   another name. The units and nested-open arrows are the concrete transported
   adjunction maps, not replacement maps. Checked U empty/V whole, U=V=whole,
   the empty scheme, and arbitrary noninjective M: unique amalgamation still
   supplies the pullback; no surjectivity is asserted. Without the cover, two
   empty opens on a nonempty scheme cannot recover a nonzero M.
   Fresh logged LeanFinder search `sheaf module restriction direct image open
   cover cartesian square gluing`, Loogle search `"isPullback", "Sheaf"`, and
   grep search `sheafCondition.*[Pp]ullback|[Pp]ullback.*sheafCondition|overFunctor.*[Ll]imit`
   found section gluing, restriction definitions, generic site squares and
   characteristic-map pullbacks, not this transported module diagram. Searched
   both local Lean roots, the upstream algebraic-geometry sources, module-sheaf
   Mathlib sources and DAG nodes for duplicate pullback/gluing statements.
   Read `TopCat.Sheaf.isLimitPullbackCone` in PairwiseIntersections.lean,
   lines 390 onward: it is a sectionwise ingredient. Closing the new theorem
   requires the remaining transported-map comparison, not a few-line application;
   no extra holes were introduced to obscure it.
4. **Route and pruning: PASS.** Followed the proof from short exactness through
   Mathlib's `IsPullback.exact_shortComplex'`, monicity, explicit epicity, and
   `HomologicalComplex.biprodXIso`. Read the supplied, proved restriction-
   surjectivity theorem and the unit-composition identity it actually uses.
   No shorter complete specialization was found. The only old dependency
   removed from direct `proof_deps` is `def-pc-derived-open-restriction-maps`,
   listed above as still transitively needed. No module leaves the closure.
   Read `dag/units/sk-thm-picard-duality.json`: its realized statement list and
   sole realized step list are empty; neither a realized unit step nor the
   chapter route is bypassed. Removed the new gluing module's redundant public
   import of `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic`;
   it compiles with the necessary `KInjectiveMayerVietorisData` import alone.
5. **DAG agreement: PASS.** Existing node changes are exactly `proof`,
   `proof_deps`, and `proof_origin`. Its three steps match the pullback kernel,
   injectivity-dependent epicity, and degreewise biproduct comparison in Lean.
   Each node's dependency list equals the union of its steps' cited nodes.
   The new node has the required source, self-contained statement, proof,
   searches, creation record, blueprint ancestry, chapter/unit and verbatim
   Lean statement; its one named hole matches the report. The existing node's
   statement and statement dependencies are unchanged.

Second-reading changes: removed the redundant public Mathlib import from the
new module and appended this independent review. No proof or statement needed
repair. One original hole is reduced to one strictly smaller gluing hole: this
is a decomposition with net zero holes, not an axiom-free completed theorem.
