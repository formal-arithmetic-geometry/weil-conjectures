## What changed

`lean/Sheaf/CategoryTheory/ThirdValueConstruction.lean`: replaced the sole `sorry`
in `CategoryTheory.Functor.thirdValue_core` by a complete construction and comparison
proof, from the existing dependencies and one new diagram-level theorem. Its signature
and public imports are unchanged. Added the proved private helper
`bijective_retraction_hom_colimit`, which checks that a retraction-stage comparison
is the inverse of the essentially-constant cone Hom-colimit bijection.

The proof constructs compatible retractions, completes the denominator square by
TR1/MS6, and constructs the candidate distinguished triangle and its comparison
morphism by TR1/TR3. It then proves the first two comparisons over the triangle
indexing category and composes the third comparison with Mathlib's final-functor
colimit comparison. There is no arbitrary object chosen from a new unproved
existence theorem: the only new hole is a proposition about supplied diagrams,
triangles and morphisms.

Added the proof-only import `Sheaf.CategoryTheory.TriangulatedHomColimitComparison`
and `Mathlib.CategoryTheory.Limits.Final.Type`. Updated the existing node's proof,
proof dependencies and proof origin to match the actual construction.

Both sandbox modules compile cleanly with `lcompile.py --all`.

## Proved and sorry left

Closed the original hole in `CategoryTheory.Functor.thirdValue_core`
(node `lem-pur-derived-functor-triangles-05sc-third-value-core`). There are no
remaining sorries in the assigned module.

Added one named hole: `CategoryTheory.triangulated_hom_colimit_comparison`
(node `lem-pur-triangulated-hom-colimit-comparison`), in the new module
`Sheaf.CategoryTheory.TriangulatedHomColimitComparison`. Its proof is exactly
`:= by sorry`; its docstring gives the complete five-term Hom argument.

This is a decomposition: one upper hole closed, one strictly smaller argument
step added, net zero holes. The remaining theorem has no localization system,
no functor F, no derived values, and no existential candidate or denominator.
It takes a diagram of distinguished triangles and an already constructed
triangle morphism, and upgrades two supplied Hom comparisons to the third.

## No longer needed

Removed the direct proof import
`Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantCofinal` and the dependency
`lem-pur-essential-constant-cofinal-0a1s`. This route does not restrict or extend
essentially constant cones: it transports the Hom-colimit comparisons directly
using the initial projections' opposite final functors.

Removed the redundant direct import
`Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro`; its definition node
`def-pc-essentially-constant-pro-diagram` is still needed and available through
the unchanged statement imports and Hom-colimit theorem.

The older plan's extra cofiltered equalization in the construction is unnecessary.
The common-stage witness at the MS2 square directly gives compatible retractions.
No equalization lemma is imported for that step.

The filtered-colimit exactness node and five-lemma node are now dependencies of
the new comparison node, rather than direct proof dependencies of the assigned
node. They are still needed. No other node or module is pruned by this proof.
Whether the removed cofinal module leaves the targets' whole import closure
depends on its other importers; this report makes no whole-library pruning claim.

## Where the brief, the DAG or earlier work was wrong

The previous DAG plan prescribed an unnecessary equalization and treated the
essential-constancy restriction theorem as necessary for the Hom comparison.
The direct factorization and final-colimit comparison above remove both steps.
The declarations recorded in the DAG do not themselves give the five-term
comparison with the needed representative formula. That step is isolated in
the new theorem, with the supplied triangle and morphism as data.

The local clone has no `literature/stacks-project/derived.tex`. I read the
source at https://stacks.math.columbia.edu/tag/05SC, especially the displayed
five-term Hom diagram and exact-filtered-colimit/five-lemma argument. The new
statement is its contravariant/cofiltered dual and preserves that proof route.
The unit `sk-def-sf-operations` has no realized statement or proof-step nodes
that this change bypasses.

## New nodes

`lem-pur-triangulated-hom-colimit-comparison`: the single general five-term
Hom comparison described above. Its statement, source, four proof steps,
proof dependencies, verbatim Lean signature and three kinds of Mathlib search
are recorded in `dag/nodes/sec-smooth-purity/` in the sandbox. LeanSearch was
unavailable with an Internal Server Error; LeanFinder, Loogle and local searches
returned exactness/final-colimit building blocks, but no matching diagram theorem.
The existing upper third-value/value-triangle nodes cannot be imported without
circularity and do not replace this independent step.

Edge-case checks: for a terminal constant diagram, the hypotheses say the first
two components induce bijections on all contravariant Hom sets, hence are
isomorphisms by Yoneda; the assertion is precisely the usual triangle five lemma.
For the zero category all comparisons are singleton bijections. Empty J is
excluded by `IsCofiltered J`. The hypothesis is quantified over all test objects,
so it includes the shifted test objects needed for the outer two shifted terms.
No triangulated (octahedral) axiom, saturation hypothesis or smallness relation
between the stated universes is needed; only pretriangulated Hom exactness is used.

No definitions or existing interfaces changed; no forced adaptations or change
records were required. The second reader used a temporary axiom-probe copy, removed before delivery.


## Second reading by T1

1. **Interfaces — pass.** Compared the assigned module against the repository with
   `diff -u`, and separately compared the text from `theorem thirdValue_core` through
   its final type before `:= by`: byte-identical. The three public imports, universes,
   namespace and public section are unchanged. No existing definition changes, no
   target changes and no forced adaptations occur. The new private theorem is proved.

2. **Proof and axioms — pass as a decomposition.** Independently compiled both
   delivered modules with `lcompile.py --all`: no errors or warnings. Scanned both
   files for forbidden declarations and every `sorry`: precisely the single named
   `triangulated_hom_colimit_comparison` hole remains in its separate module.
   A temporary scratch copy with `#print axioms` gave only `propext`,
   `Classical.choice`, `Quot.sound` for `bijective_retraction_hom_colimit`; the public
   upper theorem and comparison theorem additionally use `sorryAx`, as reported.
   The upper theorem therefore has a complete reduction, not an unconditional proof.
   The cone maps and retractions are extracted from supplied hypotheses. The derived
   arrow is determined by the uniqueness clause of `leftDerived_value_morphism`;
   both triangle completions and their comparison use Mathlib's proved TR1/TR3,
   and the denominator completion uses the supplied MS6 property. The new open
   theorem supplies no objects or morphisms. No hollow construction is present.

3. **New statement — pass.** Read the displayed Hom diagram and exact-colimit/five-
   lemma argument at https://stacks.math.columbia.edu/tag/05SC and checked its LF
   dual. The sequence is Hom(second[1],W) -> Hom(first[1],W) -> Hom(third,W) ->
   Hom(second,W) -> Hom(first,W). All diagrams are distinguished by hH/hU, and
   the three equations of m make the representative maps commute with its arrows.
   Applying h1/h2 to W[-1] supplies the first two comparisons through the natural
   shift equivalence; filteredness of J opposite supplies exactness. Only
   pretriangulated axioms are needed; no octahedral assumption is hidden.
   For a singleton constant diagram this is the usual triangle five lemma, for
   the zero category all maps are singleton bijections, and an empty diagram is
   excluded both by IsCofiltered and the supplied j0. The statement removes all
   denominator and candidate-value construction, so is strictly one argument step.
   Independent LeanFinder search for exact sequences of cofiltered triangles,
   Loogle search for `"yoneda_exact"`, and grep for `yoneda_exact₃` and the algebraic
   five lemma found exactness and five-lemma building blocks, not this comparison.
   Also searched lean/Sheaf/CategoryTheory, lean/WeilConjectures/CategoryTheory and
   the upstream CategoryTheory sources. No duplicate or brief proof of the remaining
   statement was found. Its docstring supplies the complete mathematical argument,
   and its node records its signature, source and dependencies.

4. **Reduction and pruning — pass.** Read the reduction from the desired third
   comparison downward. The common-stage equation gives compatible first two
   retractions directly; the old extra equalization is unnecessary. The helper
   proves that the retraction comparison is inverse to the existing 05PZ map.
   Final-functor colimit comparisons transfer these bijections to the triangle
   indexing category and transfer the third one back with the exact representative.
   The removed cofinal essential-constancy import/node is unnecessary; the redundant
   direct pro-definition import is removed but its node stays needed. Every other
   old dependency remains either directly or through the new comparison node:
   filtered-colimit exactness and the five lemma are not claimed as pruned.
   All new public imports supply notions in the new signature; the new imports of
   the assigned module are proof-only. The unchanged unit sk-def-sf-operations has
   empty realized.statement and realized.steps, and this reduction replaces no unit
   statement or realized proof step. No additional global pruning claim is made.

5. **DAG — pass.** Parsed both node files and checked that proof_deps is exactly
   the union of the proof steps' uses, all dependencies exist, and the existing node
   differs only in proof, proof_deps and proof_origin. Checked each cited interface:
   05SA gives the unique arrow and denominator-square compatibility, MS2/MS6 give
   the denominator construction, TR1/TR3 give the triangles and morphism, 05R9
   gives cofilteredness and initial projections, and 05PZ includes the representative
   formula required by the helper. The new node's filtered-exactness and five-lemma
   dependencies are Mathlib leaves with the requisite statements. Its creation,
   chapter/unit, source, Lean signature, searches and proof origin match its file.

**Changes by the second reader:** added this independent review and clarified the
scratch-probe record. No Lean code or node repair was necessary. Holes closed: the
original thirdValue_core hole. Holes added: triangulated_hom_colimit_comparison.
This remains a one-for-one decomposition with net zero holes, and no additional
split-off statements were introduced during the reading.
