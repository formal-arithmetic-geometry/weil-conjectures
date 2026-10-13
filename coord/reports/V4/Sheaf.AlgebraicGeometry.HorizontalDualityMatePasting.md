## What changed

The original signature of `AlgebraicGeometry.horizontal_duality_mate_pasting` is unchanged.
Its proof now constructs both endpoint isomorphisms and applies `Arrow.isoMk` to their
commuting square. The new `HorizontalDualityMateComparisons` module constructs restricted
pullbacks and direct images, the fixed composition comparisons, pullback equivalences,
restricted pinned adjunctions, and the right-adjoint transport isomorphism. These definitions
have actual data and no `sorry`. In particular, the target comparison does not choose an
arbitrary witness of an existence theorem. It is produced by conjugation and
`Adjunction.rightAdjointUniq`.

The new `HorizontalDualityMateCommutativity` module states precisely the remaining equality
for these constructed endpoint maps. It does not assert an arrow isomorphism or choose the
endpoints. This realizes step 1 of the existing node and splits off its step 2. The original
node now records this route. New imports in the original item are proof-only imports.

## Proved and sorry left

Closed original hole: `AlgebraicGeometry.horizontal_duality_mate_pasting`
(`lem-sc-horizontal-duality-mate-pasting`), reduced to the fixed-comparison equality.

Added hole: `AlgebraicGeometry.horizontal_duality_mate_commutativity`
(`lem-sc-horizontal-duality-mate-commutativity`), with its full source and proof in words.
This is a decomposition: one upper hole closed, one strictly smaller equality hole added;
net hole decrease is zero. The endpoint constructions are complete, rather than delegated.
No holes remain in the item's module or the comparison definitions. The existing imported
lemmas' holes are unchanged.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`.
The route no longer uses `lem-pc-derived-direct-image-composition`: its existential unpinned
comparison is replaced by the explicitly constructed conjugate of the fixed pullback
comparison. That module/node is pruned from this proof; other users may still need it.

Removed the direct proof import `Sheaf.AlgebraicGeometry.DerivedPullbackComposition`, because
it is available through the existing public statement imports and the comparison module.
The pullback-composition node itself remains necessary and is not pruned.

The alternative `RightAdjointMateSuccessiveBaseChange` module was read but not imported.
Its arbitrary middle comparison does not identify the literal composite in this theorem.
The other old proof dependencies remain used transitively: `lem-pc-qcqs-derived-direct-image-right-adjoint` in the restricted pushforward and target comparison, `def-sc-duality-equation-base-change-map` in the equality, `def-pc-derived-base-change-map` in its pinned adjunctions and ordinary base-change terms, and `lem-pc-ringed-spaces-derived-pullback-composition` in both endpoint comparisons. No other dependency nodes are pruned. The existing unit statement/steps are preserved.

The second reader also removed the unused public import `Mathlib.CategoryTheory.Adjunction.FullyFaithful` from the new comparison module; its definitions use no declaration requiring that import.

## Where the brief, the DAG or earlier work was wrong

No existing signature or mathematical statement was changed. The existing DAG accurately
identifies the two parts of the argument, but its listed composition statements alone do
not provide the specialized fixed-comparison mate equality. The named equality hole now
makes that exact remaining work explicit. The constructed endpoint lemma has no mate
invertibility hypothesis and works independently of the equality step.

The repository copy of the Stacks TeX is absent on this machine. The primary texts were
read at https://stacks.math.columbia.edu/tag/0ATR and
https://stacks.math.columbia.edu/tag/0ATM. LeanFinder returns generic mate laws and
conjugation laws; no specialized fixed-comparison scheme theorem was found. LeanSearch
returned Internal Server Error; this is recorded as unavailable. Identity morphisms,
zero complexes, and empty schemes require no extra hypothesis in the constructions.

## New nodes

`lem-sc-horizontal-duality-mate-comparisons` records the actual source/target comparison
construction in `Sheaf.AlgebraicGeometry.HorizontalDualityMateComparisons`, with no new
holes. Its target isomorphism uses only c,d and their adjunctions, not a,a′ or base-change
invertibility, so it is strictly the endpoint portion of the argument.

`lem-sc-horizontal-duality-mate-commutativity` records the equality remaining after those
endpoints have been constructed, in `Sheaf.AlgebraicGeometry.HorizontalDualityMateCommutativity`.
It includes the numbered naturality, triangle, ordinary-pasting, and conjugation argument.
There are no changes to definitions or signatures of existing modules, no forced
adaptations, and no change records.

## Second reading by V4

1. Compared the delivered item against the read-only repository with diff and a byte
   comparison of its complete theorem signature. Verdict: unchanged hypotheses, conclusion,
   universes, declaration visibility and existing docstring. Only its proof-only imports and
   proof body changed. Both added modules are new; no existing definitions were altered,
   no forced adaptations and no change records are needed.
2. Read all three Lean files, including every endpoint construction. The sole local sorry
   is `AlgebraicGeometry.horizontal_duality_mate_commutativity`, a named public theorem.
   There is no sorry in data, forbidden axiom, unsafe declaration, opaque declaration or
   foreign implementation. The selected composition family is the existing universal-property
   comparison family, not an arbitrary witness of endpoint-isomorphism existence. The chosen
   adjunction is pinned by its Hom-equivalence formula; right-adjoint uniqueness constructs
   the transport map. Compilation and explicit axiom checks are recorded below.
3. Read the new equality and its node against Stacks Tags
   [0ATR](https://stacks.math.columbia.edu/tag/0ATR) and
   [0ATM](https://stacks.math.columbia.edu/tag/0ATM). Verdict: it states the remaining
   commuting-square portion with already constructed fixed endpoints; it does not restate
   existence of an arrow isomorphism. The docstring supplies the naturality, composite
   adjunction, triangle, ordinary pasting, conjugation and inversion argument. Identity
   morphisms use the coherent unit laws; zero inputs have the unique morphisms between zero
   objects; empty schemes add no restriction. Arbitrary supplied adjunction twists are
   accounted for by right-adjoint uniqueness and cancel at the intermediate adjoint.
   Independent searches used “Beck Chevalley transformations composition coherence pullback
   equivalences dualizing functor” (LeanFinder), `CategoryTheory.Adjunction.rightAdjointUniq`
   (Loogle), and searches for composition, conjugation and pasting in both source roots.
   Generic Mathlib uniqueness/conjugation laws are already used in the construction; no
   theorem for this literal fixed-comparison equality was found. Also checked
   `DerivedBaseChangeDomainIso`, `DerivedBaseChangePasting`, and
   `RightAdjointMateSuccessiveBaseChange`: they do not supply this equality. Closing the
   remaining specialized coherence proof is not a few-minute tactic replacement.
4. Followed the old two-step proof plan: endpoint construction, then the mate equality
   and `Arrow.isoMk`. Verdict: the construction is genuine completed work and the equality
   is strictly the remaining part, so this is a decomposition with zero net holes closed.
   All old dependencies are accounted for in “No longer needed”; only the unpinned
   direct-image composition node is pruned. The unit `sk-thm-picard-duality` has empty
   realized statement/step lists in the repository; this delivery changes none of them,
   and does not bypass a realized unit node. Removed the unused public Mathlib import
   from the comparisons module; existing public statement imports stay identical.
5. Compared the existing node field by field. Verdict: only `lean`, `proof`, `proof_deps`
   and `proof_origin` changed. Its two steps and their union now match the Lean calls.
   Both new nodes have source, statement dependencies, proof steps/dependencies, origin,
   searches, status, creator, blueprint ancestry, chapter/unit and Lean records. Each new
   node's Lean statement has been made verbatim, including its line breaks.

Changes by the second reader: removed the unused public FullyFaithful import, made the
new-node Lean statements verbatim, completed the accounting of retained old dependencies,
and appended this independent review. No theorem proof or statement needed repair.

Validation: all three modules compiled without warnings after the import removal.
Explicit `#print axioms` checks on the item, the remaining equality, and five endpoint
constructions showed only `propext`, `Classical.choice`, `Quot.sound` and permitted
`sorryAx`. The source comparison and ambient composition use no `sorryAx`; the target
comparison inherits it from existing imported statements. The first dry run detected a
truncated new-node signature at the conclusion's `let O :=`; corrected the record to
include both let bindings and the whole equality, without changing Lean.
