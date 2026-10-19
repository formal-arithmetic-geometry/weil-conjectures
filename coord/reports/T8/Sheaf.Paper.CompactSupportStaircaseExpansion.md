## What changed

Completed `AlgebraicGeometry.Etale.compactSupportStaircaseExpansion` in the item module.
The raw component formula and vertical pasting prove the first expansion. Horizontal
pasting, naturality, and the structural composition loop prove the second expansion.
The new module `Sheaf.Paper.DerivedCompactSupportCompositionCoherence` proves that loop
using exact-derived functor coherence and conjugate adjunctions. Its helpers and its
public theorem are all proved.

Repaired the slow selector `compactSupportStaircaseInterchange` by naming the complete
original normalization predicate and its existence theorem. The latter is proved by
`Classical.choose_spec (unboundedProperOpenInterchange A)`. The selector chooses from
this identical predicate, and the pasting calculations use its specification. Every
normalization clause and the same chosen underived family are preserved. Existing
public signatures and the other two definition bodies are unchanged. The new predicate
and existence declaration are attached to the existing staircase node. The change
record is `coord/changes/compact-support-staircase-proof-commands.md`.

The earlier resumed dry run passed and compiled both modules, but its item axiom probe
timed out. Profiling identified kernel checks of the large choice construction, rather
than axiom collection: the generated proof and selector took about 24 seconds, with
later specifications repeating the expression. A separate axiom check of all four
original public declarations found only the standard axioms and existing stated
dependencies. The structural helper's complete axiom probe passed in 5.3 seconds.
The repaired item compiled cleanly in 36.7 seconds, and the structural module also
compiled cleanly. A separate Lean `rfl` test confirmed equality with the original
selector (16.8 seconds). The unchanged direct consumer
`Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons` compiled against the
new overlay in 7.0 seconds. No consumer adaptation is required. On continuation, both retained modules compiled cleanly again against the current
server build: 0.1 seconds for the structural helper and 49.2 seconds for the item.
A fresh `rfl` comparison against the original selector also compiled using the
sandbox overlay in 21.7 seconds. The required resumed dry run passed on this repaired version at commit `61a17cb022`:
both modules compiled, the delivery's axiom probes completed without diagnostics, and
server preflight returned OK with review class CODEX. The push repeats these checks.

## Proved and sorry left

Closed the original hole of
`AlgebraicGeometry.Etale.compactSupportStaircaseExpansion`
(node `lem-amb-compact-support-staircase-expansion`). Also proved the new declarations
`AlgebraicGeometry.Etale.derivedCompactSupportComposition_cancel`
(node `lem-amb-derived-compact-support-composition-coherence`) and
`AlgebraicGeometry.Etale.compactSupportStaircaseInterchange_exists`
(attached to the existing staircase node). There are no textual `sorry`s in either
delivered module: one original hole closed, zero holes added, zero split-offs.
The interchange and open-extension coherence theorems remain stated dependencies;
this delivery proves the item from those declarations.

## No longer needed

Removed direct proof imports `Mathlib.Algebra.Homology.DerivedCategory.KInjective`,
`Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`, and
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition` from the item.
Open-extension coherence remains needed through the structural module. Both original
public imports remain.

The K-injective uniqueness node `lem-weil-pbc-kinjective-hom-derived` and generic
ringed-topos composition node
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition` are not used as proof lemmas:
`rightDerivedLowerStarComp` is the mate of exact-derived pullback composition, so its
associativity follows from `upperStarComp_assoc`, exact-derived coherence, and the
conjugate calculus. Their direct proof imports and proof-dependency edges are pruned.
This does not claim these modules leave the global targets' closure through other
importers. No unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The retained report called the structural lemma an open hole, although its Lean proof
was already present. The generic ringed-topos existence/normalization theorem does not
directly supply associativity of this specific `rightDerivedLowerStarComp`; its mate
definition supplies the shorter route implemented here.

The first timing interpretation blamed linting. The detailed trace showed that the
private-module linter was waiting for asynchronous kernel checks of the selector and
its generated choice proof. Moving the unused-simp linter option was insufficient;
the definition repair shares the complete normalization predicate instead.

Read Stacks `more-etale.tex`, Tag 0F7K, `lemma-pseudo-functor`, and checked both pasting
orders and all original hypotheses. A, C, A+B and B+C give the four binary comparisons.
The structural lemma contains neither interchange maps nor cartesian squares, and
needs only open immersions for l,a,b; p,s,t and the commutative ring are arbitrary.
Identity arrows are allowed, and scheme-associativity transports are explicit.

## New nodes

`lem-amb-derived-compact-support-composition-coherence`, in
`Sheaf.Paper.DerivedCompactSupportCompositionCoherence`, records the fully proved
structural loop used to identify the common six-factor target. It has no split-offs.
Its retained LeanSearch, LeanFinder, Loogle, and grep searches are recorded in
`searches.jsonl`. The exact-derived and mate APIs are implemented in the source library;
no matching structural-loop theorem was found. The new theorem is strictly smaller
than the staircase expansions. The normalization predicate and existence theorem name
parts of the original staircase construction and are recorded on its existing node.
The change record, including all downstream consumers, is
`coord/changes/compact-support-staircase-proof-commands.md`.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
