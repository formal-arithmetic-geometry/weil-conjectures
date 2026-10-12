## What changed

Proved `DerivedCategory.exists_pseudoCoherent_approximation_triangle` in
`lean/Sheaf/RingTheory/PseudoCoherentApproximationTriangle.lean`, with its signature
and visibility unchanged. The proof realizes all three steps of
`lem-pc-ring-pseudo-coherent-approximation-triangle`, so its existing DAG route is
unchanged and no node edit is needed.

A proved private helper constructs the brutally truncated first approximation
using the existing `HomologicalComplex.ιStupidTrunc`. It proves preservation of
finite-free terms and upper boundedness, cohomology isomorphisms above the cutoff,
and an epimorphism at the cutoff using Mathlib's short-complex comparison lemmas.
The main proof represents the second target vertex by `Q.objPreimage`, applies
`RingTheory.derived_map_lift`, cancels the representing isomorphism, constructs
the actual mapping cone, proves its finite-free terms and explicit bounds, and
uses TR3 to obtain the morphism of triangles.

Added proof-only imports of
`WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc`,
`Mathlib.Algebra.Category.ModuleCat.Projective`,
`Mathlib.Algebra.Category.ModuleCat.Biproducts`,
`Mathlib.LinearAlgebra.Basis.Prod`, and `Mathlib.RingTheory.Finiteness.Prod`.
No definitions, public statements, dependency modules, or targets changed.

The complete module compiles without warnings via `lcompile.py`. Removing the
projective-module import fails at categorical projectivity; removing the
biproduct import loses `ModuleCat.biprodIsoProd`. The product imports supply the
free and finite instances needed for cone terms. All lines are at most 100
characters. The proof works with independent ring, module, and derived-category
universes, without a `Small R` hypothesis; zero terms and cutoffs outside the
original support are covered by the truncation's zero-term branch.

## Proved and sorry left

Closed 1 existing hole:
`DerivedCategory.exists_pseudoCoherent_approximation_triangle`
(node `lem-pc-ring-pseudo-coherent-approximation-triangle`).

No `sorry` remains in the item. No holes were added or split off. Both private
helpers, `truncIndex` and `exists_truncated_approximation`, are proved.

This is a proof from the existing dependency `RingTheory.derived_map_lift`, whose
proof still reaches `CategoryTheory.precise_vanishing`
(node `lem-pc-ring-precise-vanishing`). Thus the delivery closes the local hole;
it does not claim that the target's entire dependency closure is sorry-free.

## No longer needed

None. Both original imports (`Sheaf.RingTheory.MPseudoCoherent` and
`Sheaf.RingTheory.DerivedMapLift`) are used, and all four planned proof-dependency
nodes remain needed. No node or module is pruned. No import of
`PseudoCoherentIffAllM` is added: its relevant calculation is private and that
module reaches this item, so importing it would create a cycle. Instead the
existing independent truncation-inclusion module is used.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface correction was needed. The DAG plan is usable as
written, including its representation of the second vertex before applying the
lifting theorem. Its unit record `sk-thm-picard-duality` has no realized statement
or step carried by this node; no unit route is bypassed.

The referenced local Stacks source file is absent in this checkout. The proof of
Tag 064R and the lifting lemma Tag 064E were read at the official Stacks pages:
https://stacks.math.columbia.edu/tag/064R and
https://stacks.math.columbia.edu/tag/064E. They give exactly the truncation,
lifting, mapping-cone, and TR3 construction used here. Library search found no
independent theorem proving the whole approximation-triangle statement; it did
find the existing truncation inclusion and a similar private calculation in
`PseudoCoherentIffAllM`.

## Second reading by R2

1. **Interface: pass.** Compared the complete delivered module with the repository
   using `diff -u`, and separately compared the existing theorem signature from
   `theorem` through the text before `:= by`: byte-identical. Its visibility and
   sole public import are unchanged. Only proved private helpers, proof-only
   imports, the proof body, and the authors line were added. There are no other
   delivered modules, definitions, node edits, or change records.
2. **Proof: pass.** Independently compiled the delivered module with `lcompile.py`
   without errors or warnings. A fresh scratch copy of the exact delivered text
   with `#print axioms` for both private helpers and the main theorem confirms
   that the helpers use only `propext`, `Classical.choice`, and `Quot.sound`.
   The main theorem additionally uses `sorryAx` through the existing
   `RingTheory.derived_map_lift` dependency and its open precise-vanishing lemma.
   No local `sorry`, axiom, unsafe declaration, opaque declaration, implementation
   override, external code, or hollow definition occurs. The approximation and
   cone are explicit constructions; no new definition chooses data from an
   unproved existence theorem. The existential lift is used within the proof of
   an existential proposition, not to introduce an arbitrary chosen definition.
3. **Split statements: pass (none).** No holes or split statements were added.
   Read both proved helpers: at the cutoff the inclusion preserves cycles and
   only surjects on homology; above it, all three neighboring components are
   isomorphisms. The zero ring, zero terms, negative cutoffs, and a cutoff above
   the original upper bound cause no exceptional case: absent truncation terms
   are subsingleton, and the original upper bound is preserved. No unjustified
   freeness of kernels or quotients is used. An independent LeanFinder query
   about brutal truncation and cohomology returned smart-truncation results,
   which do not preserve finite-free terms; `rg` located only the downstream
   private calculation in `PseudoCoherentIffAllM`, whose import would cycle.
4. **Route and pruning: pass.** Read the proof from the target downward and
   checked it against [Stacks Tag 064R](https://stacks.math.columbia.edu/tag/064R)
   and [Tag 064E](https://stacks.math.columbia.edu/tag/064E). It truncates the first
   witness at `m + 1`, represents the second vertex, applies the existing lift,
   constructs the mapping cone, and extends the square by TR3. The cone terms
   are `P^(i+1)` plus `F^i`; the explicit interval is
   `[min m aF, max (bP - 1) bF]`. Both original imports and all four original
   proof dependencies are used, so `No longer needed: None` is complete.
   The five added imports are proof-only and supply the truncation inclusion,
   categorical projectivity, the biproduct/product identification, and the free
   and finite product instances. Removal checks fail at the respective uses.
   The unit `sk-thm-picard-duality` has empty realized statement and step lists;
   no unit route is bypassed.
5. **DAG: pass.** Opened the item's node and its unit record. All three recorded
   proof steps and their dependency union match the code, and the document
   proof origin remains accurate. Its recorded Lean signature is unchanged.
   No new node is required for the proved private helpers. No existing node
   needs an edit.

Second reading changed only this report by adding the independent review and
verification evidence. The Lean proof was retained as written. The net local
hole count is one closed and zero added; no module is pruned.
