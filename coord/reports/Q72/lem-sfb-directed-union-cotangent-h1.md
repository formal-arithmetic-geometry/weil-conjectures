# Q72 stage-1 report: lem-sfb-directed-union-cotangent-h1

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-directed-union-cotangent-h1.json`: statement, now split into four proof steps; not itself a Mathlib leaf. Statement and statement dependencies unchanged.
- No new nodes and no new Mathlib leaves. Reused the existing arbitrary-variable polynomial differential basis and presentation-functoriality leaves, together with the polynomial-ring definition.
- `citations.json`: six verbatim statement excerpts, one per step/cited-node pair.
- `searches.jsonl`: five searches actually run with msearch.py; all services answered. Search results and verdicts are appended to the item's earlier searches.

## Attachments

None. Searched the project source for the exact blueprint tag and for cotangent/direct-limit notions. `Algebra.subsingleton_h1Cotangent_of_finite_subfields` in `WeilConjectures/RingTheory/H1CotangentFiniteSubfields.lean` proves a field-extension vanishing reduction, not either full general-ring continuity clause. `TransitivityGamma.lean` contains related finite-support arguments inside a field theorem, not a declaration stating this item. The item is therefore not an attachment.

## WANTED

None. All sources needed are present locally.

## Corrections and discrepancies

The imported statement is correct, including its nonempty directedness assumption; no statement repair is needed. Its empty proof has been replaced by an elementwise expansion of Stacks Tag 07BQ. Rather than appealing to an unspecified continuity theorem, the proof identifies precisely what finite data descend. In particular, a zero class requires a finite product-ideal witness, not just the variable support of its representative. The proof never assumes that the conormal-module transition maps are injective.

The existing `blueprint.from.node` is null and the ancestor tool returns None. I preserved this inherited ancestry and its detailed place/via chain. The current latest blueprint direct-image proof does not itself state this algebra lemma; its place in the DAG is the existing chain through Tag 08TY and the locally dense image-subalgebra comparison. Searches of all imported blueprint nodes for `cotangent`, `directed union` and `07BQ` found no equivalent blueprint statement. The newest text read is under `literature/blueprint/latest/`, not an earlier snapshot.

## Unfinished work

No mathematical step remains for this one-level split. The independent maintainer review and subsequent Lean stages belong to the project workflow.

## Not duplicates

No nodes created. In particular, reused `lem-weil-pbc-polynomial-ring-kahler-basis-any-variables` instead of creating a polynomial-differential lemma. The field-only `lem-weil-pbc-h1-cotangent-finite-subfields` and `lem-weil-pbc-transitivity-gamma` do not state this general-ring continuity result. The sheaf comparison nodes that already cite Tag 07BQ depend on this algebraic input and are not usable as a proof of it.

## Review by Q72

I read Stacks `algebra.tex`, Tag 07BQ (`lemma-colimits-NL`), including its canonical polynomial presentation and its proof identifying the polynomial ring and relation ideal as colimits. I also read Tag 00RX (`lemma-differentials-polynomial-ring`) and checked both tag/label associations in `stacks-project/tags/tags`. I read the full statements of all three cited DAG nodes: `def-weil-pbc-mv-polynomial-ring`, `lem-weil-pbc-polynomial-ring-kahler-basis-any-variables`, and `lem-weil-pbc-nl-presentation-h1-functoriality`. The last two are existing Mathlib leaves, including the arbitrary-index-set and base-changed-basis clauses that this proof actually needs. There are no new nodes needing separate sources or Mathlib searches.

Step 1 takes finite monomial expansions and evaluation uniqueness from the polynomial-ring definition. I checked that renaming an inclusion preserves distinct exponent vectors over the unchanged ring R: its injectivity does not need R to embed in S. The equality between the two evaluation maps is checked on constants and variables. Only the subalgebra inclusion A into S is used to reflect a relation. I wrote out the induction selecting one member for any finite set of labels, including the empty set and the optional requirement to contain a prescribed member. These are direct finite-set and polynomial calculations, not extra unproved lemmas.

Step 2 uses the full statement of the arbitrary-variable differential basis node, not the finite-variable version. It gives both the differential coefficient formula and the basis after tensoring with the evaluated algebra D. I wrote the partial derivative on each monomial, so compatibility with variable inclusion and the vanishing outside its image follow term by term. This avoids using a definition node as though it asserted a base-change injectivity theorem. The statement excerpt in citations.json includes exactly the two basis clauses being used.

Step 3 chooses a polynomial representative of the conormal quotient class. Step 1 places that polynomial in a stage's evaluation kernel; step 2 reflects each evaluated derivative equation by the injectivity of S_lambda into S. All coefficients are in that subalgebra. The basis node then gives the required kernel membership. The presentation-functoriality node states explicitly that the induced map sends a conormal representative to its polynomial image and restricts to the kernel. Its excerpt includes this formula, so the last identification is an equality for the canonical map in the item, with no choice of a different presentation map.

Step 4 uses that same functoriality formula to translate the zero image into membership in I_S squared. I expanded the definition of a product ideal as a finite sum of products of relations, absorbing any polynomial multipliers into a factor. The selected stage contains S_lambda itself and every variable in every factor. Evaluation injectivity places each lifted factor in the stage's relation ideal. Polynomial-renaming injectivity from step 1 then reflects the equality between the lifted representative and the finite product sum. Its quotient class is therefore zero. This verifies the stronger eventual-zero conclusion, without assuming that membership in I_S squared reflects to the original stage.

I checked sections B through E of delivery-errors against the actual statements and sources: no new node repeats a clause, no reference is used as a proof, every non-elementary input is an explicit cited statement, and the proof contains no invocation of a source's unstated standard result. The ordinary finite-support and ideal-product calculations are written out within the steps. All four steps are shorter than 2000 characters. The union and injectivity hypotheses are used only where stated; no flatness, finite presentation, characteristic, field, Noetherian, or small-category assumption was introduced. Constant and zero polynomials, empty variable support and empty product sums are covered by nonemptiness. For a singleton family S_lambda=S the argument gives identity descent and identity zero detection. It also works for the zero ring and rings with nilpotents because it uses coefficient equality and genuine ideal-square membership rather than evaluation on points. A directed union with noninjective conormal maps is allowed: only polynomial renaming and the underlying subring inclusions are treated as injective.
