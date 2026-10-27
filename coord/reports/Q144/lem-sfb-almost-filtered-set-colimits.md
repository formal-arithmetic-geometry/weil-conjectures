# Stage 1 report: lem-sfb-almost-filtered-set-colimits

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-almost-filtered-set-colimits.json — item, statement, split by Stacks 002Y into five explicit steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-almost-filtered-components.json — new statement-only lemma, unsplit; Stacks 002X. No exact or one-line Mathlib match found.
- citations.json — exact statement quotations for all three proof-step citations.
- searches.jsonl — actual msearch.py queries and returned search summaries.

One new node; zero new Mathlib leaves. The proof reuses the existing Mathlib leaf lem-weil-pbc-filtered-colimits-commute-finite-limits (002W).

## Attachments

None. Searches for the blueprint tag, almost filtered/almost directed terminology, componentwise filteredness, and decomposition in lean/WeilConjectures found no project declaration giving the item or the new lemma. Nothing was compiled or written in the read clone.

## WANTED

None: both sources are present in literature/stacks-project/categories.tex.

## Audit and corrections

The imported item was statement-only, with both conditions of Stacks 002X already expanded. I retained all its hypotheses and both canonical-bijection conclusions. Its parsed statement contained doubled TeX backslashes; these were normalized to single TeX commands, without changing its mathematical content. There is no statement dispute. Its original Mathlib search records remain, with the new actual searches appended for this delivery.

I read the chapter record sec-six-functors-basics and unit sk-thm-sf-ctf-stability. The generic site-colimit tool remains below the existing direct-image alteration route. blueprint_refs.py ancestor returns None: the recorded ancestry ends at lem-sfb-admissible-direct-image, whose created.item is the module name Sheaf.SixFunctors.CtfStabilityDirectImages. I preserved the inherited null ancestor and complete via chain, and extended only the new node's via list. The current blueprint/latest places thm-sf-ctf-stability under sec-six-functors/sk-thm-sf-kunneth-verdier; its current proof was read. No chapter, unit, or target statement was changed.

The DAG and whole imported-blueprint searches for 002X, 002Y, almost, disjoint union, filtered category, equalizers, and connected components produced no duplicate for the decomposition lemma. Searching the full DAG statements likewise found no general filtered-component assertion. The existing 002W node is exactly the filtered-colimit fact needed, so I cited it rather than creating another leaf. The new lemma does not assert either clause of this item: it is the independent categorical partition input to the proof of 002Y.

## Review by Q144

I read categories.tex at lemma-split-into-directed (002X), lemma-almost-directed-commutes-equalizers (002Y), and the existing 002W node's full statement and Mathlib match. For the new node I checked both span and parallel-pair conditions against 002X verbatim, including the allowance for an empty category. For the item I followed 002Y's decomposition, filtered comparison, and tagged-coproduct argument, and supplied the two set-theoretic inverses where the source says “Details omitted.”

Step 1 cites the new 002X statement: it gives a partition into nonempty filtered full subcategories with no cross-part morphisms, precisely the structure the later steps need. Smallness follows because the parts are subsets of the small object set and the index is its quotient. Step 2 cites def-weil-pbc-category-colimit only for its stated cocone universal property: compatible maps into a set are the same as one compatible family on each part. There is no theorem smuggled into that definition citation; the disjoint-union universal cocone and its uniqueness are written explicitly. Step 3 cites lem-weil-pbc-filtered-colimits-commute-finite-limits; its statement expressly includes fibre products and equalizers, so both clauses apply to the small filtered I_j, with finite cospan and parallel-pair shapes. I opened each of these three cited statements and copied its full statement into citations.json.

Steps 4 and 5 use only equality of tagged pairs and the identifications already proved. For the pullback, equality of images forces the same tag, and forgetting that repeated tag gives the inverse; for the equalizer, the common tag cancels and leaves the component equality. Their maps on representatives are exactly the canonical comparison maps, so the proof proves preservation by those maps. These are elementary steps, not unreferenced non-elementary lemmas. All five steps are below 2000 characters. The two non-elementary steps respectively apply the independent decomposition theorem and the existing filtered finite-limit theorem, rather than reassigning the item's two conclusions to new nodes.

I checked the empty index (both comparisons empty to empty), a singleton index (identity comparisons), a two-object discrete index (both conditions vacuous, tags essential), and any already filtered index (one nonempty part). The decomposition lemma is true for those cases: empty J, one singleton, two singleton parts, and a single full filtered category respectively. A nontrivial group as a one-object category does not satisfy condition (b): postcomposition by an invertible arrow cannot coequalize distinct arrows. Thus neither hypothesis was silently dropped. No nonemptiness or connectedness was added; no binary-product or terminal-object preservation was asserted.

The new lemma's proof, to guide its later worker, is the argument in 002X: relate x and y when they map to a common target. Reflexivity uses identities, symmetry swaps the arrows, and transitivity uses (a) on the two arrows from the shared middle object. Every arrow joins equivalent objects. Each equivalence class is nonempty; common targets stay in the class; condition (b) coequalizes parallel arrows with target still in the same class. This is recorded here rather than as proof steps of the unsplit new node.

Mathlib candidates were read in ConnectedComponents.lean:135,179 (general decomposition without filteredness), Filtered/Basic.lean:76-98 (the stronger global pair-upper-bound condition), Filtered/Connected.lean:23-35 (filtered implies connected), FilteredColimitCommutesFiniteLimit.lean:159,324,338 (requires IsFiltered), and Limits/Preserves/Grothendieck.lean:72 (requires base preservation already). None is a one-line proof of the new span-condition criterion or the full item. Semantic searches were tried twice with different phrasings; all actual answers and exact queries are in searches.jsonl and the node fields.

I checked delivery-errors B through E against the files: the new node is self-contained, statement-only, uses existing size/colimit definitions, and has the right tag and label; all non-elementary proof uses have statement citations; the three explicit assembly arguments are elementary; no circular dependency or new restatement of the item was introduced. No unapproved source route or SGA source is used.

## Not duplicates

lem-sfb-almost-filtered-components vs lem-sfb-almost-filtered-set-colimits: the new 002X lemma gives a partition of a category into filtered full subcategories and says nothing about set-colimits or their preservation properties; the item proves both comparison bijections using that partition and the existing 002W leaf.
lem-sfb-almost-filtered-components vs lem-sfb-site-left-adjoint-connected-limits: the latter is a theorem about adjoint functors between categories of sheaves on sites, whose comma-category argument uses the item; the new lemma is the independent category decomposition criterion, with no sites, sheaves, or adjunctions.

## Unfinished work

The new decomposition lemma remains unsplit as required for a one-level stage-1 delivery. Its argument has not been placed into its JSON. No other work was left incomplete.
