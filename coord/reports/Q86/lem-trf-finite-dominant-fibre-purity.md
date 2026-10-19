# Worker report: lem-trf-finite-dominant-fibre-purity

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finite-dominant-fibre-purity.json`: statement, split in six steps; no exact Mathlib match and no new nodes.
- `citations.json`: one verbatim statement quotation for each of the 20 step/node citation pairs.
- `searches.jsonl`: actual msearch results for this item, retained with their original queries.
- `report.md`: this report and self-review.

There was no earlier sandbox node or report to continue. The repository item was unsplit. Its existing searches and all ancestry/creation metadata were retained; the new search records are appended. There are zero new nodes and zero new Mathlib leaves. No unit realization changes are needed: the key node of sk-i-curve-zero is lem-trf-local-term-locality, not this auxiliary item.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the exact blueprint id and by finite-dominant/fibre-purity terminology found no declaration stating the item. The read-only master source also has no matching tag. Generic finite-fibre declarations in the source do not state fibre purity. No upstream sorry declaration was treated as a finished proof.

## WANTED

None. All ingredients used are available in the local Stacks sources and existing DAG.

## Corrections and source route

The mathematical statement is unchanged: S remains integral Noetherian; C and D remain integral and finite type over S; r remains finite dominant over S; every nonempty C_s is pure of the one fixed dimension n; the same conclusion is proved for every nonempty D_s. The reference attached to “dominant” was corrected from def-weil-surjective-morphism (which defines a different property) to the existing def-sbc-normal-dominant-galois (which explicitly defines dominance as dense image). This is a citation correction, not a strengthened hypothesis. Surjectivity of r is proved in Step 1, not assumed.

The old source field pointed to more-morphisms.tex, but Tag 02FZ is morphisms.tex, label lemma-openness-bounded-dimension-fibres. I corrected the source pointer and identified the exact other labels: Algebra 00OK, lemma-integral-sub-dim-equal; 00OY, lemma-Noether-normalization; Varieties 0A21, lemma-dimension-locally-algebraic. These results do not individually state the item, so proof_origin is agent, not document.

The inherited source prose and the parent's Step 5 advertised a “standard going-up argument” that a component upstairs maps onto a component downstairs. Going-up alone does not provide this lifting of generizations from a specified point; that is not a proof of the needed assertion. The delivered split instead computes local fibre dimension at the generic point of the total space D, then uses the genuine upper semicontinuity theorem on D. It is essential that the computed point is the generic point of D, rather than merely the generic point of some fibre component: any nonempty open upstairs contains it. This supplies exactly the missing lower-bound argument without asserting that a general integral extension has going-down. No change to the parent's file is made.

I read the chapter record, the sk-i-curve-zero unit record, the current main-20261015 unit statement and lem-trf-local-term-locality proof, and the immediate parent's existing split. This node is a general dimension tool inside the parent's finite-cover step, along its recorded specialization/normal-cone ancestry; it does not replace the contracting-correspondence route of the unit. All off-unit statements are explicitly declared in split_report.tool_uses as general scheme/topological dimension tools. No SGA source is used.

## Searches and reuse

Whole-DAG searches by 02FZ, 00OK, 00OY, 0A21 and fibre-dimension terminology found the exact existing ingredients. `tools/blueprint_refs.py search` was run for “fibre dimension”, “finite surjective”, “finite dominant”, “pure dimension” and “02FZ”; none states this item. The ancestor command confirms lem-trf-local-term-locality, and the item's existing precise from.place and via are retained; same_as is empty. In particular the existing finite-surjective dimension node is about total dimension over a field, not about pure relative dimension over S, so it is an ingredient rather than a duplicate of the item.

Logged msearch calls include two distinct LeanFinder phrasings, a Loogle pattern combining IsFinite and IsDominant, two source grep patterns in AlgebraicGeometry, and a LeanSearch query on upper semicontinuity of fibre dimension. All services answered. LeanFinder gives finite/discrete fibres of finite scheme morphisms, stability of integral maps, and generic dominance infrastructure. LeanSearch gives general upper-semicontinuity definitions. None gives the claimed scheme theorem. Source grep hits in Finite.lean concern closed immersions and finite monomorphisms; AlgebraicCycle/Basic.lean:65 is explanatory prose about equidimensionality. I read that prose and the fibre definitions; these are not candidate matches for the theorem. No Mathlib leaf was fabricated from this infrastructure. Existing historical search records in the item remain historical records, not claims that Q86 reran those exact queries.

## Unfinished work

None at this stage. This is a one-level split using existing statement nodes as interfaces; no Lean was written or compiled. The item still awaits the maintainer's independent review after delivery.

## Not duplicates

No new nodes. Existing nodes were reused for all non-elementary inputs. The local generic-fibre irreducibility argument is a short subspace argument in Step 2, not a new lemma node or a restatement of a clause of the item.

## Review by Q86

I read Stacks morphisms.tex at 02FZ, 01WL (lemma-base-change-finite), 01WN (lemma-finite-proper), 01S1 (lemma-base-change-surjective), and 01T6 (lemma-finite-type-noetherian); algebra.tex at 00OK and 00OY; varieties.tex at 0A21, especially parts (3) and (5); schemes.tex at 01IS (lemma-scheme-sober) and 01K1 (lemma-fibre-topological); and topology.tex at 0055 (definition-Krull) and 0B7I (lemma-dimension-supremum-local-dimensions). The item is an agent-written consequence of these statements, with no additional flatness, properness, normality, dominance over S, or generic-fibre hypothesis. No new node has a separate source to audit.

For Step 1 I opened lem-weil-pbc-finite-closed-map-finite-fibres: its statement explicitly makes r a closed map. The definition in def-sbc-normal-dominant-galois supplies dense image, so closed plus dense proves surjectivity. lem-weil-pbc-finite-morphism-permanence explicitly gives finite base change; lem-weil-pbc-surjective-base-change gives surjective base change; lem-sfb-finite-type-composition-base-change supplies finite type of the two fibres; lem-weil-pbc-finite-type-over-noetherian supplies their Noetherian property over a field. The map r_s is the base change along C_s, not an assumed unrelated map. All hypotheses match the item. The Noetherianity of Spec of a field is the elementary observation that a field has only two ideals and its spectrum has one point.

For Step 2 I opened def-pc-integral-scheme, lem-sc-scheme-sober, def-sc-generic-point and def-pc-scheme-fibre. They respectively give nonempty irreducibility, unique generic points, the dense-singleton meaning of generic, and the homeomorphism of a scheme fibre to the actual inverse-image subspace. Continuity and surjectivity prove r(xi_D)=xi_C. A subspace containing a generic point has that point dense: every nonempty relative open comes from a nonempty ambient open, which contains the generic point. This is the whole elementary argument, explicitly written for both fibres. It uses only irreducibility of these fibres and makes no assertion about their reducedness or integrality after field extension. The common image t need not be the generic point of S; this check avoids an unstated dominance hypothesis on C→S.

For Step 3 I read lem-sc-finite-surjective-dimension: it states equality of total dimensions for nonempty finite-type schemes over an arbitrary field, exactly the situation for r_t. The irreducible fibre C_t is its only component, so its dimension n follows from the item's existing hypothesis, not a new lemma. lem-sc-dimension-locally-algebraic explicitly says that local dimension at every point of an irreducible locally algebraic scheme equals its global dimension; it applies to D_t. These cited statements are sufficient, without assuming a componentwise surjectivity theorem for finite maps.

For Step 4 I opened lem-weil-pbc-local-fibre-dimension-open. It explicitly states that the bounded-dimension locus is open in the source D for every nonnegative integer bound, with no flatness or properness assumption. For n>0 the bound n−1 is legitimate. Step 3 excludes xi_D from the open set, and the generic-point definition therefore makes it empty. This is the lower bound; an openness assertion alone without the total-space generic-point calculation would not suffice. For n=0, def-kun-topological-dimension-at-point says local dimension at a point is nonnegative, so no negative-index openness theorem is invoked.

For Step 5 I opened lem-sbc-equidimensional-open-local-dimension, which assumes locally finite type over a field and exactly the component-purity hypothesis we have for C_s. I take the whole fibre as its open O. lem-weil-pbc-dimension-supremum-local-dimensions states global dimension is the supremum of all pointwise local dimensions; C_s is nonempty, so that supremum is n. The finite-surjective dimension statement then applies to D_s→C_s. Finally, the whole fibre is one of the open neighbourhoods in the definition of local dimension, giving the upper bound. None of these statements assumes algebraic closedness of κ(s), so there is no unnoticed coefficient-field restriction.

For Step 6 I opened lem-sbc-constant-local-dimension-components. Its statement assumes local Noetherianity and constant finite local dimension on an open; Step 1 gives the first and Steps 4–5 give the second. Taking the whole D_s gives every component dimension n. I use this statement, not some construction inside its proof. This is the item's exact conclusion.

I checked the edge cases n=0, empty fibres, a base-image point t which is not generic in S, nilpotents in arbitrary fibres, inseparable finite covers, and a nonnormal base/target. The proof only needs topological irreducibility for C_t and D_t, and allows nilpotents in fibres. Empty fibres are excluded only where nonemptiness is required for dimension equality and local points; the final conclusion is vacuous there. No componentwise going-down or separability is used. Each non-elementary input has a cited existing node, with a verbatim quote in citations.json. The proof-dependency list is precisely the union of step citations. A source-only dependency traversal found no path from any new citation back to this item. There are no new data definitions, no statement-only children concealing the argument, and no new id or duplicate-tag obligations. All six proof steps are below 2000 characters. My corrections were the dominance citation, source-file attribution, and replacement of the unsupported going-up sketch by the explicit generic-point/openness proof.
