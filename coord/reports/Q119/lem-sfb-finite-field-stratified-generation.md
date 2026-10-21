# Q119: lem-sfb-finite-field-stratified-generation

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-field-stratified-generation.json`: statement, split; no exact Mathlib match. The statement is unchanged. Its five proof steps use existing nodes only.
- `citations.json`: ten entries, one for every occurrence of a node in a proof step, with verbatim portions of the cited statements.
- `report.md`: this report. The search command also wrote `searches.jsonl`; all six Q119 searches were read and appended to the item's pre-existing search records.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact item tag and for stratified/constructible generation found no declaration with this statement. In particular, `AlgebraicGeometry.Etale.constructibleFiniteTor_eq_triangEnvelope_ctfGenerators` in `SixFunctors/Etale/Derived/Stability/Generation.lean:349` concerns the etale site, finite-type schemes over a field, invertible coefficient exponent, finite Tor dimension, and a retract-closed envelope. It does not attach this ordinary pro-etale, arbitrary-Noetherian, finite-extension-only assertion. The ProEtale localizing-generation results likewise do not state the item.

## WANTED

None. All sources needed for the split are available locally.

## What was wrong or incomplete

The assigned node was a statement-only extraction with no proof. Its source references point to a stronger derived stratification discussion, but do not themselves supply the promised explicit finite construction with sheaves as generators. The present split supplies that argument. It uses clauses (1)-(2) of the already-existing `det-sf-flat-model-generation`; it does not infer finite extension generation from that node's retract-closed generation clause (3).

No statement dispute was found. No hypothesis, coefficient convention, or conclusion was changed. The blueprint ancestor is `lem-sfb-dc-hom-preserves`; this item supplies its finite-coefficient devissage input. The item is not its unit's key statement and does not change the unit or chapter records. The proof follows the finite-filtration route, using the blueprint's flat-model lemma and Stacks derived-category triangles. No prohibited source is used.

## Not duplicates

No new nodes were created, so there are no new/existing-node pairs to distinguish. Whole-DAG searches for stratified generation, finite filtrations, flat constructible objects, and truncations, together with `blueprint_refs.py search` for `stratified generation`, `constructible generation`, `finite filtration`, `flat constructible`, and `truncation`, identified the existing facts now cited. The current item is not the general flat-model node: it has field coefficients, arbitrary bounded constructible cohomology, and gives finite extension generation without requiring retracts.

## Mathlib searches

The six actual Q119 searches are preserved in `searches.jsonl` and reproduced with their exact tool/query text and outputs in `mathlib_searches`. All services answered. LeanFinder's first phrasing returned condensed constant-sheaf constructors. Its second phrasing returned bounded representatives and the standard t-structure. LeanSearch returned sheafification, abelian sheaf categories, and generic t-structures. Loogle returned no hits. The first grep returned only constructible-set topology files; the second returned no hits. None states the finite pro-etale stratified-generation theorem or specializes to it in one line. The earlier Q54 search records were retained, not fabricated or rerun as new evidence.

## Review by Q119

I read the current chapter and restricted-functors unit, the current ancestor statement, the item's source passage in Bhatt--Scholze (Lemmas 6.3.3 and 6.3.9, and the filtering argument of Lemma 6.7.13), and the current blueprint file `sk-lem-sf-flat-model/det-sf-flat-model-generation.md`. For the actual assembly argument I read Stacks `derived.tex`, Tag 0152 (`lemma-derived-canonical-delta-functor`) and Tag 08J5 (`remark-truncation-distinguished-triangle`). I also read the relevant constant-field flatness source: `sites-modules.tex`, Tag 03ER (`definition-flat`) and Tag 08FC (`lemma-flat-eq`), and `fields.tex`, Tag 09FN (`lemma-vector-space-is-free`). The proof origin is marked agent because this explicit combination and strengthening to finite sheaf generators is our extraction, not a verbatim theorem in the cited paper.

Step 1 uses the full statement of `lem-exc-constant-field-module-flat`, not just a definition of flatness. It applies to all ordinary modules over the associated constant field sheaf. The item uses that very ring, rather than an adic completion or an unrelated condensed coefficient ring. I checked its extra site hypotheses against the small-skeleton convention and ordinary ring/abelian sheafification. The size convention explicitly permits a common larger universe. `lem-sfb-grothendieck-sheafification` supplies abelian sheafification on that small site; `lem-weil-pbc-site-sheafification-iso-locally-bijective` supplies exactly its locally-bijective criterion. Ring sheafification and composition with the underlying ring functor are the ordinary constructions used for the already-specified constant coefficient sheaf. There is no appeal to conservativity of geometric points on the pro-etale topos. This step is non-elementary and cites its flatness theorem.

Step 2 uses only clauses (1) and (2) and the conventions of `det-sf-flat-model-generation`. I opened that node's statement and checked both sites, arbitrary Noetherian schemes, and ordinary uncompleted coefficients are explicitly included. Finite fields are finite commutative rings, and Step 1 establishes the additional flatness assumption on each cohomology sheaf. Clause (1) supplies the finite ordered strata and finite-projective locally constant restrictions; clause (2) supplies the finite sheaf extension filtration. The statement itself identifies locally closed extension with open extension into the scheme-theoretic closure followed by closed direct image. Over a field a finitely generated module is exactly a finite-dimensional vector space, so these generators meet the item's specification. We do not use an etale/pro-etale comparison hidden inside that node's proof. No finite-type base or invertible-characteristic hypothesis is imported.

Step 3 uses `lem-sf-derived-ses-triangle`, whose statement explicitly gives a distinguished triangle for each short exact sequence of objects of any abelian category. The ordinary module-sheaf category is abelian. The induction starts at the literal zero sheaf in the supplied filtration, and constructs the middle object from the preceding filtration term and the prescribed quotient. This proves the required finite extension assertion for each degree-zero cohomology sheaf; it does not use an unspecified meaning of iterated extension in a triangulated envelope.

Step 4 uses the cohomology formulas actually written in `def-kun-truncations` and the localization described in `def-weil-abstract-derived-category`. This is an elementary calculation: below the lower cohomological bound the upper truncation has no cohomology at all; at the upper bound its inclusion retains all cohomology. Thus the first endpoint is zero in the derived category and the last is isomorphic to the given complex. It does not confuse a complex with bounded cohomology with a termwise bounded representative. No infinite truncation convergence is needed.

Step 5 uses the exact successive-upper-truncation triangle in `lem-weil-pbc-truncation-triangle`. I read the whole statement and take only its existence clause, with the first term tau_LE(q-1), the middle term tau_LE(q), and third term H^q[-q]. Its hypotheses are generic abelian-derived-category hypotheses and impose no etale restriction. The triangulated-category definition provides shifts of distinguished triangles, so shifting the finite construction from Step 3 builds each third term. The induction index is the finite integer interval a through b and the base is the zero endpoint established in Step 4. This yields the actual finite construction of P. It does not infer a finite construction from an abstract localizing or thick-envelope membership statement.

I tested the zero sheaf, acyclic complexes, the empty scheme, a complex with exactly one nonzero cohomology sheaf, and a scheme with only one required stratum. Acyclic objects can use any chosen nonempty bounding interval and start/end at zero; a one-degree object requires exactly its sheaf filtration and one shift. Different cohomology degrees may use different finite stratifications: the union of their finitely many finite generator lists is still finite, and the item does not demand a single preassigned stratification. All five steps are below 2000 characters and contain no omitted comparison lemma.

Against B--E of the delivery-errors checklist: there are no new statement nodes or new definition obligations (B1--B10); all cited results are read from their statements and copied verbatim to the citation file (C1--C5); the delivery leaves cycle and route verification to the required server checks (C6--C8), declaring its generic off-unit tools in split_report; the two explicit finite inductions carry the content rather than moving it into a fresh restatement (D1--D5); and coefficient rings, site, bounds, middle/endpoint orientation, and the absence of extra geometric hypotheses were checked as above (E1--E7). There are no new source-tag collisions to justify and no unresolved mathematical correction.

## Unfinished work

No stage-1 mathematical work remains. Server dry run and direct delivery are the remaining operational steps; their outcome will be reported by the delivery command.
