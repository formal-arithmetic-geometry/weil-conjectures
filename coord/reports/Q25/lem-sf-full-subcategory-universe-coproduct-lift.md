## Worker report

Files written: dag/nodes/sec-six-functors/lem-sf-full-subcategory-universe-coproduct-lift.json (statement, split; no whole-item Mathlib match), citations.json, searches.jsonl, report.md. The item had no previous sandbox copy or report. Its live statement and statement dependencies are unchanged.

## New nodes

None. No new Mathlib leaves. The universal-property arguments are steps, not separate lemmas or nodes restating clauses of the item.

## Attachments

None. The blueprint tag search in lean/WeilConjectures returned nothing. Concept searches in the CategoryTheory and SixFunctors sources found specialized localizing-closure and Brown-representability results, including Triangulated/BrownRepresentability/RightAdjoint.lean:286-294. That declaration assumes the specialized localizing-closure setup and does not give every clause of this item (especially ULift transfer and the comparison formula), so it is not an attachment. No Lean file was written or compiled.

## Sources and searches

Read the chapter sec-six-functors and unit sk-lem-sf-open-ctf, the current main-20261015 blueprint sk-prop-proper-image-localizing-open.proof.md, and the ancestor det-proper-image-localizing-open. The Formal properties and Localizing categories paragraphs are the source motivation; the detailed categorical argument is agent-written and marked accordingly. Read Stacks categories.tex, Tag 002F, label definition-colimit, lines 1310 onward, including the empty-diagram paragraph. Read derived.tex, Tags 014V, 05QM and 05QX, labels definition-exact-functor-triangulated-categories, definition-triangulated-subcategory and lemma-triangulated-subcategory.

DAG title/statement searches across all chapters for full subcategory, creation, reflection, reindexing and triangulated restriction found the existing lem-weil-pbc-triangulated-functor-restriction and lem-weil-pbc-colimit-initial-full-subcategory. I opened both statements. The latter's equivalence clause assumes both colimits already exist; it is unnecessary here because step 1 explicitly constructs a reindexed colimit cocone on the same vertex. The quasicategorical lem-coef-colimit-cocone-transport-equivalence has different objects and is also unnecessary. Blueprint searches via tools/blueprint_refs.py for full subcategory, creates colimits, reindexing coproducts and triangulated functor found no blueprint node stating the item. Its ancestor is det-proper-image-localizing-open. No new node required a duplicate search or a new blueprint lineage.

Ran all Mathlib searches through the prescribed msearch.py, with two semantic phrasings, Loogle, grep and LeanSearch; the exact queries and real result summaries are in searches.jsonl and the item. All services answered. Read Mathlib/CategoryTheory/Limits/FullSubcategory.lean:94-113 (creation and existence), Limits/Preserves/Basic.lean:671 (preservation detected by a reflecting composite) and :806 (fully faithful reflection), and Triangulated/Subcategory.lean:719-745 (inherited triangles and exact lift). These give components; the whole statement additionally needs the explicit change of indexing type and canonical comparison identification. It is therefore delivered as an explicit assembly split, without adding redundant component nodes.

WANTED: none.

## Faults and unfinished work

No statement dispute or source error was found. The imported empty proof is replaced by six explicit steps. No hypotheses were added or conclusion weakened. The route does not infer closure from generators; the assumed closure of P and Q is used exactly where needed. No mathematical work remains for this split. The independent maintainer review follows delivery.

## Review by Q25

I reread the item against its cited blueprint paragraphs and the Stacks universal property, then opened every cited node's statement. For steps 1 through 5 the only cited node is def-weil-pbc-category-colimit: it gives existence and uniqueness of the mediator for every compatible cocone, and uniqueness up to unique isomorphism. Each step writes out the calculation it needs from this definition. I did not use a theorem hidden in a cited proof.

In step 1 the bijections e and d transfer a family of legs in both directions; this proves the larger-index colimit exists on the original vertex before the larger-universe closure hypothesis is used. No assumption of all large coproducts slips in. The two inverse equations verify the exact coprojection identification, so this is a short definition calculation. It works separately for P and Q and for an empty type.

Step 2 uses fullness to keep the actual ambient mediating morphism, and property membership of the ambient vertex follows from step 1. This lifts every ambient colimit cocone. Step 3 proves both directions of the colimit condition: reflection restricts the universal property, while preservation compares an arbitrary subcategory colimit with the inherited ambient one using explicit mutually inverse arrows a and b. Crucially, preservation is asserted only for diagrams whose ambient coproduct exists, just as in the statement. Neither arbitrary colimits nor cocones to objects outside the property are assumed available in the subcategory.

Step 4 checks the canonical functor and uses the assumed ambient preservation plus the proved inclusion preservation/reflection on the actual image cocone. The codomain property follows from the precise hypothesis P(C) implies Q(FC). Step 5 specifies the orientation and defining equations of the comparison M to FL, so equality with the ambient comparison is an equality of arrows in identical Hom sets. Its inverse comes from the two colimit universal properties. This also checks that no unproved comparison transport theorem has been used.

For step 6 I opened lem-weil-pbc-triangulated-functor-restriction: its statement explicitly gives the restriction on objects and morphisms, its inherited shift isomorphisms, exactness, and equality after inclusion as functors with shifts. The item's full replete triangulated hypotheses and image hypothesis meet every condition. This is an existing Mathlib leaf, so its off-unit use is a generic permitted tool. I also read its cited Mathlib isTriangulated_lift at line 742 and Stacks' exact-functor and subcategory definitions. The statement of def-weil-triangulated-subcategory supplies the inherited triangulations, and the restriction leaf states exactly the final assertion used.

For small cases I checked I empty (initial objects, vacuous equations with still unique mediators), I a singleton (a coproduct vertex is isomorphic to its sole summand), P or Q identically true (ordinary ambient construction), and a property containing no objects. In the last case the empty ambient coproduct, if it exists, forces membership by the assumed closure; otherwise the corresponding existence assertion is conditional and makes no false claim. Different chosen coproducts are covered by the explicit two-arrow uniqueness argument in step 3. No use requires objects or morphisms to be small in the indexing universe; only I and its ULift are used as discrete shapes.

I checked delivery-errors B1-B10: no new nodes or unsearched leaves, self-contained unchanged statement, correct TeX, specific source tags/labels and file lines, blueprint search and attachment checks completed. For C1-C8 all non-elementary input is the cited exact-restriction leaf; the other steps are explicit universal-property calculations, with verbatim supporting quotes in citations.json. The leaf is not dependent on this item, so no cycle arises. For D1-D5 no clause is moved to a new node, no circular intermediate assertion is cited, and omitted categorical details are written out. For E1-E7 the universe bounds, existing-colimit qualifications, repleteness, actual comparison arrow and empty family were all checked as above. Every step is below 800 characters; none hides a long comparison lemma. The correction made during self-review was to include the preservation argument for an arbitrary subcategory colimit cocone rather than just the chosen inherited one.

## Not duplicates

No new nodes.
