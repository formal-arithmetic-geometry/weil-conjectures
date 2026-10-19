# Q39 stage-1 split: lem-coef-scat-diagram-factorization-uniform-bound

## Files written

- `dag/nodes/sec-six-functors/lem-coef-scat-diagram-factorization-uniform-bound.json`: statement, split; eleven proof steps. Statement, source, blueprint ancestry, import/audit fields and inherited Mathlib searches retained. Added the proof, exact proof dependencies, proof origin, split report, and the searches actually made in this sandbox.
- `dag/nodes/sec-six-functors/lem-coef-scat-injective-universe-generators.json`: statement, unsplit; no Mathlib match. One new node, no new Mathlib leaves. It asserts common generating sets under universe enlargement, not the existence, accessibility or naturality of factorizations.
- `citations.json`: one verbatim statement excerpt per step/node citation, including the full generation assertion for the new node. The quotations were checked against the current source node statements.
- `searches.jsonl`: actual msearch output records, retained unchanged. The preparation scripts are scratch files in this sandbox, not DAG deliveries.

## Attachments

None. I searched `WeilConjectures/` in the read-only slopmaster2 source for the exact blueprint id and for Bergner, Dwyer--Kan, injective factorizations and injective diagram generators. There is no project declaration stating either the item or the new lemma. I also searched the read-only master reference for the item and notions; it supplied no attachment. Neither an upstream sorry nor a Mathlib small-object construction was treated as a completed project proof.

## WANTED

WANTED: Jacob Lurie, *Higher Topos Theory*, archival copy of https://people.math.harvard.edu/~lurie/papers/HTT.pdf, Proposition A.1.2.5 and proof (printed pp.790-791), Proposition A.2.8.2 and Lemma A.2.8.3 (pp.830-831), Lemma A.3.3.3 with its compatible-slice proof A.3.3.15--17 (pp.878-884), and Corollary A.3.6.18 proof (p.905), for the item and lem-coef-scat-injective-universe-generators. I read these places online; no local copy was present in the named literature directory and I did not download or modify the literature. Accordingly proof_origin.by is agent. No Stacks tag states this enriched-model-theoretic result; I did not substitute an unrelated Stacks citation. No SGA source is used.

## What needed repair

The item was statement-only, not previously split in this sandbox. Its inherited searches were retained. Its statement is true as written, including both factorization systems, arbitrary small D, both larger-universe and same-universe cases, and all small filtered indexing categories in the respective larger universe. No statement correction or STATEMENT-DISPUTED is needed.

The tempting fixed-universe shortcut is insufficient: lem-coef-accessible-small-object-factorization supplies some accessible factorization in a fixed universe, and lem-coef-enriched-diagram-size-generation supplies some diagram generators there. Neither statement selects one generating family that continues to generate in all larger universes. My new lemma isolates precisely that missing generation input. The item then constructs the actual factorization from those generators, rather than concluding by applying a new factorization theorem.

During self-review I found that the localization-comparison node's proof identifies the I/J classes, but its statement does not. I removed that proof citation. Step 1 now writes the recognition argument using the actual interval-lifting, cell-stability and Kan-model statements and the existing lifting-closure leaves. This repairs C4 instead of relying on another node's proof. The localization-comparison node remains an unchanged statement dependency because the item uses its Dwyer--Kan terminology.

## What remains

The new generation lemma is intentionally statement-only and joins the next stage-1 queue. Its proof is not concealed in its statement. All eleven steps of this item's proof are written. Nothing is delivered or pushed by this worker; the second reader receives the accepted sandbox.

## Not duplicates

lem-coef-scat-injective-universe-generators vs lem-coef-enriched-diagram-size-generation: the existing theorem concerns a fixed presentable category in a fixed universe and asserts some small generating set there. The new statement requires the identical U-small sets of Bergner-diagram arrows to generate the objectwise classes in every containing universe, including classes of diagrams not U-small. It neither repeats the existing fixed-universe conclusion nor assumes that existence separately in each universe is uniform.

lem-coef-scat-injective-universe-generators vs lem-coef-combinatorial-injective-diagram-model: the latter constructs injective model structures for a combinatorial category in a chosen universe; it does not name common generators for all universe enlargements. The new lemma contains no model-factorization or homotopy-limit conclusion.

lem-coef-scat-injective-universe-generators vs lem-coef-accessible-small-object-factorization: the latter starts with an already given generating set and proves an accessible factorization in a fixed universe. The new lemma constructs a common generating set for the objectwise diagram left classes and says nothing about factorization functors.

lem-coef-scat-injective-universe-generators vs lem-coef-scat-diagram-factorization-uniform-bound: this is an input about weak saturation of sets, without any middle-object functor, preservation property or comparison of choices. The eleven steps prove the item's factorization, filtered-colimit and natural comparison assertions from it. It is not any clause of the item's conclusion.

lem-coef-scat-injective-universe-generators vs lem-coef-finite-pattern-universe-comparison: that node concerns marked simplicial sets over a fixed categorical pattern with finite cone shapes. The new lemma concerns ordinary diagrams of simplicial categories and their objectwise I/J-cofibrations. The objects and left classes are different.

Whole-DAG keyword/source searches included Bergner, injective/generating, weak saturation, small object, uniform generators, and HTT A.3.3.3/A.2.8.3. Whole-blueprint searches were run using blueprint_refs.py for uniform accessible injective factorizations simplicial categories, injective, small object, Bergner, weakly saturated, diagram-size, and factorization. No blueprint node states the new common-universe generator assertion or the item. Both same_as fields are therefore empty. The new from.node is the ancestor command's prop-coef-integral-exceptional-adjoint, with the item prepended to its inherited via list. The unit and chapter bindings are unchanged.

## Mathlib search review

All new recorded queries were executed through msearch.py with Q39 and this item id. I read every returned signature and the recorded hits. The two generator phrasings find generic cofibration closure, presentability of already supplied objects, and orthogonal reflection (Hom bijectivity). These do not generate the objectwise weakly saturated class of diagram maps. I read the candidate OrthogonalReflection.lean:75-105: its orthogonality condition is uniqueness-and-existence of extensions, not the injective lifting class in question. The replacement phrasing returns SmallObject.functorialFactorizationData; I read IsCardinalForSmallObjectArgument.lean:460-473, whose premise already supplies the small-object cardinal. It supplies neither common injective generators nor the required preservation/universe comparison. SimplicialSet cofibrations_eq and the ordinary model WFS instances are about a different category or only generic model axioms. Loogle returned no hits. The broad grep's function-injectivity and module hits are unrelated; the focused category-theory Bergner/injective-model grep returned none. No unavailable service was recorded as a negative search. No new Mathlib leaf is claimed.

## Review by Q39

I read the chapter and unit records, the current main-20261015 integral-exceptional-adjoint ancestry, the item's source places online in HTT, and every cited DAG statement. This split serves the existing bounded-replacement infrastructure below paragraph 2 of the integral adjoint proof. It changes no unit/chapter route or realization record. The item is not the unit's key statement.

For the new node I read HTT A.3.3.3's statement and its full compatible-slice proof, including the cardinal requirements (i)-(v), the countable enlargement of slices in A.3.3.15, the simultaneous relative slices of A.3.3.16, and the final small pushout in A.3.3.17. Its use here is a common-universe refinement for the fixed countable finite-limit theory of simplicial categories and fixed U-small D and I/J data. For this application the enrichment in A.3.3.3 can be ordinary Set-enrichment, with copowers and products as tensor and cotensor; no simplicial model axiom for the Bergner category is assumed. The fixed ordinal models of bounded compact diagrams and their arrows are U-small, so can be used as representatives in every containing universe; the slice proof uses the same bound, whereas the lengths of the resulting cell sequences may grow. This is stronger than merely applying the fixed-universe theorem twice. HTT A.3.6.18 explicitly notes the universe-independent bound for the application. I have not claimed that its short sentence alone is a proof of the new node; the new node is the non-elementary generation obligation to split next.

Step 1 uses the actual interval statement for the generating families, small-object factorizations, retract description and J-lifting test; the cell-stability statement for W's closure and J-cell equivalences; and the Kan statement for the boundary-lifting characterization of trivial fibrations. The two lifting-closure leaves justify the closure operations on the left classes. I checked the object-surjectivity argument uses invertible-vertex lifting in the correct direction, and that local trivial fibrations lift vertices even without fibrant source or target. The retract after factoring a weak equivalence uses two-out-of-three, not a claim that arbitrary I-cell maps are equivalences.

Step 2 uses the new node exactly for common weakly saturated generators and the injective-model statement exactly for the two objectwise left classes and their model right classes. The ground WFS were identified in Step 1, not read from a proof of the localization node. This also checks combinatoriality in the application of the injective-model theorem: local presentability is given by the interval statement and I/J are small generators.

Step 3 uses the regular-bound leaf on a genuinely U-small disjoint union, including countably many simplex degrees and all arrows of D. Strict inequality above N ensures the chosen regular bound is uncountable. It bounds both the number of relevant values and equations for every generating endpoint.

Step 4 uses finite-limit-model-presentability only for pointwise filtered colimits of models, after explicitly describing the sketch. The injective-model theorem gives the pointwise ordinary diagram colimits. The elementwise-colimit leaf gives representatives and eventual equality. The smallness needed for assembling these witnesses is less than delta, supplied in Step 3; the index category itself can be V-small. I checked both surjectivity and injectivity of the Hom comparison, so non-monic transition maps are covered.

Step 5 uses diagram cocompleteness and the colimit definition for the displayed pushout. The square-set indexing is small in V because S is U-small and all relevant Hom sets are V-small. Its action on a square is written on every summand; the universal property verifies composition, not an unsupported naturality assertion.

Step 6 cites transfinite recursion and the colimit definition. The ordinal delta belongs already to U, so all its stages exist in every V. The slice colimit is justified by the underlying colimit cocone. This writes the factorization algorithm itself; the new node provides no factorization.

Step 7 uses the pushout-closure and transfinite-left-lifting leaves, whose statements apply to arbitrary small ordinals and do not require that the right class be small. For right lifting I checked that the top map factors at a stage alpha less than delta, and that its equation to the fixed target already holds there: no unsupported equality detection in a varying target is needed. The stage alpha+1 then supplies the requested summand and filler.

Step 8 uses the same closure leaves to pass from lifting against S to lifting against its weak saturation, and the injective-model statement to name the resulting right classes. In particular, it does not silently equate projective and injective cofibrations.

Step 9 uses filtered-colimit/finite-limit commutation only for the displayed fibre product of three Hom sets, not for an infinite set of squares simultaneously. Copowers preserve set colimits by their universal property; coproducts over S and pushouts then commute with colimits by the Fubini leaf, whose statement allows the relevant small fixed indices. Step 10 applies that same Fubini statement to the fixed ordinal sequence; the induction uses both input-source and input-target preservation. These prove preservation for every V-small delta-filtered ordinary index, not just posets or unions of subobjects.

Step 11 checks universe inclusion by the explicit degreewise category presentation using finite strings and relations. This is a routine universal-cocone verification, not a claim that arbitrary simplicial-category colimits are computed on underlying arrow sets. The interval node supplies existence of colimits; the injective-model statement supplies pointwise computation in the diagram category. Inclusion has exactly the same Hom sets on smaller objects; therefore the square sets used by the fixed algorithm do not change. The successor and limit comparison isomorphisms commute with both factor maps and input squares by their universal properties. Thus the conclusion is natural in arrows, and the same fixed delta works.

I tested D empty (terminal diagram category and unique factorization), D terminal (ordinary Bergner WFS), same-universe inclusion, empty diagram endpoints, and filtered diagrams with identifications rather than only injections. Both generating families may be empty in the empty-D case; the square-attachment algorithm then reduces to identities. A filtered index is nonempty under the stated definition; ordinal delta has no final stage below delta but is delta-filtered by regularity. No finiteness of D or fibrancy of its diagram values is imposed. The bounded-generation node covers arbitrary D-smallness, not finite D.

For delivery-errors B--E: the new node is self-contained, statement-only, has no proof/proof-dependencies, preserves TeX escaping and names its actual source; it carries blueprint and Lean audit data. Its searches are actual logged queries with candidate review. There is no new elementary node, duplicate, or factorization-clause restatement. I read and checked the statements used by each step, corrected the C4 issue above, and checked the smallness and universe hypotheses where applied. The proof uses existing closure and recursion facts instead of silently using them. All steps are under 2000 characters, including the explicit ground-class recognition and universe comparison; none hides a comparison behind the word 'transport'. The only non-elementary generation subclaim is explicitly the new node.

## Validation

The required server review and dry-run commands are run from this sandbox through the launcher tools. No local check_dag.py, review_split.py or preflight_delivery.py, no compiler, no Lake, no direct git command, and no write to the shared project or live launcher were used. Final command results are recorded below after completion.

The server `review_split` command printed PASS. The required `deliver.py Q39 lem-coef-scat-diagram-factorization-uniform-bound --no-push` printed `OK (not pushed) ... at 2d497df1f0: preflight passed`. The exact final sandbox, including this validation record and the last self-review wording fixes, is submitted to one final no-push dry run before handoff. The independent citation-coverage audit also checked every quoted substring and found no proof-dependency path back to this item. No new statement or proof step exceeds 2000 characters.

## Second reading by Q39

- Item statement: checked against HTT Proposition A.1.2.5(2), Proposition A.2.8.2, Lemma A.2.8.3, Lemma A.3.3.3 and the proof of Corollary A.3.6.18, hypothesis by hypothesis; the two WFS, arbitrary U-small D, containing/equal universes, regular bound, filtered-colimit preservation, functoriality and universe comparison are all present and no edge case is excluded. Verdict: PASS after the source wording repair below.
- Step 1: checked against the definitions and lifting tests in `lem-coef-simplicial-interval-lifting`, the J-cell equivalence statement, Kan trivial-fibration criterion, and both lifting-closure statements. Verdict: repaired: the I-injective characterization is now written out from the generators, and both directions of `I-inj = W ∩ J-inj` are explicit.
- Step 2: checked against the new common-generator statement and `lem-coef-combinatorial-injective-diagram-model`; the objectwise left classes and their right orthogonals are the injective WFS classes. Verdict: PASS.
- Step 3: checked the endpoint-data disjoint union, the U-small indexing by D, simplex degrees and object pairs, and `lem-coef-small-family-regular-bound`. Verdict: PASS.
- Step 4: checked the finite-limit sketch, pointwise filtered colimits, elementwise representatives/equality witnesses, and the fewer-than-delta witness count. Verdict: PASS; the argument covers non-monic transitions and does not depend on the size of the filtered index category.
- Step 5: checked the displayed square set, both pushout attaching maps, the induced map to the fixed target, and functoriality by the colimit universal property. Verdict: PASS.
- Step 6: checked successor and limit stages, slice colimits, transfinite recursion, and the identity/composition induction. Verdict: PASS.
- Step 7: checked coproduct, pushout and ordinal closure of the left class and the stage at which a generating square is attached; regularity gives the required delta-filtered ordinal. Verdict: PASS.
- Step 8: checked closure of a fixed right lifting class under the full weak saturation and the identification of both injective right classes. Verdict: PASS.
- Step 9: checked the finite-limit formula for `Q_s`, copower/coproduct/pushout colimit interchange, and the cited Fubini and filtered-finite-limit statements. Verdict: PASS.
- Step 10: checked the base, successor and limit induction for the intermediate functors and the use of one common delta. Verdict: PASS.
- Step 11: checked the explicit finite-string presentation of colimits in sCat, full faithfulness of universe inclusion, pointwise ordinary functor-category colimits, and induction over the same ordinal. Verdict: repaired wording to state pointwise colimits directly; the comparison is natural and also covers equal universes, empty D and terminal D.
- New node `lem-coef-scat-injective-universe-generators`: checked self-contained definitions of sCat, D, I/J, lifting classes, weak saturation, colimits and universe sizes; checked every notion against its statement dependencies and the six recorded Mathlib searches. Verdict: PASS as a statement-only non-elementary input; it is strictly smaller than the item and has no proof fields.

Changes made:

- Rewrote item Step 1 to supply the previously implicit I-lifting argument and clarify the two directions of the WFS recognition, repairing the C3/C4 risk.
- Reworded item Step 11 so its pointwise functor-category claim is stated as the elementary ordinary-colimit fact rather than attributed to a node that does not state it.
- Corrected the item and new-node source descriptions: HTT A.3.3.3 supplies the bounded compatible-slice construction, while A.3.6.18 supplies invariance of the regular cardinal; the identical U-small generator sets are the explicit representative-set refinement used here, not a verbatim claim of the corollary.
- Updated `proof_origin` to record the U-small representative transport underlying the common-universe refinement.

I did not find a false statement, missing hypothesis, duplicate node, Lean attachment, or source theorem whose hypotheses fail on the tested cases (D empty, D terminal, equal universes, empty endpoints, zero/identity arrows, and filtered diagrams with identifications). No `STATEMENT-DISPUTED` marker is required.
