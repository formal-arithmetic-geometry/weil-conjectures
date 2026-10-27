# Stage-1 delivery: lem-dl-a1-profinite-restriction-full-faithful

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-profinite-restriction-full-faithful.json: item, statement, split in five steps; no Mathlib match for the equivalence.
- dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-compact-hausdorff-closed-map.json: statement, Mathlib leaf Continuous.isClosedMap (Hausdorff.lean:673-674).
- dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-open-subgroup-finite-cosets.json: statement, Mathlib leaf, finiteness/discreteness/continuous left action clause by clause (OpenSubgroup.lean:287-290; Group/Quotient.lean:115-117,68-72).
- citations.json: verbatim statement excerpts for all five citations.
- searches.jsonl: actual msearch outputs; the node records preserve the exact tool/query and output summary.

## Attachments

None. Searched WeilConjectures for the exact item tag and for profinite/continuous-action/restriction/fullness terminology. Project occurrences of coset finiteness are uses or special cases, not the item. Neither a project declaration nor a Mathlib theorem proves the full equivalence. Action.full_res supplies only the elementary forward direction for algebraic actions.

## WANTED

None.

## Corrections and source issue

The item's statement and its statement dependency are retained. The finite-set comparison sentence of def-pod-finite-continuous-module really defines the action category being used; no passage from sets to modules is made. The old item was statement-only.

In Stacks Tag 0BN6, pione.tex, lemma-functoriality-galois-surjective, the final paragraph announces (4) implies (1), constructs G/U, and then says it contradicts (3) and concludes (3) implies (1). The construction in fact contradicts (4): an H-fixed coset supplies a map from the terminal singleton, whereas no G-fixed coset exists for a proper subgroup. Our proof uses fullness directly to lift that very map, so it repairs this numbering/inference slip without changing the theorem. We also supply the open-subgroup argument which the source abbreviates. No SGA source is used.

## Not duplicates

lem-dl-a1-compact-hausdorff-closed-map vs lem-sfb-compact-hausdorff-surjection-quotient: the existing node states that a continuous SURJECTION is a quotient map. It does not state closedness of arbitrary continuous images. The new Mathlib leaf states closed images of closed subsets with no surjectivity hypothesis, applied here to a non-surjective h.

lem-dl-a1-open-subgroup-finite-cosets vs lem-dl-a1-profinite-restriction-full-faithful: the leaf supplies only the finite discrete continuous coset test object for an arbitrary compact group and an arbitrary open subgroup; it states no restriction functor or surjectivity criterion. The item's argument proves the equivalence using that test object.

lem-dl-a1-open-subgroup-finite-cosets vs lem-dl-a1-field-point-full-faithful-galois-map: the existing node concerns the comparison of a field-point fundamental group with an absolute Galois group. The new leaf has no scheme, field or fundamental group and only supplies a general coset action.

lem-dl-a1-open-subgroup-finite-cosets vs lem-exc-etale-open-subgroup-quotient-finite-discrete: the existing node requires G to be an absolute Galois group Gal(K^sep/K), and states only finite/discrete quotient topology. The new leaf applies to every compact topological group and includes joint continuity of the left action. The item's arbitrary profinite groups are not assumed realizable as absolute Galois groups, so the existing statement cannot be applied. Both are direct specializations of the Mathlib declarations; no second unsplit proof is created.

DAG searches included source tags 08YD and 0BN6, Continuous.isClosedMap and quotient_finite_of_isOpen, and statement/title searches for closed images, compact Hausdorff maps, profinite subgroups and cosets. Blueprint searches included profinite, open subgroup, closed subgroup, coset, coset quotient, quotient finite, compact image, compact Hausdorff, closed map, finite discrete, restriction, fully faithful and both tags. No blueprint node states either new leaf. The exact ancestor is rem-dl-a1-conventions, with the inherited intervening chain retained. The newest blueprint's actual conventions file is under sk-lem-wft-curve-heart; its unramifiedness paragraph is the place recorded, although the existing DAG unit stamp remains sk-d-dl-a1-setup.

## Unfinished work

None in this one-level split. Both new nodes are exact Mathlib leaves, carry no proof or proof dependencies, and introduce their own spaces/group/subgroup and hypotheses. No Lean was written or compiled. Only this sandbox was written.

## Review by Q100

I read Stacks pione.tex, lemma-functoriality-galois-surjective (0BN6), in full, especially the forward implication and final coset paragraph. I read topology.tex, lemma-closed-map (08YD), whose proof explicitly shows that closed subsets have closed images. I read the local Mathlib source at Hausdorff.lean:673-674, OpenSubgroup.lean:283-295, and Group/Quotient.lean:68-78,115-117. The latter source treats arbitrary subgroups: normality is not a hidden hypothesis. I also read Action/Basic.lean:400-419, Action/Continuous.lean:96-110 and Galois/Equivalence.lean:35-54 to reject partial or canonical-functor matches for the whole item. The three-level route is unchanged; the chapter/unit records and latest blueprint conventions supply the original field-point/inertia route, and the new nodes are general Mathlib tools below it.

Step 1 uses precisely the equivariant-map and terminal/finite-set conventions in def-pod-finite-continuous-module. Choosing a preimage of each g proves equivariance by the displayed equality; injectivity of Hom restriction follows from identity on functions. There is no extra linearity condition, and the formula also holds for empty E or D whenever a map exists.

Step 2 cites the closed-map leaf, whose statement explicitly gives f(X) closed. Its compact-source, Hausdorff-target and continuity hypotheses are exactly among the item's assumptions. K is a subgroup because h is a homomorphism. Non-surjectivity supplies g outside K. This step does not cite the quotient-map node for a fact absent from its statement.

Step 3 cites no external lemma: it uses the open-normal neighbourhood basis explicitly assumed in the item. Translation by g and its inverse are continuous by continuous multiplication. The displayed open identity neighbourhood therefore contains an open normal N. The multiplication/inversion calculations prove KN is a subgroup, the union of kN proves openness, and g = kn would put gn^{-1} in the forbidden intersection. This is an explicit elementary argument from group axioms and the stated basis, not an unproved closed-subgroup separation theorem. I checked the order of factors in both products; N, not K or U, is required normal.

Step 4 cites the coset leaf for each of finiteness, discrete quotient topology and joint continuity, and def-pod-finite-continuous-module for the finite-action category and terminal singleton. The leaf's compact-group and open-subgroup hypotheses have been established. The coset U is fixed by h(H) because K is contained in U. Thus b is an actual H-equivariant map in the relevant Hom set, rather than an H-fixed point asserted without a morphism construction.

Step 5 uses the full-faithfulness hypothesis of the item and the map constructed in step 4. Fullness supplies a map whose UNDERLYING function is b, so it really sends the singleton to U. The equivariance equality forces every xU = U and hence every x in U, contradicting g outside U. No transitivity, preservation of connected objects or categorical Galois equivalence is needed. Every cited statement was opened and its exact used sentence copied into citations.json.

I tested the item on identity and trivial homomorphisms, G trivial, H trivial and G nontrivial, the finite inclusion 1 into C2, and empty finite actions. The inclusion fails fullness because the singleton can map to either point of C2 as an H-set, while neither is G-fixed. For the coset leaf I checked U = G (singleton), U = 1 in a finite discrete group, and a nonnormal subgroup C2 of S3 (three cosets); the action is on left cosets and needs no quotient-group structure. For the closed-map leaf empty X and closed A = empty or X are allowed. The proof would require extra work without compact H, since a dense proper image can act with the same equivariant maps; the closed-image citation is exactly what rules this out.

Against delivery-errors B--E: the two new nodes contain statements only; all objects and hypotheses are introduced, their matches have the actual lines read, and searches are actual logged msearch runs. Existing absolute-Galois and quotient-map special cases were read rather than used outside their statements. Every non-elementary input is a cited leaf; all other arguments are displayed from definitions or hypotheses. The leaves do not restate a clause of the equivalence, there is no back-edge to the item, and no construction depends on a future proof step. Each proof step is under 700 characters, so none hides a lemma inside a long step. The numbering slip in the Stacks proof is corrected as explained above; the item's mathematical statement is unchanged.

The first dry run requested explicit definition-node citations inside the new leaf statements. I added def-kun-subspace-topology for the induced topology on the closed subset A, after reading its full statement, and def-pod-finite-continuous-module for interpreting the finite discrete continuous coset action as an object. Their statement dependencies and the verbatim citation quotes were updated together. These convention references add no hypotheses and do not use a definition as a theorem.
