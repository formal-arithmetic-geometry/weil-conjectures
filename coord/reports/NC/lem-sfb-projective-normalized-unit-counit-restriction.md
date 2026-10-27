# Stage-1 delivery: lem-sfb-projective-normalized-unit-counit-restriction

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-projective-normalized-unit-counit-restriction.json: statement node, now split; not a Mathlib leaf. The statement, statement dependencies, original source note, blueprint ancestry and earlier NI searches are retained. Eight proof steps use existing nodes only.
- citations.json: 28 verbatim statement excerpts, one for each step/node citation.
- searches.jsonl: six searches actually run by NC through msearch.py, with original returned records.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No unit record needs modification: this item is a helper, not the unit's key statement.

## Attachments

None. Read-only searches in lean/WeilConjectures for the exact blueprint tag, normalized/projective terminology, and unitComponent/counitComponent/unitCounit terminology produced no declaration stating the complete item. The partial and sorried project declarations are not attachments.

## WANTED

None. All sources used are present.

## What was wrong or needed completion

The live item was unsplit; its source.note preserved the earlier seven-step argument, which I read and retained verbatim. No archived attempt exists at the assignment's abandoned-item glob, and the active sandbox initially contained no node, proof or report. There is no item-specific repair note. I copied the current item and reused its mathematical route, rather than treating the preserved proof as a finished split.

I replaced the old appeal to a ringed sheaf-module localization theorem by lem-sfb-noncommutative-ringed-open-closed, whose statement directly concerns the internal module objects in this item, includes the actual adjunction counit, and allows transport through the specified pulled-back coefficient-ring isomorphisms. This avoids an unstated equivalence of coefficient categories. The old proof's separate choice of a support isomorphism is unnecessary: I compute the transpose of the actual fixed projection-defined diagonal tensor morphism and show that its restrictions are invertible.

The latest blueprint's short proof cites Tag 09AD for joint conservativity. I read proetale.tex, especially lemma-closed-immersion (09AA), lemma-closed-immersion-complement-retrocompact-exact (09BM), and lemma-ses-associated-to-open (09AH). The proof here spells out the unbounded cohomology/cone argument from the internal-module localization sequence; it makes no geometric-stalk conservativity assumption. I also read the ringed-topos tensor/pullback and composition statements in sites-cohomology.tex (07A4, 0D6D, 0D6E), but the item uses the existing normalized internal-module interfaces, not an unspecified comparison with ordinary ringed sheaves.

No statement change, STATEMENT-DISPUTED claim, route replacement, new axiom, or triangle identity is involved. The conclusion says natural transformations between the given exact functors. Their exact endpoints are hypotheses; this proof does not assert that arbitrary normalized maps form an adjunction.

## Mathlib evidence and provenance

The four original NI search entries dated 2026-10-27 in the live node remain unchanged and explicitly retain their original result records. They are inherited evidence, not searches run by NC. NC separately ran and appended these six queries (all services answered):

1. leanfinder: The canonical diagonal tensor map is invertible and diagonal insertion and trace contraction define unique natural transformations on full derived subcategories under invertible exchange and projection comparisons
2. loogle: CategoryTheory.NatTrans.ext
3. leansearch: A unit and counit defined by diagonal class and trace restrict naturally to full subcategories when exchange and projection are isomorphisms
4. grep: diagonal.*tensor|UnitCounitNormalized|unitCounit_existsUnique|trace.*contraction
5. leanfinder: Closed immersion projection formula: the canonical morphism from a complex tensor the pushforward of the coefficient unit to pushforward of its restriction is an isomorphism; restrict natural transformations to full subcategories
6. grep: projectionFormula|projection_formula|closedImmersion.*tensor|tensor.*closedImmersion

I read the results. The exact-derived single-functor isomorphisms do not assert this geometric construction. NatTrans.ext handles only its elementary uniqueness ending. Adjunction.restrictFullyFaithful and its unit/counit equations require an ambient adjunction already, whereas this item deliberately proves no triangle identities. I read Mathlib/CategoryTheory/Adjunction/Restrict.lean and CategoryTheory/NatTrans.lean to check those meanings. The second semantic search returns Zariski structure-sheaf restriction adjunctions for open immersions and Proj charts, which are not the pro-etale internal-module diagonal statement. The first grep returns representation-theoretic diagonal tensors, linear traces and an external functor product; the second grep has no hits. Thus the whole item is not an exact match or one-line Mathlib specialization. The two different semantic phrasings and grep patterns also check the smaller diagonal-isomorphism portion.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to justify. I searched the whole DAG for internal module equivalences, open--closed conservativity, diagonal tensors and closed-immersion projection formulas, and the whole imported blueprint using blueprint_refs.py for diagonal tensor, open closed, section tensor, closed immersion, unit counit, diagonal tensor morphism, normalized unit and diagonal insertion. The relevant existing internal localization and projection nodes are cited. None of the blueprint search results states this whole conditional normalized construction in another form; same_as remains empty. The existing ancestor det-prop-p1-adjunction-rational-unit-counit is the rational localizing application of this conditional helper, not a duplicate. All cited nodes were checked for a path back to this item; none has one.

## What remains unfinished

Nothing in the authorized one-level stage-1 split. Existing downstream nodes retain their own proof obligations. No Lean was written and no compiler, Lake or build tool was run.

## Review by NC

I read the chapter and unit records and the current blueprint file at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-unit-counit.proof.md. This item realizes the well-definedness paragraph of the unit's first step, retaining diagonal insertion, inverse self-base-change, inverse twisted projection, and trace contraction. The second unit step (triangle identities) remains outside this item. I read the complete statements of all sixteen cited nodes and produced a verbatim excerpt for each of their 28 uses in citations.json.

Step 1 uses lem-sfb-noncommutative-ringed-open-closed for internal-module exactness, the invertible actual closed counit, vanishing of open restriction of closed pushforward, and the localization sequence. Its final coefficient-isomorphism clause is what licenses the actual pulled-back coefficients, and its hypotheses are exactly closed immersion plus quasi-compact complementary open, with no global qcqs assumption. The exact-derived Mathlib leaf lem-sf-exact-functor-derived-triangulated and the exact-functor clause of sk-def-sfb-derived-categories give the termwise unbounded interpretation. I wrote out the H^n and cone argument, so joint conservativity is not a hidden theorem or a new node.

Step 2 uses the actual map defined in def-sfb-internal-diagonal-tensor-comparison, the derived adjunction stated in sk-def-sfb-module-derived-pushpull, the invertible internal tensor-pullback comparison and counit-mate projection definition stated in def-sfb-proetale-projection-exchange-maps, and the fixed section comparison of def-sfb-projective-diagonal-pullback. I checked its transpose is exactly mu followed by s tensor the coefficient counit and then the unitor. The identity psi=epsilon composed with i^*d then proves invertibility on the diagonal; step 1 supplies invertibility of both relevant counits. This checks the published map's normalization, not merely existence of some support isomorphism.

Step 3 again uses the internal tensor-pullback comparison, now at j, and the vanishing from step 1 to show both restrictions to the complement vanish. The closed tensor structure stated in sk-def-sfb-derived-tensor-hom makes tensoring zero zero. The statement of lem-sfb-rational-p1-left-projection-naturality applies with g=Delta, k=p_1^*u and N the coefficient unit, without an invertibility hypothesis. With the fixed natural section and unitor, it proves naturality of d, and step 1 proves d is invertible. Both inverse naturality and the cone reduction are elementary algebra from the stated facts, not additional claims hidden as nodes.

Step 4 uses precisely the natural isomorphism Id ≅ Rp_2* RDelta* already fixed in def-sfb-projective-diagonal-composition and the supported coefficient source stated in def-sfb-diagonal-coefficient-category. I checked the direction: its inverse gives the displayed conclusion Rp_2* RDelta* ≅ Id, while the forward direction starts eta. No unproved projection formula is used here.

Steps 5 and 6 use the coefficient diagram's specified delta, the exact two inversions in def-sfb-rational-p1-unit-inversion-condition, the fixed e-dependent Pi in def-sfb-tate-twisted-projection-comparison, and the complete unit formula in def-sfb-projective-ambient-unit-counit-composites. All arrow sources and targets agree: Pi is inverted before T_P(b) is inverted. For naturality I use the precise tensor-shift equation from lem-sfb-rational-p1-tensor-shift-naturality and the left-projection equation from lem-sfb-rational-p1-left-projection-naturality; the latter applies also to the right-projection version by the canonical braiding in the projection-map definition. Exchange is a mate natural transformation by that same definition. I wrote out how multiplying a naturality square by component inverses gives the inverse square. These give the displayed GF(u) eta = eta u equation without any proper-base-change or projection-formula theorem being silently assumed: those invertibilities are hypotheses of this item.

Step 7 uses the exact fixed projection inversion in def-sfb-rational-p1-counit-inversion-condition, the fixed ambient counit formula and coefficient-unit identification, and the diagram's trace. The two cited naturality lemmas apply with g=q, N=L_P[2] and morphism v, and with tensor-shift at q^*v. The two equations for t and lambda, followed by bifunctoriality of tensoring tau and unitor naturality, give v epsilon = epsilon FG(v). I checked the shift direction: t goes from Rq_*(q^*K tensor L_P[2]) to FGK, and the construction uses t inverse first.

Step 8 uses only the fixed component normalization stated in def-sfb-projective-ambient-unit-counit-composites. Preservation puts the endpoints in the respective full subcategories; fullness puts each ambient component there and faithfulness checks the equations. Componentwise heterogeneous equality to the same fixed formula becomes equality after the prescribed type identifications, and natural-transformation extensionality proves uniqueness. Exactness of F and G is an explicit hypothesis, so their composites are the specified exact functors. No triangle identity is smuggled into this last step.

I checked the small cases M=0, K=0, the zero coefficient ring, empty Y, and the zero full triangulated subcategories: tensoring and restriction give zero maps and the component uniqueness remains correct. Unbounded M is allowed because the support argument checks every H^n individually, and the tensor-pullback comparison is the unbounded one. The modules L_Z need not be invertible; only the given e, preservation and inversion hypotheses are used. The proof uses no claim about detecting arbitrary pro-etale sheaves by geometric stalks.

Against delivery-errors B--E: there are no new-node self-containment or duplicate issues; all used facts are existing statement-level assertions or explicitly written elementary calculations; no step cites a proof instead of its statement; dependency traversal gives no cycle; the off-unit internal localization result is declared as a generic tool in split_report.tool_uses. This is not a relabelling of clauses as new nodes: the eight steps carry the actual support, transpose, naturality and uniqueness arguments. All steps are below 2000 characters (the longest is 1173), so no long step hides a separate lemma. The original statement and source.note are retained, and no hollow data or source-route change was introduced.

The dry run asked for a longer excerpt for step 3's closed tensor structure. I expanded that citation to the full internal-hom/adjunction paragraph, which explicitly supplies the tensor left adjoint used to preserve zero. No proof or statement change was required.
