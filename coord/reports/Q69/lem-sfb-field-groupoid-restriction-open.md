## Worker report

Item: lem-sfb-field-groupoid-restriction-open. Group: Q69. Stage 1 only, 2026-10-24.

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-field-groupoid-restriction-open.json (statement, split using existing nodes); citations.json (one verbatim statement quotation for each step/node citation); searches.jsonl (generated only by the prescribed search command); report.md.

## New nodes

None: 0 new nodes and 0 new Mathlib leaves. Reused lem-sc-scheme-over-field-universally-open and lem-weil-pbc-surjective-base-change, both already Mathlib leaves. No separate restriction-groupoid node was created, since that would merely restate a clause of the item. The explicit construction and groupoid-law verification are elementary steps in the item itself.

Attachments: none. The searches of lean/WeilConjectures for the blueprint tag and for groupoid/restriction terminology found no declaration giving the item. The few groupoid mentions concern descent or finite locally free relations and do not supply this assertion.

WANTED: none. No unfinished work.

The item's statement and statement dependencies are unchanged. The seed had no proof. Its source combines the restriction construction (Stacks 02VB) and the dotted projection in 04LQ; the latter actually proves more (affineness, flatness, universal openness) than the item asks. No extra hypotheses or conclusions were inserted. The groupoid is absolute, and s and t need not coincide as maps to Spec k. In particular, the proof uses two separate base changes of q, never a presumed single k-algebra structure making the whole groupoid k-linear.

## Sources and searches

Read literature/stacks-project/groupoids.tex, Tag 02VB, lemma-restrict-groupoid (the proof is omitted there); more-groupoids.tex, Tag 04LQ, lemma-restrict-groupoid-on-field, including its complete proof; morphisms.tex, Tag 0383, lemma-scheme-over-field-universally-open, and Tag 01S1, lemma-base-change-surjective, including their proofs. The groupoid axiom expansion is written out by Q69, so proof_origin is conservatively marked agent while naming the Stacks route.

Read the chapter and unit records, SETUP's three levels, GOAL.md, the worker/stage-1 contract and delivery-errors B-E. Also read the current blueprint/latest (main-20261024) sk-thm-sf-ctf-stability/_section.md and its direct-images proof, in particular (3). This is the supporting geometric input in the inherited direct-image chain, not a change to that unit's route. blueprint_refs.py ancestor returns None for this created-item chain. The inherited null blueprint ancestor, long exact place and via chain are preserved; the report explains the connection instead of inventing a mechanical ancestor.

Whole-DAG searches by 04LQ, 02VB, 0383, 01S1 and the restriction/universal-openness/base-change-surjectivity concepts found the existing Mathlib leaves and definition nodes used here. blueprint_refs.py searches for 'groupoid restriction', 'restrict groupoid', 'universally open', and '01S1' gave no matching blueprint node. The 'surjective base change' search returned sbc-lem-bc-integral-surjective, whose base-change cohomology assertion is different. Read the complete statements of every cited node, not their proof text. The source-and-statement search also found def-sfb-restricted-groupoid-relation; that definition uses the opposite endpoint ordering, and supplies no groupoid laws, so the elementary construction here uses the common fibre-product definition directly.

Retained all of the seed's Q40 recorded searches and their results. Ran the prescribed command for Q69 with LeanFinder ('Pullback of an internal groupoid in schemes along a map of objects gives a groupoid with triples as arrows'), Loogle ('"Groupoid", "Scheme"'), grep ('groupoid.*restrict|restrict.*groupoid'), and LeanSearch ('Base change of internal groupoid schemes along arbitrary object morphisms'). The inherited natural-language queries concern the open surjective field restriction; the new queries check the more general categorical restriction construction. Loogle had no hits; grep returned manifold structure groupoids, not internal scheme groupoids. LeanSearch and LeanFinder returned Scheme.GrpObjAsOverPullback and ordinary base-change facts. Read Mathlib/AlgebraicGeometry/Pullbacks.lean:831: the former is group-object base change in Over S, not restriction of an absolute groupoid with distinct endpoint maps. Read Geometry/Manifold/StructureGroupoid.lean:377-384 to distinguish its restriction operation. The full item is not a one-line specialization of these hits.

Also read the reused leaves' Mathlib sources: AlgebraicGeometry/Morphisms/UniversallyOpen.lean:151ff, the arbitrary map to an integral singleton scheme instance (no finite-presentation assumption), and AlgebraicGeometry/PullbackCarrier.lean:436ff, the surjectivity base-change instance. These confirm the stated generality. No Mathlib search result was invented or recorded as unavailable when it succeeded.

## Review by Q69

I checked the statement against 04LQ's diagram: the middle projection from the twice-restricted relation is exactly the dotted arrow, and the two endpoint equations in the statement match the t-first convention in that diagram. Tag 02VB permits any map on objects. For the absolute version all schemes are over Spec Z, so no common k-linearity of s and t is required. The conclusion only asks open and surjective, and 04LQ gives those properties without any finiteness condition.

Step 1 uses precisely def-pc-fibre-product's existence, uniqueness and pairing clauses and def-a1-groupoid-scheme's endpoint identities. I checked each map into the iterated product: identity uses te=se=id, inverse uses ti=s and si=t, and composition first pairs the middle arrows because s(r)=q(v)=t(r'). The composite's outer endpoints then satisfy tc=t(pr0) and sc=s(pr1). This is a direct universal-property construction, not an appeal to the omitted proof of 02VB or to a new clause-sized lemma.

Step 2 uses the statement of def-a1-groupoid-scheme, which explicitly gives all unit, inverse and associative identities and defines a groupoid scheme by its natural test-scheme points. The proof computes both unit products, both inverse products and both associations. Naturality follows because every operation is a scheme morphism built in step 1. No separate Yoneda theorem is silently used: the cited definition itself asks for the pointwise groupoid laws.

Step 3 uses def-pc-fibre-product to write the projection as R_K -> B -> R. I checked that the second map to V is h=s composed with b, rather than t composed with b, and that the two inverse regrouping maps preserve all three projections. def-weil-affine-spectrum explicitly states that a field spectrum has one point; both fields are nonzero, so q is surjective. This is an elementary singleton-set argument, not a flatness or faithful-flatness shortcut.

Step 4 uses lem-sc-scheme-over-field-universally-open's exact statement that X times over Spec k S -> S is open for any k-scheme X and any k-scheme S. I substituted X=Spec K and respectively S=R via t and S=B via h. Swapping the product order uses the universal property already cited, and the inverse scheme maps induce inverse continuous maps. lem-weil-pbc-surjective-base-change explicitly states surjectivity of the base-change projection along an arbitrary scheme map; its f is q on both occasions. The hypothesis q surjective was proved in step 3. Both cited result statements allow the arbitrary base maps in force. They are existing Mathlib leaves, so this cross-unit use is a tool use without any replacement of the unit route.

Step 5 is only composition on underlying sets and opens. Its text gives the two point lifts proving surjectivity and the iterated image formula proving openness. No theorem about flat morphisms being open, no finite-presentation assumption and no unproved base-change invariance of an ordinary open map is hidden here.

I checked B1-B10/C1-C8/D1-D5/E1-E7 against the actual files. There are no new statements to audit for missing definitions or duplicate tags, and no dependency cycle through a new node. Every cited statement has a verbatim quotation in citations.json. All steps are below 2000 characters; no long step conceals a lemma. Elementary steps are explicit constructions, groupoid identities, singleton surjectivity and image composition. Step 4 is marked non-elementary and names both theorem inputs. The changes required on reading were to make the two different maps R -> Spec k explicit and to expand every groupoid law instead of referring only to 02VB, whose proof is omitted.

Small-case checks: K=k reduces to the original groupoid and identity projection; the identity groupoid R=Spec k restricts to the pair relation Spec K times over Spec k Spec K, not generally to an identity groupoid; inseparable and infinitely generated extensions still satisfy both cited leaves; a groupoid with s different from t still has the second base map h=s b. No argument assumes reduced R, nonempty test schemes, finite degree or finite type. For the empty test scheme all formulas and laws hold as well. Thus no statement dispute or source error was found.

## Not duplicates

No new nodes. Existing general results were cited rather than duplicated.
