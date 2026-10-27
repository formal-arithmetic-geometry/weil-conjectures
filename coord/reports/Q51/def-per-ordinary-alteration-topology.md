# Worker report: def-per-ordinary-alteration-topology

## Files written

- dag/nodes/sec-deligne-laumon-a1/def-per-ordinary-alteration-topology.json: definition, now split; no exact Mathlib match. Statement and fourteen statement dependencies retained verbatim; proof and proof_deps remain empty.
- citations.json: empty list, because this definition has no proof steps or proof-step citations.
- searches.jsonl: five actual msearch.py searches, with their returned hits. The item's older search records are retained as inherited evidence; they are not represented as searches performed by Q51.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag and by alteration, uniformization, ordinaryAlteration and markedRegularCover found no declaration for this definition. lean/Sheaf/AlgebraicGeometry/PrimeToEllAlterationTopology.lean is a different definition, with a prime parameter; it does not supply the ordinary topology plus U(S,Z).

## Literature

No WANTED documents. Read the local ILO PDF through sandbox ilo.txt: Expose II 1.1.1-1.1.2, 1.1.7-1.1.10 and 1.2.2 (printed pp.23-24), 2.1.1 (p.26), 2.3.1-2.3.3 (p.28), and VII Theorem 1.1 (p.81). There is no relevant Stacks tag defining this alteration topology; the exact ILO numbered definitions are the source. No prohibited SGA source is used.

## Corrections and findings

No statement correction or statement dispute. The item is a definition, not the weak uniformization theorem. U(S,Z) is a proposition specifying witnesses; it does not assert their existence for every Noetherian S. Consequently neither quasi-excellence nor a proof of regular connected sources being integral is needed to state it. That theorem's conversion from connected regular sources to integral sources belongs to the caller, not to the construction of this predicate.

Read the newest blueprint main-20261024 (COMMITS.txt: ef6f9619fdbffa59e88528fb56483d76c70258c8), the current chapter and unit, and the ancestor statement and proof. The ancestor's Step 3 is the duality branch; the alteration definition occurs only in the existing auxiliary weak-uniformization branch, not as an explicit sentence of that blueprint. The inherited provenance chain is retained and this limitation is recorded in split_report.blueprint. This definition changes neither chapter nor unit route and is not the unit's key node.

## Unfinished work

None in this definition. Existing dependency nodes remain the established DAG nodes; their later work is not part of this item.

## Not duplicates

No new node was created. Whole-blueprint searches for alteration, alteration topology, uniformization and normal crossings returned no exact blueprint notion. Whole-DAG searches found the ordinary topology here and its users lem-per-qe-weak-uniformization-cover and lem-per-ordinary-alteration-proper-refinement. def-per-prime-to-ell-alteration-topology shares alt/S but imposes degree and decomposition conditions in its topology; it is reused for the underlying category rather than duplicated. def-trf-strict-normal-crossings-boundary supplies the existing boundary notion.

## Review by Q51

I checked the definition against the actual ILO passages, rather than inferring the ordinary topology from a prime-to-ell theorem. II 1.2.2 specifies finite-type reduced maximally finite dominant S-schemes. II 1.1.2 and 1.1.8-1.1.9 express exactly the generic-point image and finite residue-field requirements written here. With parameter 1 the extra degree condition disappears. II 2.1.1 likewise makes the decomposed-etale condition an ordinary etale cover. II 2.3.1 and 2.3.3 therefore give exactly the two generating families in the item. ILO explicitly warns that the two families alone need not be a pretopology; the item correctly takes the smallest Grothendieck topology, not just these families. It never substitutes an ordinary scheme fibre product for a fibre product in alt/S.

I opened every statement dependency. def-pc-scheme supplies schemes, morphisms and affine opens, and def-weil-pbc-noetherian-ring supplies the coordinate-ring condition in the explicit finite-cover definition of Noetherian scheme. def-weil-finite-type-morphism supplies finite type, def-pc-reduced-scheme supplies reducedness, def-weil-irreducible-components supplies components, and def-weil-residue-field supplies the induced residue-field maps. Generic points are explicitly defined inline; the underlying category in def-per-prime-to-ell-alteration-topology is independent of its prime and agrees word for word with this one. No degree or invertibility hypothesis from its different topology is imported.

For the topology, def-weil-pbc-topos really defines sieves and the three Grothendieck topology axioms, not merely topoi. def-weil-etale-morphism, def-weil-proper-morphism and def-weil-surjective-morphism supply exactly the two sorts of generating arrows. Joint surjectivity means that each target point is hit by some member. Generated sieves and refinement are explicitly defined in the item. The smallest topology can be read literally as the pointwise intersection of all topologies containing those generators: the all-sieves topology ensures this collection is nonempty, and each of the three axioms is preserved under intersection. This is elementary well-definedness, not an additional existence lemma to hide in a new node.

For the marked predicate, def-pc-integral-scheme supplies the nonempty integral convention, def-weil-regular-scheme the regular local-ring condition, and def-trf-strict-normal-crossings-boundary defines the actual finite regular-component Cartier boundary with its empty boundary convention. The item asks for equality of supports of the inverse-image closed set, exactly as VII 1.1 does; it does not incorrectly require a scheme-theoretic inverse image to be reduced. No proof of uniformization, integrality of regular connected schemes, or finite-type Noetherian ascent is smuggled in as a clause. Each T_i is explicitly required to be Noetherian. The nowhere dense closed set means one whose closure has empty interior; being already closed, its interior is empty.

I tested S empty: the empty etale family generates the empty covering sieve at the empty object, so the explicitly allowed empty witness family makes U(empty,empty) meaningful and true. For S=Spec(k), Z must be empty and the identity singleton is a permitted witness: its source is integral regular Noetherian and its boundary is empty. For a reducible S the generic-point condition is componentwise, not surjectivity on every component; the topology imposes covering separately. For a nonreduced S, the category still has reduced objects; U is only defined for reduced S, so no unmentioned final-object assertion about nonreduced S is needed. A singular reduced S is also legitimate: U is a proposition, and this node does not claim the identity makes it true.

I checked B-E point by point. B: no new statements, no unintroduced objects, valid single TeX escapes, and sources read. C: there are no proof steps; every notion uses an opened definition that actually defines it, so citations.json has no proof-step entries. D: no theorem has been relabelled into a new node, and no clause has been split out as its own lemma. E: all hypotheses above were checked, inverse images are set-theoretic supports as stated, and there is no unstated prime assumption. There are no long proof steps to audit. The only changes needed were marking the audited definition split and recording the current searches and review.

The Mathlib hits were read: Sites/Etale.lean defines the etale topology on Scheme or the small etale category, without the proper-surjective generators; Sites/Coherent/Basic.lean defines categorical regular/coherent topologies by effective epimorphisms. Neither supplies alt/S or U(S,Z). Two distinct natural-language phrasings, LeanSearch, Loogle and the required msearch grep all ran successfully. No Mathlib leaf was claimed.
