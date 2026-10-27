1. Files written

- dag/nodes/sec-trace-formula/lem-trf-open-sheaf-coproduct-base-change.json: item, statement, split in seven steps; no exact Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-fppf-covering-is-fpqc.json: statement, Mathlib leaf, AlgebraicGeometry.Scheme.fppfPrecoverage_le_fpqcPrecoverage (Mathlib/AlgebraicGeometry/Sites/Fpqc.lean:66–69).
- citations.json: verbatim statement quotations for every citation of every item step.
- searches.jsonl: actual msearch.py records; existing item searches are retained, and this run's searches appended in the item.

2. Attachments

None. The read-only project Lean search by the item's blueprint tag and by coproduct/representability/fppf concepts found no declaration stating this relative comparison. The existing EtaleCoproductRepresentation declaration concerns restriction on the small etale site, not this item.

3. WANTED

None; all sources used are present locally.

4. What needed work

The item was statement-only and its existing searches were retained. Its statement is correct and unchanged. In particular the site-size assumption on C_T is retained, no jointly covering assumption on V_i was introduced, and no algebraic-space hypothesis on F_i or H was used. The familiar informal identification in Spaces 02WR requires a sheaf coproduct, not a pointwise presheaf sum. The proof uses the existing clopen-partition theorem rather than making that mistaken identification.

I read roles/worker.md, coord/brief-stage1.md, SETUP.md (including all three blueprint levels), GOAL.md, stages/1-dag.md, the chapter/unit records and delivery-errors B–E in both retained copies. This is an auxiliary categorical tool in the existing historical descent branch below lem-trf-local-term-locality, not a replacement proof of the contracting-correspondence unit. Its blueprint.from ancestry was retained; whole-blueprint searches for coproduct, 02WR, subcanonical and fppf covering found no node stating the item or the new covering-comparison lemma.

5. Unfinished

Nothing in this one-level split. The new node is an exact Mathlib leaf with an empty proof. Existing cited nodes retain their existing owners and statuses.

## Review by Q19

I read the item against literature/stacks-project/spaces.tex, Tag 02WR, lemma-glueing-algebraic-spaces, first proof paragraph. The source identifies the pullback of the sheaf coproduct with the scheme coproduct before using its covering or algebraic-space hypotheses. This confirms that those extra hypotheses are unnecessary for this item. I also read Spaces 0F15 (lemma-coproduct-sheaves-open-and-closed), including its omitted pullback verification, and 02WO (lemma-representable-sheaf-coproduct-sheaves). Those results underlie the existing lem-trf-fppf-sheaf-coproduct-partition; I read its full statement and proof. I do not use lem-trf-coproduct-scheme-pullback as a substitute: its assumptions and comparison are different.

For the one new node I read topologies.tex Tag 022C, lemma-zariski-etale-smooth-syntomic-fppf-fpqc, both statement and finite-affine-refinement proof. I read Mathlib/AlgebraicGeometry/Sites/Fpqc.lean:66–69: fppfPrecoverage_le_fpqcPrecoverage has precisely this statement. The previously recorded Mathlib interpretation of def-weil-pbc-fpqc-covering identifies its quasi-compact-open convention with Stacks' finite affine-open convention. The log contains real LeanFinder, LeanSearch, Loogle and grep queries for this node. Loogle finds the exact declaration; the other semantic hits describe precoverages and flat maps. For the item I ran a second phrasing with LeanFinder and Loogle after reading the first hits. Scheme.coprodPresheafObjIso concerns rings of structure-sheaf sections; LocalRepresentability.isRepresentable concerns gluing a Zariski sheaf along open charts; finite extensivity and coproduct component squares concern schemes, not the asserted relative fppf sheaf comparison. I read their relevant source contexts and did not call them matches.

Step 1 cites the new covering comparison and lem-weil-pbc-fpqc-representable-descent. The latter's statement explicitly gives existence AND uniqueness for arbitrary schemes and compatible maps on an fpqc family, with no finiteness hypotheses. It applies first with target X and then with target S to check that the descended map is over S. I read its source descent.tex Tag 023Q (lemma-fpqc-universal-effective-epimorphisms) and etale-cohomology.tex Tag 03O3. The finite-limit sheaf condition here is written directly: glue both components and check their equality after restriction; separatedness of F proves the equality globally. This is the equalizer axiom, not an unmentioned topos exactness theorem.

Step 2 cites the scheme coproduct lemma for its mapping property and disjoint clopen summands; the partition lemma for converse gluing of specified summand sections; and lem-pc-zariski-coverings-are-fppf for the fppf cover by those summands. I opened each node: these are exact clauses of their statements, rather than facts borrowed from their proofs. The universal s_i and equation iota_i(s_i)=t(v_i) come from the representing isomorphisms assumed in the item. Equality in F is checked on the summand cover. Step 3 uses the unique clopen partition and sections clause of the partition lemma, then the assumed universal property of each V_i to define g_i. The coproduct decomposition of W is part of the cited partition statement, so assembling g does not need a new lemma.

Step 4 uses the Zariski-to-fppf covering leaf, the scheme coproduct's disjoint open summands, the definition of open immersion (isomorphism onto the restricted open subscheme), and uniqueness of partitions and sections in the partition theorem. The inverse images D_i have their open subscheme structures; maps factor through them as open restrictions, not through an arbitrary locally closed subset on the basis of point containment. On each D_i both inverse constructions have the identical universal pair, so uniqueness in the assumed representation recovers g there. Step 1's sheaf property recovers g globally. This proves both composites, not just local existence of representatives.

Step 5 cites exactly the partition theorem's arbitrary restriction clause, then uses uniqueness of the maps representing their pairs to check the naturality equation. Step 6 cites the scheme coproduct mapping property. The maps d_i are specified by their two projections via the given representing opens; the equality of the two comparison arrows is checked on inverse-image summands and glued. The final explicit formula (g,b') maps to (g^*a_C,b') and then through Psi for T' verifies the base-change comparison itself, without assuming a theorem that coproducts commute with pullback. Step 7 applies precisely the definition of a representable sheaf map in def-trf-algebraic-space, not its additional algebraic-space conditions, and uses the partition theorem's empty-index formula.

Small cases checked: I empty and W nonempty (both section sets empty); I empty and W empty (both singleton); empty summands; two identical opens V_1=V_2=T (the labels remain distinct, so C_T has two copies); opens whose union is a proper subset of T (q need not be surjective); infinite I and a disconnected W meeting infinitely many summands (the construction uses the full clopen partition, never finite support). The new covering leaf permits an infinite family and empty target, where n=0 is allowed. All schemes and families are within the stated universe model. No source or statement dispute was found.

I checked delivery-errors B–E: the only new node is self-contained, statement-only and strictly a generic covering comparison, not a clause of the main representation; all its notions are cited; source tags/labels and the Mathlib line were read; searches are genuine; every non-elementary input has a cited statement and a verbatim quote. No proof step exceeds 2000 characters. The inline constructions are direct uses of specified representing bijections, restriction of maps to opens, the sheaf equalizer axiom, and coproduct universal properties. The dependencies do not point back to the item. The other-unit proof citations are existing Mathlib leaves, except the explicit definition of open immersion, used only for its meaning.

## Not duplicates

lem-trf-fppf-covering-is-fpqc vs lem-trf-space-closed-immersion-cover-descent: that node descends closed immersions between algebraic spaces along etale scheme charts; this leaf only compares fppf and fpqc covering families.

lem-trf-fppf-covering-is-fpqc vs lem-trf-fppf-local-open-subfunctor-descent: that node descends a locally represented open subfunctor along a local-lifting map; this leaf only compares covering families.

lem-trf-fppf-covering-is-fpqc vs lem-weil-pbc-finite-locally-free-degree-etale-descent: that node descends finite locally free morphisms of a fixed degree; this leaf is the topology comparison for arbitrary fppf families.

lem-trf-fppf-covering-is-fpqc vs lem-weil-pbc-etale-covering-affine-refinement: that node assumes etale maps and an affine target and produces a finite etale affine refinement; this leaf allows arbitrary fppf maps and targets.

lem-trf-fppf-covering-is-fpqc vs lem-weil-pbc-fpqc-finer-than-etale: that node treats only covering families in a small etale site; this leaf treats arbitrary fppf families, including non-etale maps.

lem-trf-fppf-covering-is-fpqc vs lem-galois-fpqc-descending-types-morphisms: that node is an effective descent reduction for properties of scheme morphisms with three extra assumptions; this leaf has no descent data or morphism property.
