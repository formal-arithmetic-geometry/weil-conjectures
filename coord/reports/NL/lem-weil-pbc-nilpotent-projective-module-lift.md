## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-nilpotent-projective-module-lift.json: statement split into six steps; not a Mathlib leaf.
- citations.json: verbatim statements for all three step citations.
- No new nodes. Two existing Mathlib leaves are reused.

## Attachments

None. Searches for the item tag and for projective-module/nilpotent lifting in WeilConjectures found no declaration stating the item. The upstream master is reference material only.

## Wanted

None: the required Stacks sources are present.

## Corrections and route

The statement of Tag 07LV was preserved: arbitrary projective modules, commutative A, globally nilpotent I, no finite generation. The formerly empty proof now follows its free-module projector argument. The noncommutative lifting invoked there is expanded by the proof of Tag 05BU into a commutative universal polynomial quotient, so it needs only the already existing commutative idempotent-lifting leaf. This does not assume End(F) is commutative.

I read the chapter and sk-thm-properbasechange unit records and the amplification ancestor's proof (c). This is a lower-level algebra input to the existing local-effectivity/projective-complex route, not a replacement of a unit step. Blueprint searches for projective module, projective, nilpotent, idempotent, and 00J9/05BU found no imported duplicate of the item. The existing étale finite-free-projector node needs finite rank and changes the ring; it does not prove this item. The existing locally nilpotent idempotent leaf is used exactly for a commutative polynomial quotient, not directly for an endomorphism ring.

Mathlib searches were run only through msearch.py. The first module-lifting phrasing returned one-ring lifting-property characterizations, finite projective splittings, and enough projectives. The second phrasing returned finite families of orthogonal idempotents, not projective-module lifting. Loogle and grep found no projective/nilpotent lifting theorem. The additional idempotent searches located exists_isIdempotentElem_eq_of_ker_isNilpotent at Mathlib/RingTheory/Idempotents.lean:249-253; I read that ring-general theorem and its surrounding proof. The existing commutative leaf is already the needed input, so no new ring-general node was created. LeanSearch was unavailable (Internal Server Error) and recorded as such.

## Unfinished work

None at this one-level split. No Lean was written or compiled. No delivery push is requested.

## Review by NL

I read algebra.tex Tag 07LV (lemma-lift-projective-module), Tag 05BU (lemma-lift-idempotents-noncommutative), and Tag 00J9 (lemma-lift-idempotents), together with the complete statements of def-weil-pbc-projective-module and lem-weil-pbc-lift-idempotents-locally-nilpotent. There are no new statements to review.

Step 1 takes the explicit direct-summand characterization from the projective definition leaf, which says there are maps i and s with si=id on an arbitrary free module. Its statement really supplies this, rather than just naming projectivity. Step 2 uses only finite-support coordinates: quotient vectors can be lifted individually even for an infinite basis; I wrote the construction and the kernel computation instead of silently using finite matrices. Step 3 proves the filtration inclusion by linearity and its induction, retaining the same global exponent N for every vector.

Step 4 applies the quoted commutative idempotent leaf to R=Z[t]/((t²-t)^N) and J=(u²-u). R is commutative and J^N=0, hence every element of J is nilpotent, exactly the leaf's hypotheses. Its conclusion gives the lift v and v-u in J. Step 5 evaluates this construction in End_A(F); polynomial evaluation is valid because integers are central and all powers of the one element p commute. The relation evaluates to zero by step 3. Writing the correction as a multiple of x explicitly proves its reduction is unchanged. Thus Tag 05BU's short universal-ring argument is expanded into the item, without creating an elementary specialization node.

Step 6 again uses the quoted direct-summand characterization, now for the image of the actual idempotent e. I checked e acts identically on its image, wrote the surjectivity onto the reduced projector image, and proved P intersect IF = IP by applying e to a finite sum. The displayed inverse verifies the quotient identification, including independence from the choice of lift. No flatness or tensor-exactness theorem is hidden in this step. All other facts are the explicit coordinate, polynomial, and quotient calculations written in the steps.

I checked the delivery-errors B–E points: no new node lacks definitions, searches or a source; no cited statement is being used for something absent from its text; the proof is an actual construction rather than relabelling the conclusion; and the only non-elementary inputs are the two cited existing leaves. Small cases checked were I=0 (already idempotent p), N=1, the zero module/empty basis (zero image and zero quotient), the zero ring, and infinitely generated free/projective modules (all vectors and sums still have finite support). Global nilpotence, rather than mere elementwise nilpotence of I, is essential in step 3 and is present in the item. No hypotheses were added and no statement dispute was found.


## Second reading by NL

- Item statement: checked algebra.tex Tag 07LV, `lemma-lift-projective-module`, hypothesis by hypothesis; faithful commutative-ring convention, globally nilpotent ideal, arbitrary projective quotient module, and exactly the reduction isomorphism; no statement dispute.
- Step 1: checked the full statement of def-weil-pbc-projective-module and algebra.tex 05CF, `lemma-characterize-projective`; its direct-summand clause supplies precisely the maps used, and $is$ is the required projector. PASS.
- Step 2: checked 07LV's lifted-projector sentence; the written finite-support coefficient argument proves surjectivity, the kernel, and the lift for an arbitrary basis, including the empty basis. PASS, elementary.
- Step 3: checked 07LV's nilpotence sentence; $A$-linearity sends $I^kF$ into $I^{k+1}F$, induction starts at $k=0$, and the same global $N$ kills every vector. PASS, elementary; no finite-rank hypothesis.
- Step 4: checked the complete statement of lem-weil-pbc-lift-idempotents-locally-nilpotent against algebra.tex 00J9, `lemma-lift-idempotents`, and 05BU, `lemma-lift-idempotents-noncommutative`; the universal ring is commutative and $J^N=0$ verifies exactly the leaf's elementwise-nilpotence hypothesis. PASS.
- Step 5: checked 05BU's universal-ring argument; integer scalars are central, evaluation sends the relation to $x^N=0$, and a multiple of $x$ has image in $IF$. No commutativity of the endomorphism ring is assumed. PASS, elementary polynomial calculation.
- Step 6: checked the projective definition leaf's direct-summand clause and 07LV's final image construction; the written sum calculation proves $P\cap IF=IP$ and lift independence. Added the two inverse compositions and the reason for $A/I$-linearity. PASS, elementary image/quotient calculations after the cited characterization.
- New nodes: none; B1–B7 introduce no new-node obligations. The two reused nodes are existing Mathlib leaves: read `Module.Projective.iff_split`, Algebra/Module/Projective.lean:236–239, and `existsUnique_isIdempotentElem_eq_of_ker_isNilpotent`, RingTheory/Idempotents.lean:373–380. Their statements supply exactly the cited clauses; citations.json contains their verbatim statements for steps 1, 4, and 6.
- Duplicate/source search: independently searched all DAG nodes for 07LV, 05BU, and 00J9, and both source checkouts for projective lifting. The etale finite-module lifting node has different hypotheses/conclusion and does not replace this item. Read the chapter/unit records and amplification proof (c); this is its subordinate projective-complex lifting input, with no changed route.
- Independent Mathlib searches: ran msearch.py leanfinder with “A projective module over a quotient by a nil ideal admits a projective lift over the original ring” (eight one-ring projectivity/splitting hits), and grep with `Projective.*[Qq]uotient|[Qq]uotient.*Projective` (twenty quotient, Grassmannian, projective-resolution/dimension, or unrelated projective-group hits). Neither states this coefficient-ring lifting result; actual output is recorded in searches.jsonl and the item's mathlib_searches.
- Edge cases: $I=0$ and $N=1$ give $x=0$ and the original projector; a field has only the zero nilpotent ideal; the zero ring and zero module/empty basis give the zero image and quotient. Infinite bases remain valid because every vector and every sum in $IF$ has finite support. $N=0$ is excluded in the statement; if permitted it would force the zero ring. There is no scheme hypothesis to test.

Changes: expanded step 6 with both inverse compositions and quotient linearity to make the claimed bijection directly checkable; removed split_report.tool_uses because delivery-errors C8 reserves tool-use recording to the maintainer, and the cited Mathlib leaf needs no route exception; appended two independently executed Mathlib searches with their actual results. Preserved the statement, all existing citations, all six steps, and the first worker's Review by NL section. No new nodes, Lean writes, or compiler/build calls.
