# Q54 stage-1 delivery

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-formal-power-series-continuous-conormal.json`: statement, now split; no exact Mathlib match. Nine proof steps, all using existing nodes.
- `citations.json`: verbatim statement excerpts for every cited node of every item step.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the slopmaster2 `WeilConjectures/` sources for the blueprint id, conormal, continuous differentials, formal power series and Kähler differentials, and checked the upstream names index. The hits concern ordinary scheme differentials, smooth finite presentations and étale algebras; no project declaration states this continuous conormal sequence. The item has no Lean-audit declaration. The read-only master source also supplies no exact attachment.

## Wanted literature

None. All sources used are available in `literature/stacks-project/`.

## Findings and changes

The mathematical statement was retained. The original node was statement-only and left the inverse-limit argument unspecified. Merely taking the inverse limit of right-exact conormal sequences would not prove surjectivity. I instead form the actual finite module N presented by the asserted sequence, apply the existing completeness theorem to N, and construct two explicit inverse maps between N and the differential inverse limit. The one-index shift is essential: a derivation sends the (r+1)st power of an ideal into its rth power, and need not kill the rth power modulo itself.

The ambient free theorem is independent of the item: its current DAG node has an empty proof and no edge to this item. It is a strictly different claim about the ambient power-series ring, already present and already used by the parent. The proof never cites the parent `lem-trf-formal-power-series-continuous-differentials`, avoiding a cycle.

The inherited `blueprint.from.place` describes an old Jacobian/nodal paragraph of the ancestry. I read the current main-20261015 ancestor and the unit: they now give the contracting-correspondence/Varshavsky argument, and contain no such nodal paragraph. I retained the existing ancestry and maintainer-owned unit rather than inventing an occurrence in the current source. The split report makes this mismatch explicit. This item remains a valid commutative-algebra ingredient of the existing nodal branch; neither the unit route nor any target was changed.

I considered an auxiliary finite-truncation tower node and ran exploratory searches for it, but dropped the uncommitted draft: it bundled most of the item's content and was unnecessary. The delivery contains no new node. Item search records retain their inherited searches and append the actual Q54 queries. The Q54 Loogle hit `KaehlerDifferential.mapBaseChange` and its exactness relatives were read at Mathlib/RingTheory/Kaehler/Basic.lean:719-850; they treat ordinary differentials and do not state this inverse-limit assertion.

## Not duplicates

No new nodes were created. Existing conormal node `lem-weil-pbc-jacobi-zariski-differential-maps` is the ordinary quotient conormal sequence (00RU), whereas the item concerns the stated inverse limits. Existing `lem-weil-pbc-kahler-differentials-mod-power-ideal` is the finite-level 02HQ comparison, not this continuous exact sequence. The ambient free node has no quotient ideal I. The parent continuous-differentials node is the full Jacobian presentation and depends on this item, so it cannot be cited here.

## Review by Q54

I read Algebra Tag 00RU, `lemma-differential-seq`, including its proof (34103-34155); 02HQ, `lemma-differential-mod-power-ideal` (34194-34209); the construction and universal property of Kähler differentials, 07BK and 00RO (33820 onward); 0306, `lemma-Noetherian-power-series` (6028 onward); and 00MA, `lemma-completion-tensor` (22901 onward). I verified their tags against `tags/tags`. I also read the current blueprint ancestor/unit, the chapter record, Curves 0C4D and the neighbouring continuous-differentials and continuous-free nodes. The continuous comparison is my proof, not a claim that Stacks 00RU already states the continuous version. There is no new-node source to audit.

Step 1 uses exactly the statement of the existing ambient continuous-free node: its basis gives finite generation of M, T and N. The base-change definition gives the tensor relations and extension of a linear map. The Kähler definition gives componentwise derivation identities. I checked that the ambient theorem allows every field and n=0, and does not assume a regular ideal.

Step 2 uses the statement of power-series-noetherian with the coefficient ring F, whose ideals are explicitly shown to be principal. The variables-complete node states completeness for every commutative coefficient ring and precisely the variables ideal. The finite-module-complete node states that the canonical map into compatible residue sequences is bijective; it is applied to the finite D-module N, not to the generally nonfinite ordinary module of algebraic differentials of D. The action factors through R, so the two ideal filtrations on N agree. These are exactly the hypotheses and exactly the canonical map needed later.

Step 3 uses only the Kähler definition and the displayed relation generators: differentiating a finite expression sum a_j f_j kills both terms after quotient. This makes the derivation on R genuine and well-defined.

Step 4 uses the universal property in the Kähler definition to construct each ring-induced differential map and to check its functoriality on all universal differential generators. The base-change definition supplies its extension to T. I checked that R_r is both D/n^r modulo the image of I and R/m^r, and that I acts by zero. Thus the map kills each defining relation of N. The stated generator formula is exactly the one that will appear in the conclusion.

Step 5 writes out the Leibniz estimate from 02HQ rather than using 02HQ by an uncited tag: a derivative of r+1 factors still has r factors in the ideal. This is a few-line use of the Kähler definition. The target is killed by m^r, hence also by m^(r+1); the derivation really has source R_(r+1) and target N/m^r N. The universal property cited in the node produces eta_r with that precise domain.

Step 6 verifies commutation of the eta maps on all d(x), so the shifted family belongs to the required inverse limit. Completeness from Step 2, already proved there with its citation, supplies the inverse iota^{-1}. No unproved exchange of a tensor product and a limit is used.

Steps 7 and 8 check both inverse identities separately. Step 7 checks N's finite generators and then uses injectivity of its canonical completion map. Step 8 first notes that m^r kills C_r, then checks the maps C_(r+1) to C_r on every d(x), not just on coordinates. This is why the inverse identity applies to arbitrary inverse-limit elements. The Kähler definition explicitly says these universal differentials generate its module; the quote was read and included in citations.json.

Step 9 is the elementary quotient calculation: ker(q)=L and image(R^s to T)=L, and composition with the established isomorphism changes neither the kernel nor surjectivity. The formula for the second map follows at each coordinate from Step 4. The first map need not be injective, which is consistent with the statement.

I checked delivery-errors B through E point by point. There is no unsplit new-node argument, elementary new node, duplicate, clause moved into a new node, unsupported non-elementary theorem, or circular citation. Every cited statement was opened and copied verbatim into citations.json. All proof steps have fewer than 2000 characters (longest 830), and the elementary steps write their quotient, derivation and coordinate arguments out. Generic completeness is declared as a tool use because the trace unit has no corresponding commutative-algebra result.

Small cases: n=0 forces I=0 and all differential modules vanish. I=0 and s=0 give the identity presentation. Zero and repeated f_j merely add zero or repeated generators of the same submodule. For n=1 and f=t, N=0 and R=F. For f=t^p over characteristic p the relation differential is zero, so N=R dt, as the ordinary differential calculation of F[t]/(t^p) requires; the proof does not divide by p. For f=t^2 in characteristic different from 2, N=(R/(t))dt; in characteristic 2 it is R dt. The index-shift estimate works in all these cases, including r=1. No hypothesis is silently added, and no statement is disputed.

## Unfinished work

None in this one-level split. Existing dependency nodes remain in their recorded states. Validation and delivery results are recorded below after the required tool exits.
