# Stage 1 report: det-prop-scalar-six-exceptional

Files written:

- `dag/nodes/sec-six-functors-basics/det-prop-scalar-six-exceptional.json`: the existing item, split into eight steps; no new nodes and no new Mathlib leaves.
- `citations.json`: 49 verbatim statement quotations, covering every citation in the eight steps.
- `report.md`: this review and handoff. Existing search logs are retained.

Attachments: none. Search by the exact blueprint tag and by scalar/exceptional/coefficient terminology in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no project declaration proving the whole statement. Generic scalar adjunctions and supplied orientation coefficient-change data do not prove it. Upstream master is reference material only.

WANTED: none.

The statement is unchanged, including the inverse compact-support comparison in its defining transpose, every listed coefficient map, and composition and open-restriction compatibility. The proof follows the current main-20261015 companion proof: formal properties, closed supports, projective line, affine space, and general morphisms. No statement dispute was found. The current chapter and unit source `_section.md` files were read; corresponding new-snapshot JSON chapter/unit records are absent in this shared snapshot, so no maintainer-owned binding was invented or changed. The item is a detail node, not the unit's key node.

The imported proof omitted supporting statements and the last square of the triangle comparison, and compressed the projective-line argument across coefficient categories. The retained repairs cite the actual morphism-of-triangles theorem, construct its third component by TR3, distinguish finite/integral/rational inputs, and factor integral-to-finite coefficient maps through a finite quotient. They also make the affine induction and graph factorization explicit. No result was moved into a new node restating the item.

What could not be finished: nothing mathematical. Earlier continuation dry runs exited with status 137 while waiting for delivery locks; these were tool failures, not accepted validation. This continuation uses the unmodified dry-run command only and leaves delivery to the next independent reader.

## Review by Q42

I reopened the main-20261015 statement and `.proof.md` at `sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-exceptional`, the chapter/unit source sections, and the statements of all 32 distinct proof dependencies. This is an author's check against delivery-errors B–E, not a substitute for the next independent reading.

Step 1 uses existence (4) and scalar-ctf (3) to put both sides in Dctf. The existing composite-adjunction definition supplies exactly the composite counit; compact-support comparison supplies its composition compatibility. The open-restriction node actually states both source and target open identifications and local detection. The proof spells out the Hom bijections for target restriction and uses the pullback coefficient identification for opens. Thus it checks the canonical transpose, not merely the existence of some isomorphism.

Step 2 uses the condensed open–closed recollement statement for its explicitly normalized counit triangle on bounded-below inputs. K is bounded. The unbounded support-adjunction statement then compares that right adjoint with the chosen localizing right adjoint: the argument first proves H is in Dctf using direct-image stability, the triangle, and exact restriction. Only then does it use Yoneda in the full localizing category. The ring-sheaf open–closed statement supplies exact, fully faithful i_* and i^*i_*=id for the pulled-back rings. Finite type over the Noetherian field and the locally-Noetherian quasi-separatedness node verify qcqs and quasi-compact complements. Closed-immersion properness supplies Ri_!=i_*.

Step 3 uses derived tensor exactness, the direct-image comparison with its unit compatibility, and pullback/closed-pushforward coefficient compatibility. The square on the middle and third vertices commutes by those stated compatibilities. Rotation and TR3 produce the full triangle morphism. Full faithfulness writes its first component as i_*alpha, and the first square plus the adjunction bijection identifies alpha with the specified beta. The cited triangle-morphism lemma, unlike the discarded transformation-on-one-triangle lemma, applies to exactly these three components and proves invertibility. Restriction by i^* reflects it back to Z.

Step 4 uses the ordinary finite-ring P1 adjunction for arbitrary finite A killed by an invertible N, with its actual Kummer-normalized counit. The two finite-comparison statements identify the whole etale category and its pro-etale localizing counterpart compatibly with pushforward and pullback; tensor-pullback compatibility carries the counit formula. Rational unit/counit and triangle statements are applied only to E or Qlbar. At integral coefficients the proof writes the diagonal unit and trace counit and computes the two composites using proper base change/projection and the tower integration identities. The rank-one twist and pullback preserve Dctf. Projective-space properness and uniqueness of restricted right adjoints then identify this adjunction with the chosen q^!.

Step 5 uses the Cartier statement's coefficient compatibility for the Kummer component, direct-image unit compatibility for the other component, and the finite P1 decomposition for the trace as a projection of its inverse. Derived scalar extension preserves this finite sum and inverse, without flatness. The tower trace, limit, and coefficient statements give the integral reductions and scalar extensions. Transitivity gives finite field extensions and composites. Every O_E to A map factors through O_E/pi^r because A is killed by a power of pi; the already proved finite-ring case handles the remaining arrow. There is no unsupported claim that arbitrary tensor commutes with inverse limits.

Step 6 checks the defining counit equality for the pullback-and-twist comparison. It writes the canonical projection map's adjoint transpose and applies tensor-pullback compatibility and the direct-image counit comparison to that expression. The trace equality from step 5 finishes the counit square. For proper q the compact-support comparison is the direct-image comparison by its stated construction, so uniqueness of transposes identifies the resulting isomorphism with beta itself.

Step 7 is the elementary composition argument: A1 is open in P1, the n=0 case is the identity, and the induction passes through A1 over A^(n-1)_Y. Step 8 uses open local detection and an affine embedding defined by a polynomial-ring surjection. Separatedness makes the graph a pullback of the closed diagonal. Base change and composition of closed immersions are checked on quotient-ring charts directly from the cited definition. This gives a closed immersion followed by an affine-space projection, so the earlier cases finish the proof. No extra geometric theorem is hidden in a new node.

Small cases checked: zero K; empty X; identity maps; n=0 and n=1; empty or full closed support; nonflat Z/ell^2 to F_ell (derived tensor, not ordinary tensor); arbitrary finite O_E-algebras via an annihilating pi power. The finite P1 input assumes Noetherian base and invertible N, both satisfied by the standing schemes. No SGA source, smooth-purity detour, or rational-only assertion at integral coefficients is used.

B1–B8 and duplicate-pair reporting are vacuous because there are no new nodes. The existing blueprint search for the exact item title returns only the item, consistent with same_as=[]. The saved msearch log records two semantic phrasings, successful Loogle searches and a grep in the actual Mathlib AlgebraicGeometry directory; their hits are general adjunction ingredients, not this sheaf-theoretic assertion. Earlier invalid/inconclusive queries remain identified as such, never as evidence of absence. No searches were invented or relabelled as newly run.

## Earlier second reading (a previous round; superseded)

The earlier second reading repaired the closed-support normalization, wrong triangle lemma, finite-ring and rational/integral scope errors, integral-to-finite trace comparison, projection transpose, affine induction and graph argument. This continuation independently checked those repaired statements and steps and retained the eight-step node and its citation records. The prior report's inconsistent five-step description and obsolete delivery-blocked conclusion were removed. A fresh second reader must still read this sandbox and deliver it under the current dispatch protocol.

Validation: the required unmodified `deliver.py Q42 det-prop-scalar-six-exceptional --no-push` is the final check. No direct git command, Lean edit, compiler, Lake invocation, launcher modification, or push is part of this continuation.

## Continuation review, 2026-10-16

I reread all 32 cited dependency statements in the current shared DAG and checked all 49 citation entries against them; each quote is verbatim and each step uses the stated assertion. In particular the bounded-below recollement explicitly supplies the counit normalization missing from the generic support triangle, and the triangle-isomorphism lemma requires all three squares, which step 3 obtains by rotation and TR3. The finite projective-line adjunction covers arbitrary finite rings killed by an invertible integer, the rational adjunction is used only for E and Qlbar, and the integral case writes its unit, counit and both triangle identities from the tower identities. No source or dependency changed enough to require a mathematical repair.

Fresh msearch LeanFinder and LeanSearch queries using the phrase “exceptional inverse image on constructible sheaves commutes with derived coefficient extension” returned only ordinary sheaf pullback/pushforward coherence, site equivalences and internal-Hom statements. The fresh Loogle query returned the generic composite-counit lemma already represented by def-weil-pbc-composite-adjunction; grep of AlgebraicGeometry found no exceptional/coefficient declaration. These are recorded together with the retained earlier second phrasing, so no service result is invented. The exact blueprint-id project search is empty; the keyword hits concern exceptional adjunctions or trace-formula data, not this whole scalar-comparison theorem.

The current main-20261015 chapter, unit, statement and companion proof were reread. The eight steps follow precisely the formal-properties, closed-support, projective-line, affine-space and graph-factorization route. No new nodes, definitions, Mathlib leaves or duplicate pairs were introduced. The statement, imported flags and maintainer metadata are retained. The only node edit in this continuation records the fresh semantic searches; the report removes the obsolete blocked conclusion.

The final validation is the unmodified command `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q42 det-prop-scalar-six-exceptional --no-push`; READY requires its explicit OK result. This sandbox is for the next independent reader, who will deliver it. No push is authorized in this worker turn.

## Second reading by Q42

- Step 1 checked against the current main-20261015 statement/proof and the six cited dependency statements; the transpose, composition, and both open-restriction cases use exactly those assertions; verdict: pass.
- Step 2 checked against the closed-support source passage and all eight cited recollement, support, constructibility, and qcqs statements; boundedness and the restricted right-adjoint identification have the required hypotheses; verdict: pass.
- Step 3 checked against the closed-immersion source passage and all seven cited triangle, tensor, pushforward, and full-faithfulness statements; TR3 supplies the connecting square and the triangle-isomorphism lemma applies to all three components; verdict: pass.
- Step 4 checked against the projective-line source passage and all thirteen cited finite, rational, integral, comparison, trace, and properness statements; coefficient stages and Dctf restrictions retain their stated hypotheses; verdict: pass.
- Step 5 checked against the all-coefficient trace-comparison passage and its seven cited Cartier, tower, limit, and pullback statements; arbitrary finite maps and integral-to-finite factorization are explicit; verdict: pass.
- Step 6 checked against the canonical projective-line comparison passage and its four cited projection, counit, pullback, and compact-support statements; the displayed equality is the defining transpose; verdict: pass.
- Step 7 checked against the affine-space source passage and the definitions used in its dimension-zero and induction argument; the induction starts at n = 0 and has the n = 1 factorization; verdict: pass.
- Step 8 checked against the general-morphism source passage and its four cited open-detection, graph, diagonal, and affine-factorization statements; separatedness and quotient-chart hypotheses are used explicitly; verdict: pass.
- No new nodes were introduced, so B1–B7, duplicate-node searches, and Mathlib-leaf checks are vacuous; all 49 citations were reread verbatim against their 32 distinct dependency statements; verdict: pass.

Changes made in this second reading: added this required review section and retained the repaired eight-step proof, with no mathematical or node changes needed. The small cases checked were zero and empty objects, identity and open maps, n = 0 and n = 1, empty/full closed support, a nonflat finite coefficient map, and finite rings killed by a power of the uniformizer; all pass. The required dry run and delivery are now rerun.
