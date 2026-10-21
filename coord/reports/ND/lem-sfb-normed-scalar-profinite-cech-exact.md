# Stage-1 worker report

1. Files written:
   - `dag/nodes/sec-six-functors-basics/lem-sfb-normed-scalar-profinite-cech-exact.json`: item statement unchanged, eight proof steps, status split; not a Mathlib leaf.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-finite-valued-cech-cocycle-descent.json`: one new statement-only unsplit node; no complete Mathlib match.
   - `citations.json`: every step/node pair has a verbatim quotation from the cited statement.
   - `report.md`: this report. `searches.jsonl` was produced by the required msearch command.

2. Attachments: none. Searching the live `lean/WeilConjectures/` by the item tag, profinite/Cech notions and cocycle/quotient terminology found no declaration of the item. The additional `lean/Sheaf/` results give other constructions or upstream dependent inputs, not this result.

3. WANTED: none for this split. The obtained Bhatt–Scholze PDF supplies the coefficient route and the obtained Stacks topology source supplies the profinite approximation background. The explicit Cech argument is agent-written and marked accordingly, not attributed verbatim to a lemma which does not state it.

4. Problems found and corrected: the item was unsplit. Its statement already restricts to a complete finite extension E; it does not contain the noncomplete algebraic-closure claim mentioned in some inherited historical search verdicts. Those records are retained. The proof must not choose independent primitives modulo pi^m and then assert their inverse limit exists: steps 5–6 explicitly correct a lift by a finite-kernel primitive. A lift of a finite coefficient set is not assumed additive. The only new node preserves the cocycle equation at a finite quotient of the arrow, which mere factorization of one function does not supply. No statement dispute or target change was needed.

5. Unfinished: the new node is intentionally statement-only and unsplit, as required by the one-level split. Its later worker must establish finite-quotient descent of both the cochain and its equation. No other obligation in the item is moved to it. No Lean was written and no compiler, Lake or local DAG checker was run.

## Sources and search evidence

I read Bhatt–Scholze, *The pro-etale topology for schemes*, obtained PDF printed page 33, Lemma 4.3.9 and its proof. Part (2) concerns discrete modules; part (4) treats sequential inverse limits with profinitely split coefficient transitions; part (3) treats closed sequential coefficient colimits. I use this as the route, while proving the actual continuous-function Cech statement explicitly. I also read the current main-20261015 `_section.md` for sk-thm-sf-ctf-stability and its direct-images proof paragraph (3). That paragraph delegates the open-coefficient theorem; it is motivation, not a source claiming this analytic lemma. The inherited chapter, unit and from/via chain are retained. `blueprint_refs.py ancestor` returns None for this detached chain; I retain its null ancestor rather than fabricate a blueprint node.

For the new node I read Stacks `topology.tex`: Tag 08ZY (`lemma-profinite`, finite clopen-partition presentation), 08ZZ (`lemma-profinite-refine-open-covering`), 0A2P (`lemma-describe-limits`), and the nearby nonempty-limit lemma. These provide the topological ingredients, not a verbatim finite-Cech descent theorem. The source field explicitly says agent-formulated. A justification for the later worker is as follows. Index compatible finite clopen partitions of T and S. Their quotient arrows are surjective because q is. The inverse limits of their r-fold fibre powers are T_S^r: a compatible tuple of coordinates reconstructs r points of T whose q-images agree in every finite quotient of S, hence agree. Factor c through a finite stage using the existing locally-constant factorization theorem. The differential of that representative vanishes on the limit in the next degree. If it never vanished after refinement, the nonzero fibres would form a cofiltered system of nonempty finite compact spaces, contradicting the nonempty-limit property. Therefore after one refinement the representative is a cocycle. Finite-stage fibre-power projection maps are NOT assumed surjective; phantom tuples are removed by refinement of the equation. This is the non-elementary fact isolated in the new node.

Whole-DAG and whole-blueprint searches included profinite, Cech, finite quotient, finite clopen, continuous cocycle, cocycle, 08ZY and the item ancestor. Nearby group-cochain nodes require a group, an action, or prime-to-ell finite quotients, and do not state descent for a general profinite surjection. The finite-etale Cech comparison nodes concern schemes and sheaf coefficient colimits; they do not give this topological arrow presentation and equation descent.

Every new Mathlib search was made through `/home/ubuntu/weil-launcher-all/batch2/msearch.py ND lem-sfb-normed-scalar-profinite-cech-exact ...`, and its log record is preserved in the JSON results. Both the field-valued exactness question and the finite-valued descent question were asked with more than one phrasing. I read the returned Mathlib Cech constructor at CategoryTheory/Sites/SheafCohomology/Cech.lean:65 and the returned locally-constant factorization statements in Topology/Category/Profinite/CofilteredLimit.lean:109,124,156,191, plus Nobeling/Span.lean:228. They construct a complex or factor a function on a supplied limit; they do not supply descent of a cocycle equation on a finite quotient arrow. Nobeling exactness concerns its special locally-constant integer sequence, singular exactness concerns singular chains, and alternatingConst concerns a constant complex. None is an exact or one-line generalization of either delivered statement. Existing `lem-weil-pbc-profinite-limit-function-factorization` already names the Mathlib factorization result, so no duplicate factorization leaf was created.

## Review by ND

I checked sections B–E of delivery-errors against both files and the obtained sources. The new node introduces its spaces, finite coefficient group, fibre powers, all maps and all equations. It has a statement only, is not marked reviewed, has no proof sketch in its statement, and keeps all searches authentic. It is strictly subsidiary: it gives a finite cocycle representative and no primitive; the item itself supplies the contraction, the finite-kernel induction, integral reconstruction and field-valued conclusion. Elementary algebra and finite-set lifting stay in proof steps.

For step 1 I opened `lem-sfb-finite-quotient-fiber-product` and used exactly its assertion that its fibre product is compact Hausdorff and totally disconnected. Both factors and the base meet its hypotheses at every induction stage. The d-squared calculation cancels two ordered coordinate deletions with opposite signs; continuity follows from continuous faces and finite sums. Empty source implies empty base by surjectivity, and the zero cochain groups handle that case.

For step 2 I checked the full statement of the new node: its coefficient group is finite discrete abelian, its q is a continuous surjection, its degree is positive, and the cocycle equation holds on the exact same fibre powers. Its conclusion gives BOTH the finite arrow and the equation used for contraction. I verified the sign on `(sigma(s),x_0,...,x_n)`: the first face is c and the other faces have signs (-1)^(j+1), giving d v=c with v=c(sigma(s),...). Only the finite surjection q_0 has a section; no section of q is assumed.

For step 3 I opened `def-weil-l-adic-coefficient-extension`, `lem-weil-l-adic-extension-integers-dvr`, `lem-weil-valued-dvr-finite-quotients` and `lem-sfb-integers-profinite-tower`. Their statements respectively introduce the valuation data, give the DVR and a nonzero uniformizer in the maximal ideal, make every A_m finite with surjective transitions, and give the ring isomorphism AND homeomorphism O to the compatibility subspace. I did not infer any of those theorems from a definition alone. E is the same finite extension with the same extending norm, so all hypotheses match. These generic arithmetic and topology inputs outside the inherited unit are declared tool uses where necessary.

For step 4 the reductions are additive, and step 2 applies to the finite group A_1. The induction explicitly specifies both d g_m=f_m and transition compatibility. For step 5 the cited finite-quotient theorem supplies the surjection, and a section between finite discrete sets is continuous. Its lack of additivity is harmless: only p_m is used to commute with d. The error cochain lands in the finite kernel and is a cocycle by the already proved d-squared identity. For step 6 step 2 applies to this kernel as a finite abelian group. Subtracting its primitive gives BOTH equations of the induction, with the sign written out. These are arguments internal to the earlier steps, not new unlabelled non-elementary facts.

For step 7 I checked the tower theorem's actual conclusion: the inverse is continuous and reduction maps distinguish elements because the map is a ring isomorphism. The map to its product-subspace target is continuous coordinatewise. Reducing the finite alternating sum proves the desired equality in O; no limit-exactness or Mittag-Leffler theorem is being used without a citation.

For step 8 compactness is the assertion read in the fibre-product node, iterated as in step 1. The increasing open sets |f|<|pi|^(-k) cover the compact domain, hence one index bounds all values. Multiplying by pi^k gives a continuous map into O with its subspace topology and preserves the cocycle equation. Dividing the resulting primitive by the SAME pi^k recovers f. Completeness enters through the topological integral inverse-limit theorem, and no bound for an algebraic closure is claimed.

Small-case checks: the empty surjection has all groups zero; for the identity or a one-point fibre, d alternates between 0 and identity, agreeing with the contraction; n=1 needs a degree-zero primitive only; n=2 has the displayed positive insertion sign; coefficient groups 0 and Z/2 cause no division and are included. The induction also allows a zero kernel. Arbitrary profinite cardinality uses no countability of T or S; only the coefficient tower is sequential. Finite-dimensional local E is retained; no assertion about noncomplete Omega is introduced. Every proof step is under 1000 characters, so none hides a greater-than-2000-character argument. The genuine finite-stage comparison is separated as the new node. I checked every citation quote against its statement and recomputed proof_deps as exactly the union of uses. No statement changed, no inherited blueprint metadata or import flags were removed.

## Not duplicates

lem-sfb-finite-valued-cech-cocycle-descent vs det-pe-condensed-point-basis: the existing statement is Affine ind-étale schemes over a separably closed field; its objects and conclusion are unrelated to finite discrete Cech cocycle descent on a continuous surjection of profinite spaces (any section-number match is not that topological assertion).

lem-sfb-finite-valued-cech-cocycle-descent vs det-pe-stonean-projective: the existing statement is Gleason: extremally disconnected equals projective; its objects and conclusion are unrelated to finite discrete Cech cocycle descent on a continuous surjection of profinite spaces (any section-number match is not that topological assertion).

lem-sfb-finite-valued-cech-cocycle-descent vs lem-sfb-compact-discrete-quotient-realization: the existing node realizes a compatible family of quotient points in one compact space; it does not descend a cochain and its differential equation.

lem-sfb-finite-valued-cech-cocycle-descent vs lem-sfb-finite-quotient-fiber-product: the existing node identifies one binary fibre product with a specified inverse limit; the new node descends a finite-valued higher Cech cocycle together with its equation to one finite quotient arrow. The equation-descent conclusion is absent from the existing statement.

lem-sfb-finite-valued-cech-cocycle-descent vs lem-sfb-integers-profinite-tower: the existing node is the topological ring presentation of O_E by its arithmetic quotients, not descent of a cocycle on an arbitrary profinite surjection.

lem-sfb-finite-valued-cech-cocycle-descent vs lem-weil-pbc-profinite-clopen-basis: the existing node gives a clopen neighbourhood basis for one space, not finite quotient diagrams or cocycle equations.

lem-sfb-finite-valued-cech-cocycle-descent vs lem-weil-pbc-profinite-limit-function-factorization: the existing node factors one locally constant function on an already supplied limit; it does not provide a finite quotient of q on whose entire higher nerve the cocycle equation holds.

lem-sfb-finite-valued-cech-cocycle-descent vs lem-weil-pbc-spectral-directed-limit-spectral: the existing statement is A directed limit of spectral spaces along spectral maps is spectral, with spectral projections; its objects and conclusion are unrelated to finite discrete Cech cocycle descent on a continuous surjection of profinite spaces (any section-number match is not that topological assertion).

lem-sfb-finite-valued-cech-cocycle-descent vs lem-weil-pbc-spectral-limit-descend-opens: the existing statement is Quasi-compact opens of a directed limit of spectral spaces descend to a finite stage; its objects and conclusion are unrelated to finite discrete Cech cocycle descent on a continuous surjection of profinite spaces (any section-number match is not that topological assertion).

lem-sfb-finite-valued-cech-cocycle-descent vs lem-coef-algebroid-cocontinuous-base-change: the existing statement is Cocontinuous unary change of enrichment on algebroids; its objects and conclusion are unrelated to finite discrete Cech cocycle descent on a continuous surjection of profinite spaces (any section-number match is not that topological assertion).

lem-sfb-finite-valued-cech-cocycle-descent vs lem-coef-algebroid-object-space-fibration: the existing statement is Cartesian fibration of categorical algebras over object spaces; its objects and conclusion are unrelated to finite discrete Cech cocycle descent on a continuous surjection of profinite spaces (any section-number match is not that topological assertion).

lem-sfb-finite-valued-cech-cocycle-descent vs lem-coef-counit-cone-boundary-extension: the existing statement is Counit extension of a three-object boundary diagram; its objects and conclusion are unrelated to finite discrete Cech cocycle descent on a continuous surjection of profinite spaces (any section-number match is not that topological assertion).

lem-sfb-finite-valued-cech-cocycle-descent vs lem-coef-enriched-coherent-adjunction-extension: the existing statement is Enriched extension from adjunction data to the walking coherent adjunction; its objects and conclusion are unrelated to finite discrete Cech cocycle descent on a continuous surjection of profinite spaces (any section-number match is not that topological assertion).

lem-sfb-finite-valued-cech-cocycle-descent vs lem-coef-enriched-simplicial-presentation: the existing statement is Simplicial presentations retaining the enriched functor calculus; its objects and conclusion are unrelated to finite discrete Cech cocycle descent on a continuous surjection of profinite spaces (any section-number match is not that topological assertion).

lem-sfb-finite-valued-cech-cocycle-descent vs lem-coef-homotopy-adjunction-coherent-witnesses: the existing statement is Counit object is terminal in the right-slice pullback of a homotopy-2-category adjunction; its objects and conclusion are unrelated to finite discrete Cech cocycle descent on a continuous surjection of profinite spaces (any section-number match is not that topological assertion).

lem-sfb-finite-valued-cech-cocycle-descent vs lem-sfb-field-profinite-galois-site: the existing statement is The pro-etale field site as profinite Galois sets; its objects and conclusion are unrelated to finite discrete Cech cocycle descent on a continuous surjection of profinite spaces (any section-number match is not that topological assertion).

lem-sfb-finite-valued-cech-cocycle-descent vs lem-sfb-normed-scalar-profinite-cech-exact: the item concludes existence of a continuous primitive over complete E; the new node only supplies a finite representative for a finite discrete coefficient cocycle, without a primitive or any integral or field limit.

lem-sfb-finite-valued-cech-cocycle-descent vs lem-sfb-normed-scalar-profinite-hom-acyclic: the existing statement is Underived continuous functions compute derived internal functions of profinite parameters; its objects and conclusion are unrelated to finite discrete Cech cocycle descent on a continuous surjection of profinite spaces (any section-number match is not that topological assertion).

lem-sfb-finite-valued-cech-cocycle-descent vs lem-sfb-profinite-action-finite-quotients: the existing node presents an action by finite invariant quotients of a single profinite G-space, not a general surjection and its Cech cocycle equation.

lem-sfb-finite-valued-cech-cocycle-descent vs lem-sfb-spectral-clopen-component-homeomorphism: the existing node compares connected-component spaces under a clopen bijection; it says nothing about cochains or finite arrow descent.

## Validation

The required server checks and final delivery are run after this signed review; their authoritative output is the deliver.py result.
