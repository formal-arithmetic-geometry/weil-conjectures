# Stage-1 delivery: lem-sfb-proper-polynomial-comparison-class-normalization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-proper-polynomial-comparison-class-normalization.json: statement, split in seven steps; no exact Mathlib match. The inherited searches are retained, and actual NY searches are appended with their recorded results.
- citations.json: 23 verbatim statement quotations, one for every citation in the seven proof steps.
- No new nodes; no Mathlib leaves. All additional ingredients already exist in the live DAG.

## Attachments

None. Searches in lean/WeilConjectures/ by the exact blueprint tag, item id, polynomial/diagonal terms, and relative-dualizing terminology found no declaration stating this assertion. The similarly named finite-coefficient smooth-duality files concern a different coefficient theory. The existing polynomial-model declaration is under Sheaf, is an existence statement, and does not constitute an attachment of this item's chosen-class normalization.

## Literature

WANTED: none.

I read duality.tex, definition-relative-dualizing-complex (0E2T), lemma-relative-dualizing-complex-algebra (0E2U), lemma-uniqueness-relative-dualizing (0E2W), the section-gluing proof of lemma-existence-relative-dualizing (0E2X), lemma-flat-proper-relative-dualizing (0E2Z), remark-relative-dualizing-complex-bis (0E4P), remark-relative-dualizing-complex and equation-pre-rigid (0E2P), and the polynomial comparison discussion at remark-local-calculation-shriek (0BV2). I also read dualizing.tex, section-relative-dualizing-complex-algebraic (0BZI), including its footnote about top differential forms, lemma-well-defined (0BZJ), lemma-relative-dualizing-noetherian (0E2E), and lemma-base-change-relative-dualizing (0E2F). The latter is useful to delimit the literal source: it does not specify the arbitrary-ring graph arrows or their equality with particular proper comparison maps. The proof is accordingly marked agent-written, not attributed verbatim to Stacks.

For the representing comparison I read more-algebra.tex, lemma-internal-hom (0A65), lemma-dual-perfect-complex (07VI), lemma-perfect-over-polynomial-ring (068X), and dga.tex, lemma-tensor-hom-adjoint (09LT), and the existing arbitrary-polynomial-diagonal-hom statement and proof. The item only uses its stated natural derived isomorphism, not intermediate objects in that proof. No SGA source is used.

## Statement clarification: STATEMENT-DISPUTED

The imported text referred to the specified canonical comparisons of the polynomial-model theorem, but its statement alone only specified the object isomorphisms, restrictions and refinement normalizations. Those conditions do not determine a comparison from the proper trace object: for f = id on Spec(Q), multiply every chart comparison by -1. Every comparison between polynomial charts, every restriction and every refinement contraction is unchanged, whereas the equation identifying the proper class 1 with the graph class 1 fails on the zero-variable chart. Thus it would be C3 to claim the class equation from the bare statement of that theorem. Calling the arrows canonical does not supply the missing construction.

I preserved the imported mathematical assertions and added an explicit construction convention. First identify K_f with the proper trace pair, and construct its class from the local adjunctions. On a chart, for any B-linear natural representing bijection psi, put w = psi_C(xi_P) and e = psi_M(gamma) composed with w inverse. The specified comparison is the realization of e inverse. Invertibility, independence of psi, the class equation and uniqueness are conclusions proved in Steps 3–7. This is an independent representability prescription, not an assumption that the desired class equation already holds. It makes precise the intended construction of the model's proof (unique pair identifications after fixing the graph class), without using an unstated conclusion from that proof as a theorem interface. No geometric or Noetherian hypothesis was added or removed, and no proper trace-pair base-change comparison was identified with polynomial exchange.

## Blueprint and searches

I read the recorded chapter and unit, and the current latest blueprint sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images proof (3). The inherited coherent-duality branch is downstream of the alteration/moduli argument; this delivery only treats that branch's requested normalization. The ancestor command reports blueprint.from.node = null, which I preserved together with the full inherited place and via chain. The split_report names which steps realize this supporting argument. No chapter or unit record is changed.

Whole-blueprint searches for polynomial comparison, polynomial-diagonal, relative dualizing, dualizing and diagonal, together with DAG searches for 0E2W/0E2Z/0E4P/0BV2 and polynomial-diagonal Hom, were read. In particular, lem-sfb-arbitrary-polynomial-diagonal-hom already gives the arbitrary-ring derived comparison, and lem-sfb-arbitrary-polynomial-dual-properties already gives the polynomial object's finiteness and scalar map. I therefore created neither a second reduction lemma nor a second relative-perfectness lemma. No blueprint node states this chosen proper trace/graph normalization in another form; same_as remains empty.

NY's searches were run only through msearch.py and are present in searches.jsonl. The two semantic phrasings returned ordinary differential and cotangent constructions; Loogle's dualizing query returned no hits, and its derived/Hom query returned only generic derived-category declarations. The regex searches returned an order diagonal and unrelated polynomial antidiagonal lines. LeanSearch returned proper/flat scheme facts and ordinary differential facts. These do not have the same objects or conclusion as this item. The original item's five searches were retained, not represented as newly performed NY searches.

## Review by NY

I checked the split against delivery-errors B–E with the source passages and the statements of all cited nodes open. There are no new statement-only children to audit for hidden proof text, omitted definitions, elementary duplication, or restated clauses. The item has genuine assembly arguments; it does not move its clauses into children. No non-elementary step exceeds 2000 characters (the longest is about 1210). I made no Lean edits and ran no compiler or local project checks.

Step 1 uses the space trace-duality statement for the local Hom characterization and trace-preserving uniqueness, the etale/Zariski equivalence for structure modules, pushforward and pullback, and the tensor formula for the exact adjunction counit. The local adjunction statement applies because proper implies quasi-compact and separated; it explicitly allows a non-qcqs base and an infinite affine cover. The model theorem supplies the already existing global adjoint. The comparison between two representing objects is obtained directly from their Hom bijections, so it has no undetermined scalar. The proper-adjoint-diagonal-pair statement gives both the actual local class and its preservation under trace-preserving identifications. Its qcqs hypothesis is used only on affine bases and their proper inverse images.

Step 2 uses the restriction statement for derived internal Hom, the global-sections/Hom statement, and the proper-adjoint theorem's explicit overlap compatibility. The self-products above affine bases really cover the entire fibre product: each point has one common base image. Local multiplication identifies H with a degree-zero sheaf, so these local morphisms are ordinary compatible sections, not an unjustified derived-Hom sheaf descent assertion. H^0 of derived global sections of a degree-zero sheaf is its ordinary sections; a nonnegative injective resolution proves this. The definition of a coherent pair is used only after local pseudo-coherence, local relative Tor amplitude and invertible multiplication have been obtained. Intersections of base affines are covered by affines, never assumed affine.

Step 3 applies arbitrary-base-affine-dualizing-realization to the now supplied pair, with the two input pairs equal. Its statement gives exactly flat finite presentation of R -> B, R-perfectness of M and the multiplication map of the actual restricted class. Arbitrary-polynomial-dual-properties applies to this flat finitely presented algebra and the selected polynomial surjection. The ordered differential volume identifies its coefficient P[n] with Omega^n[n], preserving the coinduction action. The graph-class theorem gives the specified xi_P and its multiplication isomorphism, not just some rank-one generator. The unmarked-isomorphism theorem's hypotheses are then all satisfied for M and C_P. Its isomorphism a is only an auxiliary witness, never claimed to preserve classes.

Step 4 uses the stated arbitrary-ring natural derived isomorphism, takes H^0, and retains restriction along the first coprojection. The scalar map from the polynomial-dual-properties statement identifies End(C_P) with the regular B-module and its composition algebra; it is not merely an unspecified rank-one identification. The multiplication maps identify the two class modules with B, with the actual classes as generators. Therefore psi_C(xi_P) is a unit, and psi_M(gamma) is a unit times any isomorphism a. This explicitly proves invertibility before taking either inverse. It does not infer a normalized equality from an arbitrary isomorphism.

Step 5 is the elementary naturality equation psi_T(u_*xi_P) = u composed with w. Cancellation proves the class equation and the independence from psi. All objects and naturality used here were introduced in Steps 3–4, so this step needs no additional node. It is more than the unsupported phrase 'the same calculation': the arrow equation, its inverse image and the cancellation are displayed.

Step 6 uses the affine-realization statement only for the source class gamma, and the canonical affine pullback/tensor comparison for the actual arrow e inverse. No theorem about two already coherent pairs is applied to the polynomial pair before its coherence is proved. Instead the ring class equation is sheafified, the underlying object isomorphism transports finiteness, and the explicitly natural tensor–Hom transpose transports the multiplication isomorphism. This verifies exactly the definition of a supplied coherent pair, including its actual class map.

Step 7 applies open rigidity only after both pairs are supplied. Its statement gives unique class-preserving isomorphisms over arbitrary bases and includes empty opens. A changed scalar would change a generator; this is why it must be 1. I tested B = 0, empty charts, n = 0, the identity morphism over Q, and the identity morphism over a non-Noetherian ring. In the last case the zero-variable prescription gives w invertible and e the identity after the trace identification; no finiteness of the base ring occurs. The zero ring case uses the unique endomorphism of zero, which is both its identity and its invertible map. An arbitrary coordinate presentation of a non-complete-intersection flat algebra does not introduce any regularity requirement on its defining ideal: only the graph class theorem is used.

The generic off-unit tool uses are declared in split_report.tool_uses. These are derived internal Hom restriction, derived global sections/Hom, and affine pullback/tensor realization, not substitute six-functor routes. I checked for cycles by reading the relevant dependency interfaces; the required server DAG check remains authoritative.

## Not duplicates

No new nodes. The existing arbitrary-ring diagonal Hom and polynomial-dual-properties statements are reused; the Noetherian polynomial-diagonal-rhom-reduction is insufficient for the arbitrary-base assertion and is not used.

## Outstanding work

None in the stage-1 split. Mechanical server validation and delivery follow this report. The canonical-arrow specification gap above is reported for the maintainer's independent mathematical review.
