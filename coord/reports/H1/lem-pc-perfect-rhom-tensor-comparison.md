Files written:

- `dag/nodes/sec-picard-framework/lem-pc-perfect-rhom-tensor-comparison.json` (statement, split)
- `dag/nodes/sec-picard-framework/lem-pc-affine-perfect-complex-duality.json` (statement-only auxiliary node; Mathlib searches found no match)
- `citations.json`

Attachments: none.  WANTED: none.

## Not duplicates

lem-pc-derived-tensor-internal-hom-adjunction vs lem-sc-derived-internal-hom-adjunction: the new node states the adjunction in direct variables A, I, E and identifies the evaluation composite used by this item, while the existing node additionally specifies K-flat representatives and the tensor symmetry isomorphism.

lem-pc-derived-tensor-internal-hom-adjunction vs lem-sc-ext-stalk-localization: the new node states the global tensor-internal-Hom adjunction for arbitrary objects of D(O_X), while the existing node only identifies stalks of sheaf Ext for coherent modules on a Noetherian scheme and does not state an adjunction.
lem-pc-derived-tensor-internal-hom-adjunction vs lem-pc-derived-internal-hom-pullback-adjunction: the new node states the three-variable tensor/internal-Hom adjunction on one derived category D(O_X), while the existing node states a pullback/direct-image compatibility isomorphism for a morphism g and does not state the underlying tensor-Hom bijection.

lem-pc-affine-perfect-complex-duality vs lem-pc-perfect-rhom-tensor-comparison: the new node is the algebraic calculation for one bounded finite-projective complex over a ring, while the item is the global scheme-level RHom, quasi-coherence, zig-zag, and derived-pullback/base-change theorem.
lem-pc-affine-perfect-complex-duality vs lem-sc-finite-locally-free-derived-hom: the new node treats bounded complexes of finite projectives and includes tensor evaluation, biduality, and zig-zag identities; the existing node treats a single finite locally free sheaf in degree zero and only computes RHom in degree zero.
lem-pc-dualizable-evaluation-criterion vs lem-pc-perfect-rhom-tensor-comparison: the new node is the abstract closed-monoidal implication from a natural evaluation isomorphism to triangle identities, while the item is the scheme-level perfect-complex theorem whose evaluation isomorphism supplies the hypothesis.
lem-pc-rhom-strict-perfect-hom vs lem-weil-pbc-derived-exchange-triangulated: the new node states the Tag 0A8D strictly-perfect Hom-complex computation, while the existing node concerns exchange of derived functors and does not state that computation.
lem-pc-rhom-strict-perfect-hom vs lem-weil-pbc-adjunction-shift-compatibility-unique: the new node computes internal Hom from a strictly perfect complex, while the existing node proves uniqueness and shift compatibility for an adjunction morphism.
lem-pc-rhom-strict-perfect-hom vs lem-weil-pbc-derived-adjunction-commshift: the new node computes internal Hom from a strictly perfect complex, while the existing node concerns commutation of a derived adjunction with shifts.

The source declaration search found no sorry-free declaration tagged `lem-pc-perfect-rhom-tensor-comparison` in the project source. The existing node `lem-pc-perfect-tensor-hom-duality` depends on this item and therefore was not used as a citation. The new nodes are strictly smaller: the bounded finite-projective calculation and the general derived tensor-internal-Hom adjunction, rather than the global scheme statement. The superficially similar `prop-sf-dualizable` and `prop-sf-dualizable-hom` concern the different category D^b_ctf(X,Lambda_X) of constructible Lambda_X-modules from `def-sf-datum`, with M restricted to D^b_ctf; they are neither this item nor special cases of it.

## Second reading by H1

Step 1 was checked against Stacks Tag 08DQ (cohomology-lemma-dual-perfect-complex) and Tag 0FPC (cohomology-example-dual-derived): the affine representative, degreewise tensor-Hom map, bidual map, and zig-zag maps are now stated explicitly; verdict pass.
Step 2 was checked against the restriction argument in Tag 08DQ, the tensor-Hom adjunction of Tag 08DJ, and the canonical-map construction in Tag 0FPC: the adjunction is available for every object of D(O_X), so the criterion applies globally and supplies both triangle identities; verdict pass.
Step 3 was checked against Tag 0GM7 (cohomology-lemma-pullback-internal-hom, case (1)), Tag 08DM (cohomology-lemma-RHom-strictly-perfect), Tag 08DJ (the derived adjunction), and Tag 09UA (cohomology-lemma-perfect-pullback): termwise pullback preserves the finite-projective calculation, and the explicitly defined adjoint is the canonical base-change map; verdict pass.
Step 4 was checked against the construction of the canonical map in Tag 0GM7: it identifies the pulled-back evaluation map, and its elementary status is justified by the preceding degreewise calculation; verdict pass.
The auxiliary nodes were checked as statement-only, self-contained assertions: the bounded-complex node introduces R, P, M, the dual differential, evaluation, bidual, and zig-zags; the adjunction node introduces arbitrary A, I, E in D(O_X) and the adjoint correspondence. Their zero-complex, one-term finite-free, and one-point scheme cases reduce to the zero, ordinary module tensor-Hom, and ordinary derived adjunction identities. The Mathlib searches were checked in `searches.jsonl`; no exact declaration was found.

Changes made: corrected the strictly-perfect source from Tag 0A8D to Tag 08DM; added the missing Tag 08DJ derived tensor-internal-Hom adjunction node; explicitly defined the global evaluation, bidual, and base-change maps as adjoints; expanded all four proof steps to require the evaluation isomorphism for every object of D(O_X); retained the existing non-duplicate distinctions and updated citation quotes.

Second-reading repair: made the auxiliary node self-contained by stating the dual and internal-Hom differentials explicitly; this removes the otherwise ambiguous phrase “usual dual differential.” The item node’s `created` metadata is inherited from the base and was left unchanged as a maintainer-owned field.

Second-reading repair: specialized the dualizability criterion from an undefined generic closed monoidal category to the explicitly defined category D(O_X), and added its tensor and internal-Hom definition dependencies; updated the corresponding citation quote.

New node `lem-pc-affine-perfect-complex-duality`: checked against Tags 08DQ and 0FPC and the displayed cochain formulas; verdict pass.
New node `lem-pc-derived-tensor-internal-hom-adjunction`: checked against Tag 08DJ's canonical derived adjunction; verdict pass.
New node `lem-pc-dualizable-evaluation-criterion`: checked against Tag 0FPC and the explicit D(O_X) tensor/internal-Hom definitions; verdict pass after specialization.
New node `lem-pc-rhom-strict-perfect-hom`: checked against Tag 08DM's strictly-perfect Hom-complex statement; verdict pass.

## Review by H1

I read the imported item and the Stacks sources named in Tags 08DQ, 0FPC, 0GM7, 09UA, 08DM, and 08DJ. Step 1 now explicitly cites the affine bounded finite-projective representative theorem, perfectness definition, affine QC derived equivalence, K-flatness, and the 08DM Hom-complex bridge before applying the auxiliary calculation; its arbitrary-complex clause supplies the every-object hypothesis. Step 2 cites restriction of internal Hom and the new 08DJ adjunction node, then uses the closed symmetric-monoidal criterion for the global zig-zags. Step 3 cites termwise derived pullback, restriction, the 08DM bridge, and the auxiliary calculation; the base-change map is the adjoint explicitly defined in the statement. Step 4 cites the tensor-complex calculation and the adjunction definition.

I checked every cited node's statement directly and copied the relevant clauses into `citations.json`. The two new statement-only nodes are self-contained and carry blueprint ancestry plus all required Mathlib searches. I tested the auxiliary statement on the zero complex and one-term finite free complex. The repaired proof specifically addresses the return: the global triangle identities follow from the natural evaluation isomorphism and the criterion, rather than a false locality claim. The item statement dependencies now include the internal-Hom and tensor definitions.
