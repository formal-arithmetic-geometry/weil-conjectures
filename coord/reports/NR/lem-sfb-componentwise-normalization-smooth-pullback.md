# Stage-1 delivery: lem-sfb-componentwise-normalization-smooth-pullback

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-componentwise-normalization-smooth-pullback.json: statement, split; no exact Mathlib match. The existing statement is unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-normal-ascent.json: new statement-only unsplit node; no Mathlib match after semantic searches in two phrasings, Loogle, LeanSearch and source grep.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-normal-generic-recognition.json: new statement-only unsplit node; no Mathlib match after semantic searches in two phrasings, Loogle, LeanSearch and source grep.
- citations.json: literal statement quotations for all 14 step/node citations.

Two new nodes, zero Mathlib leaves. The statement-only nodes have empty proof and proof_deps and null proof_origin.

## Attachments

None. Searched lean/WeilConjectures for the item tag, componentwise normalization and normalization under smooth pullback. The relative normalization comparisons in WeilConjectures/Mathlib/AlgebraicGeometry/Normalization.lean and the stalk-normalization modules concern a supplied morphism, not the absolute componentwise normalization in this item. SmoothConnectedGenericGeometry.lean treats a geometrically connected family over a normal integral base, which is insufficient for our arbitrary, possibly disconnected family. No finished project declaration stating the item was found.

## WANTED

None. All mathematical sources used here are in literature/stacks-project/.

## What needed repair

There was no earlier sandbox split or report. I copied the current unsplit item, retained all its statement, provenance and earlier searches, and added a six-step proof. The imported source is Stacks 07TD, which really covers smooth morphisms and nonreduced schemes. The componentwise definition agrees with its normalization by 0CDV. I read the chapter and inherited unit; this item is a generic scheme-theoretic prerequisite below the alteration route, and changes neither that route nor any unit statement.

A tempting shortcut through clause (3) of lem-per-componentwise-normalization-properties would require the pullback P to be locally Noetherian. Normalization need not be finite here, and I do not assert that either Y^nu or P is locally Noetherian. The new recognition node removes precisely that unsupported hypothesis. It does not restate smooth pullback: it concerns an arbitrary supplied integral normal scheme with matching generic points and residue fields, and contains no smooth morphism or fibre product.

The Mathlib hit AlgebraicGeometry.Scheme.Hom.instIsIsoNormalizationPullbackOfSmooth was checked against Mathlib/AlgebraicGeometry/Normalization.lean:588-611. Its source is the relative normalization of a supplied qcqs map. Converting it to the componentwise normalization is an additional theorem, so it is not a one-line match for this item. Its integral-morphism toNormalization instance also concerns a different object from absolute normalization recognition. The normal-ascent searches returned smoothness definitions, stability under base change and localization results for integrally closed domains, not the scheme statement. Every recorded added search is copied from the actual searches.jsonl log; none of the services used in this attempt was unavailable. The first normal-ascent Loogle query reported an unknown identifier, which is retained explicitly in its logged result; the second semantic query and source grep supply the substantive absence check.

## Not duplicates

lem-sfb-smooth-normal-ascent vs lem-sbc-finite-etale-generic-fibre-hom-extension-existence: the existing node extends generic-fibre maps between finite etale covers and requires a normal integral base and geometrically connected fibres; the new node asserts only normality ascent for arbitrary smooth morphisms.
lem-sfb-smooth-normal-ascent vs lem-sbc-smooth-connected-generic-geometry: the existing node requires an integral normal base and nonempty geometrically connected fibres and also identifies generic stalks; it does not cover arbitrary disconnected smooth schemes over a disconnected normal base.
lem-sfb-smooth-normal-ascent vs lem-sbc-smooth-connected-generic-geometry-core: this core still requires an integral normal base and nonempty geometrically connected fibres, neither of which is imposed in normal ascent.
lem-sfb-smooth-normal-ascent vs lem-sc-smooth-normal: the existing node is only a smooth curve over a field, not a smooth morphism over an arbitrary normal scheme.
lem-sfb-integral-normal-generic-recognition vs lem-sbc-normal-finite-stage-universal: the existing node constructs a finite replacement of a Noetherian approximation stage, not recognition of an arbitrary integral normal source over a locally Noetherian base.
lem-sfb-integral-normal-generic-recognition vs lem-sbc-normalization-dominant-lift: the existing node lifts dominant maps between integral schemes; the new node recognizes a possibly disconnected normalization by integral and generic-field data, without requiring the normal source to be locally Noetherian.
lem-sfb-integral-normal-generic-recognition vs lem-trf-conductor-smooth-base-change: the existing node concerns the coherent conductor over finite-type Q-schemes; the new node has no conductor, characteristic, finite-type or finiteness assumption.
lem-sfb-integral-normal-generic-recognition vs lem-trf-normalized-blowup-calculus: the existing node concerns normalized blowups of finite-type Q-schemes; it does not state this recognition principle over arbitrary locally Noetherian bases.
lem-sfb-integral-normal-generic-recognition vs lem-per-componentwise-normalization-properties: clause (3) of the existing node assumes the source Z is locally Noetherian. The new node explicitly removes this hypothesis, needed since P may be non-Noetherian. Clauses (1) of the existing node are reused, not duplicated.
lem-sfb-integral-normal-generic-recognition vs lem-per-integral-etale-chart-flatification: the existing node constructs flattenings for finite families of etale charts over quasi-excellent integral Noetherian schemes; it is not a normalization recognition theorem.
lem-sfb-integral-normal-generic-recognition vs lem-per-excellent-normalized-blowup-tower: the existing node treats finite towers over an excellent integral Noetherian scheme; the new recognition statement needs no excellence, finite normalization, or blowup.
lem-sfb-integral-normal-generic-recognition vs lem-per-excellent-normalization-preparation: the existing node proves finiteness and dense-open properties over an excellent base, not recognition without a Noetherian source.
lem-sfb-integral-normal-generic-recognition vs lem-per-finite-curve-normalization-regular: the existing node assumes dimension one and finite normalization and proves regularity; the new recognition statement has none of these restrictions.
lem-sfb-integral-normal-generic-recognition vs lem-per-normal-projective-compactification: the existing node constructs a model over a mixed-characteristic trait, not recognition of an arbitrary integral normal scheme by generic-field data.
lem-sfb-integral-normal-generic-recognition vs lem-weil-pbc-reduced-normalization-over-normal-reduction: the existing node compares normalization on a normal reduced open in a finite-type field-scheme; the new node recognizes arbitrary integral normal covers.
lem-sfb-integral-normal-generic-recognition vs lem-weil-pbc-reduced-algebraic-normalization-field-change: the existing node treats finite-type reduced schemes over a field and separable scalar extension; it does not give arbitrary integral normal recognition without local Noetherianity of the source.

I also searched the whole DAG and blueprint by normality/smoothness, normalization, integral birationality and the source tags. No blueprint node states either new theorem. The nearest-blueprint-ancestor command returns None for this inherited created-node chain; I preserved the item's null from.node and used that same result for the new nodes, retaining the explicit alteration-route place and complete via chain.

## Tool uses

lem-per-componentwise-normalization-properties supplies only its clause (1): normality of Y^nu, integrality, the generic-point bijection and exact generic fibres. It is an off-unit general tool; its clause (3) is deliberately not applied. lem-pc-smooth-flat supplies flatness of f and q as a generic tool. These two uses are declared in split_report.tool_uses. The other reused external tools are already Mathlib leaves or Lean-closed (flat-going-down, integral base change, smooth base change); none changes the unit route.

## Review by NR

I read more-morphisms.tex, lemma-normalization-and-smooth (07TD), including its proof, rather than relying on its title. For the normal-ascent node I read descent.tex, lemma-normal-local-smooth (034F), especially the ascent paragraph, which has no Noetherian or connectedness assumption. For recognition I read morphisms.tex, lemma-normalization-normal (035Q) parts (3) and (4), its reductions footnote, lemma-normalization-trivial (0H7D), and lemma-normalization-in-terms-of-components (0CDV). With the generic-point bijection in the new recognition statement, only finitely many components meet the inverse image of an affine open of T: its generic points map to the finitely many generic points in that open. Normality of Z reduces its generic local rings to residue fields, so the residue-field isomorphisms are the birationality-on-reductions condition of 035Q(3). The normalization of Z is trivial by 0H7D; uniqueness follows from 035Q(4). This verifies the new statement without assuming its source is Noetherian.

In step 1 I reopened the exact statements of def-pc-fibre-product, lem-per-componentwise-normalization-properties and lem-sbc-integral-morphism-base-change. Clause (1) of normalization-properties states all four facts taken from it, including the scheme-theoretic generic fibre isomorphism, and the base-change node states integrality for arbitrary base change. Only Y, which is locally Noetherian in the item, is passed to normalization-properties.

In step 2 I read the statement of lem-pc-proper-base-change: its clause (2), despite the title, states smooth base change for arbitrary schemes. The new 034F node gives normality of P because Y^nu is normal. The exact statement of lem-pc-smooth-flat then supplies flatness of both f and q. Neither of these nodes needs finite normalization or a Noetherian base. Thus normality and flatness of P are justified by actual cited statements.

In step 3 the definition of flat morphism explicitly gives flat maps of local rings. The cited lem-sc-flat-going-down is the ring-map going-down theorem: applied to the local ring at a generic source point, its sole prime makes a strict generalization of the target point impossible. The statement of normalization-properties explicitly gives that generic points of Y^nu map to generic points of Y. This is a short consequence of cited results, written out, not a separate new generic-point node. I checked the algebra.tex going-down proof (00HS).

In step 4 the fibre product definition gives associativity of the displayed base changes, and normalization-properties gives the exact generic fibre being pulled back. Further pullback to Spec kappa(xi) really has one point and unchanged residue field. I wrote both directions of the generic-point correspondence: a lift of generic xi has no strict generalization; conversely a generic z lies over a generic base eta, and any strict generalization of p(z) in X would remain in that same generic fibre and lift under its isomorphism. The elementary affine description is valid even for nonreduced rings: primes of B tensor_A kappa(p) are the primes of B contracting to p, with the same inclusion relation. This step does not assume that a smooth fibre is zero-dimensional or connected.

Step 5 checks all four hypotheses of the new recognition statement individually before applying it. Inversion gives exactly the orientation and uniqueness of the isomorphism requested by the item. Step 6 quotes the explicit etale-is-smooth-of-relative-dimension-zero clause of def-sbc-smooth-morphisms. Each cited statement is copied verbatim into citations.json, making the claimed interfaces inspectable.

I tested the statements and proof on the empty scheme (vacuous generic conditions), an identity map of Spec k[epsilon]/(epsilon^2) (both normalizations Spec k), affine space over that nonreduced point (pullback kills epsilon and gives the usual normal affine space), disconnected smooth schemes over a field (components are all retained), and a reduced node (the normalization has two generic branches). Recognition needs the stated bijection and field isomorphisms: an extra normal vertical component or a nontrivial field extension fails those hypotheses, as it should. Smooth normal ascent allows a disconnected or empty source and does not infer integrality or connectedness. There is no use of excellence, finite normalization, a dense open normal locus, or the existence of such an open without finiteness. Every step is below 2000 characters; no long step hides a comparison lemma. The new nodes are generic tools strictly smaller than the smooth-pullback item and are left statement-only. No source dispute was found and no statement was weakened.

## Unfinished work

None in this one-level split. The two new unsplit nodes intentionally join the stage-1 queue for their own later splits.
