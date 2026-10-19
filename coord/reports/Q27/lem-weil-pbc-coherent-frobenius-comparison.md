# Q27 stage-1 delivery: lem-weil-pbc-coherent-frobenius-comparison

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-coherent-frobenius-comparison.json — statement, split; no Mathlib match after semantic searches, a second semantic phrasing, Loogle and source grep.
- citations.json — verbatim statement quotations for every step citation.

0 new nodes; 0 Mathlib leaves. No Lean files or unit records changed. The sandbox originally contained only dispatcher marker files, so I copied the current item from the shared repository and retained its inherited proof, provenance, searches and protected metadata. The rewritten argument uses existing DAG results throughout.

## Attachments

None. Source searches under /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the blueprint id, coherent_frobenius_comparison, structureCoherentFrobenius, and the relevant Frobenius/coherent terminology found no declaration giving the item. The existing node's stage-2 statement record is not a finished project proof in that source checkout.

## WANTED

None. All documents used here are available locally.

## Findings and corrections

The mathematical statement is unchanged. The inherited proof already supplied a common Cech calculation, but its long Step 5 hid the compatibility between module pullback, underlying abelian pullback and the specific Ext base-change map. I replaced that identification with the existing ringed-site refinement square (new Step 5) and the existing coefficient factorization, resolution naturality, resolution edge, normalization and coefficient transport statements (new Step 6). These are generic results with their own hypotheses, not new versions of clauses of the item. Added proper base-change explicitly in Step 1 and the fixed resolution normalization in Step 2. The previous Step 5 is now discharged by cited generic lemmas rather than asserted inline. Every final step is shorter than 2000 characters.

The item uses canonical additive maps. In particular, Frobenius is not claimed to be O-linear, inverse image of the additive structure sheaf is not identified with the structure sheaf of the base change, and the flat base-change map is the specified linear extension of the structural h-map. Retained the item statement's explicit canonical characterization; the existence-only quasi-coherent comparison theorem alone would not establish it.

The current blueprint proof is literature/blueprint/main-20261015/blueprint/sec-curve-estimates/sk-lem-curve-normalization/lemma-weil-pbc-smooth-curve-artin-schreier.proof.md, final paragraph. Its coherent-base-change/Frobenius assertion is exactly the place served by this child. Searched the whole blueprint using blueprint_refs.py for Frobenius and coherent cohomology; the curve assertion and generic flat-comparison nodes do not provide the full item. No same_as was found. No chapter, unit, target statement, or coefficient route is changed.

## Not duplicates

No new nodes are created. The general ringed-site refinement result and the fixed-resolution coefficient and edge results already exist and are cited in place of creating comparison lemmas.

## Review by Q27

I read Stacks etale-cohomology.tex, Tag 0A3P (lemma-finiteness-proper-variety-char-p-p), including its appeal to coherent comparison and flat base change; Tag 03P2 (theorem-zariski-fpqc-quasi-coherent), including its affine and separated Cech proof; coherent.tex, Tag 02KH (lemma-flat-base-change-cohomology), especially the canonical map and separated finite-affine-cover calculation; sites-cohomology.tex, Tags 03AX (lemma-cech-cohomology), 03AZ (lemma-cech-spectral-sequence), 03F7 (lemma-cech-spectral-sequence-application), 03FD (lemma-cohomology-modules-abelian-agree), and 03F3 (lemma-cohomology-of-open); and cohomology.tex, Tags 01F8/01F9/01FA/01FB and 01FD (lemma-functoriality-cech). The naturality and explicit normalization details are an agent-written elaboration, so proof_origin.by remains agent. There are no new nodes whose sources need a separate review.

For Step 1, I opened the statements for properness, finite type, proper base change, separated affine intersections, affine-triple tensor base change, quasi-coherence and affine vanishing, both open-restriction-injective lemmas, the module/abelian comparison and the positive etale object-cohomology lemma. Properness gives precisely separatedness and finite type; the last gives a finite affine cover over the affine field spectrum. Each tuple, including repeated indices, is affine. The tensor theorem is applied with identity arrow on each affine and R=k, A=K, B=C its section ring. The two open-restriction statements explicitly preserve injective resolutions, so scheme cohomology vanishing is genuinely the ambient object vanishing required by the edge theorem. Proper base change justifies using the proper-scheme canonical comparison on X_K. The sites are taken small in a common universe before invoking small-site results.

For Step 2, the inclusion-of-sites lemma explicitly supplies continuity, final objects, fibre products and the site morphism; associated etale modules and tensor pullback give the same section complex. The acyclic-edge statement actually states both the change-of-site square and the module-forgetting square, with their augmentations fixed. The resolution-normalization statement identifies the fixed Ext equivalence on the same injective resolution, so the comparison is the one specified in def-pbc-canonical-coherent-etale-comparison. This does not use a merely existential choice of comparison.

For Step 3, the additive naturality clause of the edge theorem applies to Frobenius; the module coefficient-naturality statement applies only to multiplication by a scalar. The elementary binomial calculation gives additivity and p-semilinearity on the section complex, hence on its cycles and boundaries. I checked the sign identity also for p=2 and the zero section ring. The equality follows using Step 2's two specified edge identities, without treating Frobenius as a module morphism.

For Step 4, I opened the finite-limits, continuity, algebraic-structures inverse-image and cohomology-pullback statements. They supply the exact base-change functor, its adjunction unit on abelian sheaves and compatibility with the set-theoretic inverse image. The edge lemma then gives the claimed formula for the actual unit-and-coefficient pullback because the adjoint coefficient map is structural pullback of sections. The target cover and tuple vanishing were checked in Step 1.

For Step 5, the existing ringed-site refinement-square statement gives its sectionwise formula and the precise module-resolution definition of its cohomology map. Its enough-injectives assumption is supplied by the scheme-modules-enough-injectives statement on each scheme. Set the index map and all tuple refinement maps to identities. The structural coefficient map is O_X-linear with target action through the structural ring map, as required. This explicitly computes j_mod, rather than assuming a compatibility between a module map and an abelian map.

For Step 6, I opened the coefficient-factor, coefficient-transport, resolution-naturality, resolution-edge and normalization statements and checked their domains: the first factors a general module h-map through the direct-image edge; the next transports precisely such a factorization; the other statements concern the specifically constructed E, not an unspecified natural family. Their specialization to the structural coefficient map gives the additive Ext map in the flat-comparison definition. Tensor pullback of the unit module is explicitly identified by the two inverse formulas, so no noncanonical coefficient choice enters. This repairs the hidden comparison in the inherited long step using existing strictly more general tools.

For Step 7, the separated flat-cohomology statement gives bijectivity of this specific beta, under flatness, compactness, separatedness and quasi-coherence. The field-extension basis argument proves flatness; compactness is quasi-compactness here and follows from finite type over the field. Module edge naturality on scalar multiplication proves K-linearity. Substituting the actual section formulas from Steps 4–6 proves the displayed pullback equality for all classes since the edges are onto.

For Step 8, there are no new black-box facts: the ring homomorphism identity (j#(z)a)^p=j#(z^p)a^p, together with Steps 3 and 7, gives the last equality on every cycle representative. Balancing scalars gives the same lambda^p a^p on both tensor presentations. I checked degree zero (ordinary regular functions), the empty scheme (zero complexes and groups), identity extension, p=2, positive degrees with zero cohomology, and imperfect extensions. None needs perfection, algebraic closure, smoothness, connectedness, a dimension bound, or finite-dimensional coherent cohomology.

I checked delivery-errors B–E against the final files. No new statement-only-node, source-tag, duplicate, Mathlib-leaf or clause-renaming issue arises because no nodes are added. All cited node statements were opened, and citations.json records their verbatim statements, including all clauses used. proof_deps is exactly the union of uses. General tools from other units are declared in split_report.tool_uses; they implement the common-Cech route and do not replace the unit's curve calculation. The required server dry run is the remaining mechanical validation before pushing.

## Unfinished work

No mathematical subclaim is left without a cited node or an explicit elementary calculation. The existing cited generic nodes remain their own stage-1 items; this delivery splits only the assigned item.
