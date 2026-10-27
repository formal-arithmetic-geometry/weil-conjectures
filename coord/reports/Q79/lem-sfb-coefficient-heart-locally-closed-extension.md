# Q79: lem-sfb-coefficient-heart-locally-closed-extension

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-coefficient-heart-locally-closed-extension.json: existing statement item, now split into seven steps; no whole-item Mathlib match. Original statement, source, creation attribution and inherited searches retained. Removed the unused bundled pushforward/pullback statement dependency and added the actual geometric definition dependencies.
- citations.json: one verbatim statement quotation for each node used by each numbered proof step.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No unit realization fields changed: this item is not the unit's key node.

## Attachments

None. I searched lean/WeilConjectures for the item's blueprint tag and for exact lower-shriek/locally-closed extension terminology, and read the internal-module LowerShriek/Defs and OpenClosed context. The exact open-extension instances there give only one factor. They do not state the Noetherian subscheme assertions, closure factorization, exact actual closed coefficient direct image, and derived comparison of this item together. The local Sheaf/Paper/CoefficientHeartFiltration definition coefficientHeartLocallyClosedExtension fixes the actual canonical closure construction, but is not a proof of this statement. No attachment claimed.

## WANTED

None. The current blueprint and all Stacks passages used are present locally.

## Corrections and scope

The item had no proof. Its statement is mathematically sound and is unchanged. The coefficient-system isomorphism is available for arbitrary condensed rings from sk-def-sfb-coefficient-morphisms; I deliberately did not use only the admissible-coefficient statement of sk-prop-sfb-cartesian-coefficients. Likewise, lem-exc-proetale-closed-exact states finite constant coefficients only and is not a sufficient citation here. Instead step 4 uses lem-sfb-proetale-identified-open-closed, whose statement permits arbitrary ring sheaves with specified inverse-image identifications. The comparison with internal module objects is written explicitly, rather than identifying the two coefficient categories silently.

The proof follows the introductory closure/extension paragraph of the current coefficient-heart unit, supplying its scheme and homological prerequisites. The source field's reference to a retained proof step 1 is inherited provenance, not a claim that the present blueprint's step 1 itself proves the Noetherian geometry. The assembled proof is marked agent-written.

## Searches and existing-node reuse

All five searches made in this session are recorded verbatim in searches.jsonl and appended to the item's mathlib_searches. I read their returned names and types. The two semantic phrasings find exact-functor derived descent, already represented by lem-weil-pbc-exact-functor-derived-factorization, but no theorem covering the whole item. LeanSearch finds ordinary CondensedMod results over an external ring, which do not give these internal coefficient modules on a scheme. Loogle finds mapDerivedCategory, and the source grep finds Noetherian-space results. These are component results, not whole-item matches.

Before writing, I searched the whole DAG by 09BM and 03DJ, by closure/image, Noetherian subscheme, exact cohomology and derived-factorization concepts, and searched the whole blueprint using blueprint_refs.py for locally closed, locally closed coefficient, 09BM, closed immersion exact and immersion open. I read the existing statements and reused them; no new node is needed. The canonical image result is the existing Mathlib leaf lemma-nagata-immersion-open-in-scheme-image. I also checked that the coefficient and exactness tools do not depend back on this item.

## Not duplicates

No new nodes. In particular I did not recreate the closure-factorization theorem, general exact-functor cohomology/descent, or the existing open/closed ringed-site exactness theorem. The neighboring lem-sfb-proetale-locally-closed-extension is an existential extension result with specified pullbacks, not this package about the actual canonical closure functor; it is not used to replace the item's argument.

## Review by Q79

I read the current main-20261015 coefficient-heart unit and its proof, and the chapter's distinction between fixed abelian coefficients and modules over the pulled-back condensed ring. For the geometry I read properties.tex lemma-locally-Noetherian (01OW), lemma-locally-Noetherian-quasi-separated (01OY), lemma-Noetherian-topology (01OZ), and morphisms.tex lemma-finite-type-noetherian (01T6), together with the quasi-compact scheme-theoretic image passage (01R8). For exactness I read proetale.tex lemma-closed-immersion-complement-retrocompact-exact (09BM) and sites-modules.tex lemma-extension-by-zero-exact (03DJ). For passage to complexes I read homology.tex lemma-exact-functor (010N) and derived.tex lemma-right-derived-exact-functor (015F), including its unbounded clause; its omitted cohomological reasoning is supplied by the existing exact-functor cohomology leaf and written out in step 6. There are no new nodes requiring further source review.

Step 1 uses the open-Noetherian leaf for V, the closed-immersion-proper leaf specifically for finite type, and the finite-type-over-Noetherian leaf for closed subschemes of V. Those statements really give those hypotheses and conclusions, so no separatedness of X over a base is assumed. The minimal-closed-subset and compact-subsets leaves give the Noetherian topology and compactness of every open preimage; the locally-Noetherian-quasi-separated leaf gives quasi-separatedness of each subscheme. A locally closed subscheme is treated by its defining closed-into-open factorization, not by an unjustified set-theoretic factorization.

Step 2 checks quasi-compactness of a and its diagonal from compactness of every subset of S. This uses the diagonal definition in def-weil-quasi-separated-morphism, not a false inference from quasi-compactness of the underlying space alone in a general scheme. The image leaf specifically requires a quasi-compact immersion and explicitly says the canonical factor is open and dense. Both hypotheses have been established. The image/factor/closure definitions provide the closed inclusion and its composite equality. Dense image inside that closed subset gives exactly the topological closure; no assertion is made about arbitrary non-quasi-compact scheme images.

Step 3 uses sk-def-sfb-sheaf-tensor for the monoidal sheafification and the essentially small site convention needed by the internal-to-sectionwise module equivalence. That equivalence explicitly leaves carrier sheaves and section maps unchanged. The module-sheaf category node explicitly asserts abelianness in the chosen universe. Finally sk-def-sfb-coefficient-morphisms gives a ring-object isomorphism alpha and its mate eta for any condensed ring, not just the finite and field cases of a narrower neighboring proposition.

Step 4 applies lem-sfb-proetale-identified-open-closed only after checking the complementary open is quasi-compact. I opened its statement: it says that actual direct image preserves finite limits and finite colimits for arbitrary ring sheaves with the specified coefficient identifications. The lower-star definition gives the actual internal action via eta and the lax monoidal product. The displayed section product verifies that it is the same action as the ringed-site direct image under the equivalence, on both objects and morphisms. Consequently the transfer of exactness follows by the elementary universal properties of cones through an equivalence. This short comparison is not a new black-box identification. The off-unit identified-open-closed lemma is declared in split_report.tool_uses as a generic ringed-site tool, retaining the coefficient-heart closure route.

Step 5 cites the open coefficient-extension definition for its explicitly stated additivity and exactness, and the locally-closed coefficient-extension definition for its exact actual composite and canonical factorization. I read both statements; no existential substitute extension is used. Preservation of a finite cone or cocone under two consecutive preserving functors proves exactness of the composite directly.

Step 6 cites the exact-functor-complex-cohomology leaf, whose statement includes naturality in K and all integer degrees. Naturality is used explicitly on a quasi-isomorphism v to identify its cohomology map with the functor applied to an isomorphism. There is no hidden boundedness or injective-resolution hypothesis. Step 7 cites the exact-functor-derived-factorization leaf, whose statement supplies the actual localization comparison and unbounded functor. I checked the displayed comparison has source D(a_!)(Q_S K) and target Q_X(C(a_!)K); the item's notation uses diagrammatic composition. This prevents reversing Q_S and Q_X.

Small cases checked: S empty, X empty, the identity immersion, a closed immersion (u identity), an open immersion whose scheme-theoretic closure can be nonreduced, the zero coefficient ring, zero complexes, and unbounded complexes. No reducedness, nonemptiness, field, invertibility of a prime, or boundedness enters the proof. The closure is the scheme-theoretic image, never an arbitrarily reduced closed subscheme. All seven steps have fewer than 2000 characters. The inline scalar-action comparison is a direct evaluation of the two cited definitions, not a separate non-elementary lemma hidden in a long step.

Against delivery-errors B--E: no new statements or duplicate nodes; notions have their actual definition dependencies; sources identify Stacks tags and labels; no unrun searches recorded; citations.json uses verbatim node statements; no fact is taken from the proof of a cited node; all non-elementary tools are cited; the graph's no-cycle requirement is left to the required server checks as well as the local reverse-dependency inspection; the steps carry the argument rather than moving clauses into new nodes. The statement was neither weakened nor repaired, and no source dispute was found.

## Unfinished work

None in the one-level stage-1 split. Dependencies remain the existing DAG work items; this delivery does not claim their proofs finished.
