# Stage-1 report: lem-weil-pbc-site-derived-tensor-descent

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-site-derived-tensor-descent.json: existing statement, split; no Mathlib match for the entire item.
- citations.json: a verbatim statement quotation for every citation in each of the six steps.

No new nodes and no new Mathlib leaves. write_split.py is a sandbox-only preparation script; searches.jsonl is the search command's actual log.

## Attachments

None for the item. The project already records CochainComplex.mappingCone.quasiIso_iff_acyclic as belonging to lem-pur-quasi-iso-cone-acyclic, with closed slopmaster2 audit. I reuse that node without changing it.

## Wanted sources

None. The Stacks sources used are available locally.

## Problems and corrections

The item's imported source list included 0G7D, but that factorization lemma is not needed for the chosen argument: right Ore/cancellation and roofs can be refined by the already existing 06YS resolution node. I preserve the statement, including flat terms, arbitrary sites, the bifunctor and extension of arbitrary natural transformations. I do not replace arbitrary ring sheaves by constant coefficients or identify these categories with master condensed-ring module objects. No target statement or master base-change morphism is changed.

The existing lem-pc-kflat-bifunctor-iso-descent states only a scheme result and only natural isomorphisms, whereas this item allows arbitrary ringed sites and arbitrary natural transformations. The existing lem-pc-kflat-tensor-product is for ringed spaces, and lem-pc-kflat-tensor-quasi-iso is for a ring on the one-point site. Their proofs cannot be used as unstated extensions to arbitrary sites. The new split proves the needed tensor invariance directly from K-flatness and the generic cone criterion, and derives the descent from the generic localization universal-property node. Therefore no generalized duplicate nodes were created.

The proof_origin is agent: the explicit roof refinement and repeated full-faithfulness argument are written here, guided by the actual sources; I do not claim that the source explicitly states the whole bifunctor/natural-transformation theorem. One initial source tag typo for K-flat tensor preservation was corrected from 06YQ to 06YP by the tag-to-label table before dry run.

## Unfinished work

No unfinished part of this split. The reused resolution theorem remains a dependency to be handled by its own worker. There is no claim that the target-level condensed coefficient bridge has been settled.

## Not duplicates

No new nodes. Whole-DAG and blueprint searches for K-flat, derived tensor and localization found no imported blueprint node stating the whole item. Existing scheme-only and ring-only statements were read and kept distinct as described above.

## Review by NI

I read sites-cohomology.tex at lemma-K-flat-resolution (06YS), lemma-derived-tor-exact (06YM), lemma-K-flat-quasi-isomorphism (06YP), the construction before definition-derived-tor (06YU), and lemma-factor-through-K-flat (0G7D), including its flat-term clause. I read derived.tex lemma-acyclic (05RT) and categories.tex lemma-morphisms-right-localization (04VI), lemma-equality-morphisms-right-localization (04VJ), and lemma-properties-right-localization (04VK). I also read the four-corners blueprint source and its current node, the parent tensor-pullback split, and the unit/chapter route. This is a generic foundational tool for that comparison, with no change to the geometric unit's steps.

For Step 1 I checked that def-weil-sheaf-of-modules-category actually asserts the abelian property under the item's smallness convention. lem-pc-kflat-resolution really supplies both K-flatness and flat terms on any ringed site, not just a ringed space. lem-pc-quasi-isomorphisms-multiplicative-system really gives both calculi of fractions in an arbitrary abelian homotopy category. Ore and cancellation witnesses need only precomposition with a resolution, so their equations survive in the full subcategory. Composites of quasi-isomorphisms remain such because the induced cohomology maps are composites of isomorphisms.

For Step 2 I read the full statements of the right-fraction representation and common-refinement nodes. The first gives a roof for an arbitrary derived morphism; the second explicitly gives equal denominators and equal numerator composites, exactly what faithfulness uses. I resolve the witness vertex instead of assuming it was already K-flat. The localization node supplies the induced functor. Fullness, faithfulness, and essential surjectivity are proved separately; no K-flat complex is assumed projective or assumed to lift a chain map through an arbitrary resolution.

For Step 3 the tensor-complex definition supplies the direct-sum totalization and its sign (-1)^p. I wrote both homotopies: h tensor 1 in the first variable, and (-1)^p times 1 tensor k in the second. Substitution in dH+Hd cancels the mixed differential terms. This is the elementary calculation underlying 06YM and provides the needed homotopy-category naturality.

For Step 4 the cone criterion states quasi-isomorphism iff cone acyclic for all complexes of any abelian category. The K-flat definition states precisely that tensoring an acyclic test complex with a K-flat one gives an acyclic total tensor. I compared the cone/tensor shifted summands and signs, then used the signed balanced swap to reverse the factors. The tensor and derived-category definitions supply the formulas used here. This uses only the flatness property of the held-fixed complex, not termwise flatness of an arbitrary tensor input and not a claim that tensor is exact on all complexes. The generic cone node is already Lean-closed; no new node was necessary.

For Step 5 the localization universal-property statement supplies factorization into any target category, lifting of natural transformations, and uniqueness respecting composition. This applies to the functor categories used in currying. Objectwise invertibility makes the denominator images natural isomorphisms. Essential surjectivity from Step 2 carries second-variable invertibility from the resolving objects to all objects. The natural comparison is the inverse of the factorization comparison, hence is in the direction stated in the item. Multiplying the naturality equation by inverses explicitly checks quasi-isomorphism inversion compatibility.

For Step 6 the same node supplies unique extensions of natural transformations, not just isomorphisms. Uniqueness in the first variable verifies the second-variable naturality squares; uniqueness in the second gives a simultaneous extension. I checked that the target category E is arbitrary and no abelian or additive structure on E is used. Universe choices remain those of the statement and its existing derived-category definition.

I checked the zero complex, a one-object site over a field, the zero ring sheaf, and unbounded complexes: the Ore/refinement argument still applies, zero tensors and their comparisons are zero, and direct sums rather than products are used in every degree. Over Z, a non-flat complex Z/2 in degree zero is not treated as a member of the resolving class; its flat K-flat resolution gives the intended derived tensor and detects Tor. Thus the argument does not mistakenly descend ordinary tensor on all complexes. There are no new statements requiring a separate small-case check. citations.json was generated from the exact opened node statements, with each use checked above.

The Mathlib searches were repeated only through msearch.py: two semantic phrasings, Loogle KFlat, grep in CategoryTheory, and LeanSearch. I read the returned hits and the Tor source: those are projective-resolution homology functors, not this unbounded site theorem. LeanSearch returned Internal Server Error and is recorded unavailable. Project-source searches by the blueprint tag and K-flat/tensor concepts, followed by reading the general monoidal instance and derivability files, supplied no declaration giving all clauses under just the item's hypotheses; hence this is not an attachment.

## Second reading by NI

- Step 1 checked against Tags 06YS and the abelian/module-category and multiplicative-system nodes: the ringed-site and smallness hypotheses, K-flat flat-term resolutions, and restricted Ore/cancellation argument are all present; verdict: sound.
- Step 2 checked against Tags 06YS, 06YU, 04VI, 04VJ, and 04VK and the quoted fraction/refinement statements: roofs, common refinements, and essential surjectivity are used exactly as stated; verdict: sound.
- Step 3 checked against the total-tensor definition and Tag 06YM: both explicit chain homotopies and their signs are supplied, so descent to homotopy categories is justified; verdict: sound and elementary.
- Step 4 checked against Tags 05RT and 06YP plus the K-flat and cone definitions: the cone identification, acyclicity argument, and signed symmetry cover both variables without extra boundedness; verdict: sound.
- Step 5 checked against Tag 06YU and the localization universal-property node: currying, two successive localizations, comparison direction, and inversion compatibility are explicitly handled; verdict: sound.
- Step 6 checked against Tag 04VK and the same universal-property statement: arbitrary natural transformations extend and uniqueness proves both naturality and uniqueness; verdict: sound.
- No new nodes were introduced; therefore B1--B7 and duplicate-node checks were vacuous. Existing dependency statements and every citation quote were checked against their node files and citations.json.

Changes made during second reading: none. The split already had the correct source hypotheses, explicit proof steps, exact citation quotations, and recorded Mathlib searches; the dry-run delivery preflight passed.
