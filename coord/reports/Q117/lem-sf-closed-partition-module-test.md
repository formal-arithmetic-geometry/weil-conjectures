# Stage-1 report: lem-sf-closed-partition-module-test

1. Files written:
   - dag/nodes/sec-smooth-purity/lem-sf-closed-partition-module-test.json: item, statement unchanged, split into four steps.
   - dag/nodes/sec-smooth-purity/lem-sf-immersion-composition.json: statement, Mathlib leaf. AlgebraicGeometry.IsImmersion.comp, Mathlib/AlgebraicGeometry/Morphisms/Immersion.lean:146-148. The definition agrees with the item's closed-then-open convention by isImmersion_iff_exists:155-158.
   - citations.json: eleven verbatim statement quotations for the eleven step/node pairs.
2. Attachments: none. I searched WeilConjectures for the blueprint tag, closed-partition terms and stratification, and read ConstructibleSheaf.lean and ModuleObject/LowerShriek/Constructible.lean. The latter proves extension by zero for module objects with a different coefficient setup; it does not state this item, which also retains the prescribed closed-side stratum schemes and canonical module comparisons. The existing pro-etale constructibility predicates and isomorphism invariance cover only part of the item.
3. WANTED: none.
4. Defects repaired: the item had a statement and searches but no proof. No statement change or dispute was necessary. The existing etale inverse-image-composition-module-linear theorem is not applicable on pro-etale sites; I instead used lem-pur-proetale-module-pullback-composition, which states exactly the comparison for the actual pro-etale module inverse images and their canonical constant-section coefficient maps. A naked citation to 02V0 would conceal a non-elementary fact; the general immersion-composition fact is now the single Mathlib leaf. I avoided creating topology, partition, zero-sheaf, or constructibility-test nodes, since existing statements and short definition checks suffice.
5. Unfinished mathematics: none. The new node is a searched Mathlib leaf with empty proof and proof dependencies, as required. No Lean was written and no compiler was run.

## Searches and source route

I read GOAL.md, the worker and stage-1 briefs, the three levels in SETUP.md, the chapter and unit records, the current parent split, and the current blueprint finite-stage proof at literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sf-localization/prop-sf-open-closed-triangle-all-stages.proof.md. The unit is the open-closed triangle; this item supplies only its closed-side finite constructibility partition argument. Its old detailed proof was retained in the item's source/blueprint ancestry. The blueprint's finite-stage paragraph motivates the restrictions; the explicit assembly here is marked agent-written, and no SGA source is used.

I searched the entire DAG for immersion composition, the 02V0 tag and the relevant keywords, and ran blueprint_refs.py ancestor and searches for stratification, inverse-image, Noetherian topology, composition of immersions, closed partition, ambient partition and 02V0. The returned general scalar-six-pullback blueprint theorem does not assert scheme immersion composition. The closed-partition hit fin4-lem-stalk-constructibility-criterion concerns an etale stalk-cardinality criterion, not this statement. The existing inverse-image composition theorem was reused. The new leaf's ID was absent before creation.

The searches.jsonl log contains every new Mathlib query used here. Both semantic phrasings of the whole item were read: the hits concern scheme sections, constructible subsets or generic sheaf-module pullback, not the full item. The logged query SheafOfModules.pullbackComp returns a generic ringed-site comparison, while Scheme.Modules.pullbackComp (Modules/Sheaf.lean:241-243, read) concerns structure-sheaf modules. These are not a one-line proof of the whole item with its specified pro-etale coefficients. The existing pro-etale module comparison is the bridge. For the new leaf, LeanFinder, LeanSearch, Loogle and the required grep all find IsImmersion.comp. I read the source at lines 146-158. The single-file grep wrapper renders the filename field as 146/222; the verified actual path and declaration line are recorded in mathlib_match. No unavailable service was recorded as absence and no search was invented.

## Review by Q117

I read coord/delivery-errors.md B-E in both copies and checked the item and the new leaf against those failure modes. For the item I read Stacks schemes.tex, lemma-composition-immersion (02V0), properties.tex, lemma-Noetherian-topology (01OZ), topology.tex, lemma-Noetherian-quasi-compact (04ZA), and sites-modules.tex, lemma-push-pull-composition-modules (03D8). I verified these tags against tags/tags. For the one new leaf I read both the 02V0 statement and its Mathlib implementation, including the factorization equivalence to the project's immersion definition. The node is self-contained, states no proof sketch, and has the requisite definition dependencies and blueprint provenance.

For step 1 I opened lem-weil-pbc-noetherian-open-subscheme-noetherian: its statement says every open subscheme of a Noetherian scheme is quasi-compact, which is exactly what is used, without extracting underlying Noetherian topology from its proof. The hypotheses match the item's locally Noetherian and quasi-compact assumption. Intersections of opens are opens, so the retrocompactness definition in def-weil-constructible-subset applies. I read def-weil-finite-type-morphism: it defines quasi-compact morphisms by preimages of affine opens; the homeomorphism of j with U makes the last inference immediate. I do not assume any separation or affineness of intersections.

For step 2 I checked that the new leaf supplies immersion composition for arbitrary schemes, so it applies to i and every t_mu. A closed immersion is an immersion via its factorization followed by the identity open immersion. def-weil-closed-immersion includes the closed-then-open definition; its image is therefore closed inside an open, or W intersect C with C ambient closed. Step 1 makes W and X minus C retrocompact, so the constructible-subset definition applies directly, without invoking a hidden constructible-image theorem. The injection of i preserves disjointness and carries the old cover to i(Z); the complementary U completes it. def-constructible-stratification requires precisely these locally closed images and immersion data. No new subscheme structure is selected and no reduction is performed.

For step 3 I read the full statement of lem-pur-proetale-module-pullback-composition. It asserts the natural functor isomorphism with the same actual module pullbacks and canonical constant-section maps as the item, for arbitrary commutative coefficient rings. Thus finite A is allowed. Substituting f=i and g=t_mu has the correct orientation. Functoriality carries the given closed restriction isomorphism to each stratum. This gives module-linearity and naturality from the cited statement itself, not a property of its proof, and avoids confusing small etale sheaves with small pro-etale sheaves.

For step 4 I read def-weil-proetale-locally-constant-sheaf, def-weil-proetale-geometric-stalk and def-weil-proetale-constructible-sheaf in full. A module-sheaf isomorphism composes with each local trivialization, and its inverse induces an inverse on each stalk colimit; hence finite stalks transfer without needing a separate invariance theorem. The zero module presheaf already satisfies the sheaf gluing condition; its sheafification is therefore the zero sheaf, locally constant on the identity cover. Every stalk of zero is zero, directly from the nonempty pointed-neighbourhood diagram (the final neighbourhood is the scheme with its chosen geometric point). The final partition has |I|+1 strata and so meets the project's N>=1 condition. These are short checks from definitions, explaining the elementary flag, not an unproved finite-coefficient descent claim.

I tested X empty; Z empty and U=X; U empty and Z=X as a set; empty individual strata; I empty (which forces Z empty); A the zero ring; P=N=0; and nilpotent closed thickenings such as Spec(k) into Spec(k[e]/e^2). In the last case U is empty but i is not an isomorphism: the proof uses only the supplied i_A^*P isomorphism and the canonical composition theorem, never a false identification of schemes or an assumed inverse of i. No stalk test of general pro-etale sheaves is used. Finiteness of A is used only to match the definition of finite constructibility, not to assert flatness or exactness. I confirmed proof_deps equals the union of uses, every quotation is a verbatim statement, all four steps are below 2000 characters, and no statement or proof edge points to the parent item. The two off-unit generic theorem uses are explained in split_report.tool_uses for maintainer review.

## Not duplicates

lem-sf-immersion-composition vs lem-per-excellent-quasiprojective-normalized-blowup: the existing statement concerns Normalized blowups preserve quasi-projectivity over an excellent affine base, with additional geometric or functorial data; it does not state arbitrary immersion composition by itself.

lem-sf-immersion-composition vs lem-per-quasiprojective-affine-composition: the existing statement concerns Composition into a finite projective space over an affine base, with additional geometric or functorial data; it does not state arbitrary immersion composition by itself.

lem-sf-immersion-composition vs lem-zl-prescribed-point-eventual-jet-system: the existing statement concerns Eventual kernel basis, complement immersion and simultaneous jets, with additional geometric or functorial data; it does not state arbitrary immersion composition by itself.

lem-sf-immersion-composition vs det-chow-projective-closed-immersions: the existing statement concerns Closedness of the Chow immersions for a proper morphism, with additional geometric or functorial data; it does not state arbitrary immersion composition by itself.

lem-sf-immersion-composition vs det-nagata-affine-opens-projective: the existing statement concerns Projective compactification of an affine piece, with additional geometric or functorial data; it does not state arbitrary immersion composition by itself.

lem-sf-immersion-composition vs lem-weil-pbc-basic-subset-immersion-image: the existing statement identifies one quotient-localization spectrum and its image; the new leaf applies to any pair of immersion morphisms.

lem-sf-immersion-composition vs lem-weil-pbc-immersion-affine-constructible-pieces: the existing statement refines a constructible immersion into an affine target by finitely many affine pieces; it does not state general composition.

lem-sf-immersion-composition vs lem-weil-pbc-proper-fp-permanence: the existing statement concerns Permanence of proper, separated, finite type, finitely presented morphisms and of immersions, with additional geometric or functorial data; it does not state arbitrary immersion composition by itself.

lem-sf-immersion-composition vs lem-sfb-finite-stratification-wide-pullback: the existing statement concerns Finite constructible stratifications have a limiting common fibre-product refinement, with additional geometric or functorial data; it does not state arbitrary immersion composition by itself.

lem-sf-immersion-composition vs lem-sfb-locally-closed-extension-coherence: the existing statement concerns Restriction and composition for locally closed extension by zero, with additional geometric or functorial data; it does not state arbitrary immersion composition by itself.

lem-sf-immersion-composition vs lem-sfb-locally-closed-module-extension-coherence: the existing statement concerns Normalized locally closed extension on module sheaves, with additional geometric or functorial data; it does not state arbitrary immersion composition by itself.

lem-sf-immersion-composition vs lem-sf-closed-partition-module-test: the item extends a closed-side partition and tests module constructibility; the new leaf is only arbitrary scheme immersion composition, with no sheaves or partition.

lem-sf-immersion-composition vs lem-sf-finite-immersion-constructibility-interval: the parent asserts constructible derived functors and cohomological bounds for complementary immersions; the new leaf only composes arbitrary scheme immersions.

lem-sf-immersion-composition vs lem-weil-pbc-irreducible-lisse-strata: the existing statement produces irreducible lisse strata for an etale sheaf; it does not state general composition.

lem-sf-immersion-composition vs lem-weil-pbc-closed-immersion-comp: the existing leaf assumes both maps are closed immersions; the new leaf allows arbitrary locally closed immersions. The stricter existing hypothesis does not cover a locally closed stratum in Z.
