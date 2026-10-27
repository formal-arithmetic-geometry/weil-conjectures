# Stage-1 delivery: lem-sfb-scheme-unramified-etale-locality

Group O3, direct-delivery worker, 2026-10-23.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-unramified-etale-locality.json: statement, split into six steps; no exact project attachment or Mathlib match for the full three-clause statement.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-stalk-formally-smooth.json: statement, Mathlib leaf. AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top, Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean:311, evaluated at the point and unfolded by the predicate at lines 305–309.
- dag/nodes/sec-six-functors-basics/lem-sfb-formally-unramified-stalk-map.json: statement, Mathlib leaf. AlgebraicGeometry.FormallyUnramified.stalkMap, Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean:151.
- citations.json: verbatim statement quotations for every step citation.
- searches.jsonl: actual launcher search log, retained across interruptions. Every new leaf has LeanFinder, Loogle, grep and LeanSearch searches; their results were read. The inherited item searches were retained and supplemented with the actual O3 searches.

## Attachments

None for the item. Project WeilConjectures source was searched for its blueprint tag and the relevant notions; no sorry-free declaration stating all three clauses was found. The two new leaves have Mathlib matches, not project attachments. Existing DAG nodes are cited rather than recreated.

## WANTED

None. All sources used are present in the read clone.

## Problems found and repairs

The imported item had no proof. Its statement is correct and is preserved. The proof must not invoke the parent algebraic-space permanence node, which depends on this item. I instead used scheme composition, arbitrary scheme base change, and differential descent on actual local rings. The existing source-and-target locality node covers local finite type, smoothness and other properties, but does not cover unramifiedness: step 3 uses only its local finite type clause. Similarly, the existing all-stalks formally-unramified criterion goes from stalks to the scheme, not conversely; the converse is the second new Mathlib leaf.

The inherited blueprint.from.node is null, with an existing long via chain and a descriptive place beginning det-thm-sf-ctf-stability-direct-images. The ancestor command reports that inherited null. I retained this provenance rather than inventing a blueprint id; both new leaves prepend this item to that inherited chain and specify their precise role. I read the current latest blueprint's direct-image proof (3); this is a scheme-local prerequisite for the already recorded compatible-chart branch, not a replacement of the unit's proof route. No unit realization is claimed. The server review_split check passed before this report was written.

I replaced the elementary identity-chart explanation by the diagonal definition of unramifiedness, so it needs no unstated differential criterion. No statement dispute or added hypothesis remains.

## Unfinished work

None within stage 1. No Lean was written or compiled. The two new nodes are statement-only Mathlib leaves; the item's proof is a complete assembly from cited statements. Delivery validation results are recorded below when available.

## Review by O3

I read Stacks descent.tex Tags 04R3 item (9), 04QZ, 03YV, 02VM and 04R2 for the item's locality assertion and its proof route. The reverse implication follows the source-local differential argument of 03YV after obtaining local finite type. I adapted it to actual stalk maps, avoiding an uncited identification of a sheaf of differentials with its stalks. The proof is marked agent-written because this assembly is my argument, not a transcription of a single proof.

For the smooth-stalk leaf I read morphisms.tex 01V6, more-morphisms.tex 02H6, and algebra.tex 04EG and 031H. Smooth affine charts are formally smooth on coordinate rings. Localization gives the actual stalk map; units in the localized base lift across nilpotent ideals. More decisively, I read Mathlib Smooth.lean lines 305–323: the smooth locus is defined using formal smoothness of the stalk homomorphism, and smoothLocus_eq_top under IsSmooth gives precisely the stated result at every point. This requires no finite presentation of the local ring map, no Noetherian assumption and no global surjectivity. A localization such as a smooth affine coordinate ring at a nonclosed prime is included; I did not falsely assert that every stalk map is finitely presented.

For the formally-unramified-stalk leaf I read algebra.tex 04E8, especially (1) implies (3), and more-morphisms.tex 0HAL, the affine characterization. I also read Mathlib FormallyUnramified.lean lines 151–156: the theorem applies directly to the actual stalk map under formal unramifiedness of the scheme morphism. It imposes neither local finite type nor finite presentation. The square-zero uniqueness formulation agrees with RingHom.FormallyUnramified. This direction is distinct from the existing node that assembles formal unramifiedness from all stalks.

Step 1 uses the definition of etale to obtain unramifiedness, then the existing scheme composition statement; the existing base-change-open statement explicitly allows arbitrary scheme base change and therefore includes the requested etale base change. I opened both statements and checked their direction and hypotheses. Neither assumes separation or quasi-compactness.

Step 2 is elementary: identity maps are flat and finitely presented, and their diagonals are identities and hence open immersions. The two cited definitions supply exactly the unramified and etale conditions. Choosing both identity charts retains every point, including arbitrary nonclosed points.

Step 3 uses only the local finite type clause of lem-sfb-scheme-etale-source-target-properties; I checked its pointwise compatible-square formulation, including the empty case, against the item's hypotheses. Unramified h is locally of finite type by definition. The same etale definition and composition statement as in step 1 make bh=fa unramified. This is not an application of the conclusion being proved.

Step 4 uses the locally-ringed-space morphism definition for composition of the actual stalk maps and their localness. The cited unramified-to-formally-unramified statement applies to g without further hypotheses; the new stalk leaf then applies to its actual stalk homomorphism. The existing ring criterion identifies formal unramifiedness with vanishing Kahler differentials. The flat-morphism definition states flatness of the stalk maps; combined with localness, it meets exactly the hypotheses of the existing flat-local-hom faithfully-flat statement. The equality a(u)=x is essential here: A and B are local rings at those actual points, rather than unrelated affine coordinate rings.

Step 5 uses the existing etale-implies-smooth clause, not its fibre dimension conclusion, followed by the smooth-stalk leaf. I read the general differential-injectivity statement: formal smoothness of A to B is the needed hypothesis for injectivity of B tensor_A Omega(A/R) into Omega(B/R), for an arbitrary composable ring pair. The codomain vanishes by step 4. The faithful-flat universal-injectivity statement uses the opposite tensor order; the written bilinear factor-switch supplies that elementary identification. The tensor-product definition is cited, and the inverse maps are written out. Thus Omega(A/R)=0, and the already cited ring criterion applies in the reverse direction. No flat descent theorem is silently assumed.

Step 6 uses precisely the all-actual-stalks to scheme formal-unramifiedness direction of lem-trf-formally-unramified-from-all-stalks. Local finite type from step 3 supplies the hypothesis of the existing formally-unramified plus locally-finite-type implies unramified result. I read both statements rather than citing the definition alone. They allow the empty source. This also checks the empty scheme edge case: both the chart and stalk conditions are vacuous and the same criteria conclude. Identity morphisms, open immersions and non-surjective etale source charts at selected points cause no additional assumptions. The proof never chooses a finite subcover, a closed point or a separable residue-field extension.

For delivery-errors B–E I checked source identity, the exact clauses and hypotheses taken from every cited node, absence of cycles through the parent permanence statement, absence of elementary or clause-restating new nodes, and the distinction between Mathlib matches and project attachments. All new nodes are genuine general stalk-map results, not restatements of a clause of the item. Every proof step is below 2000 characters. The report's citations are verbatim copied from the exact node statements. Source/tag and keyword searches covered the DAG and blueprint before creation; same_as is empty because no blueprint statement was an exact match. The following pairs document the shared-tag results, including broader source citations that do not state our leaves.

## Not duplicates

lem-sfb-smooth-stalk-formally-smooth vs def-sbc-smooth-morphisms: the existing node fixes the smooth morphism notion; the new result concerns formal smoothness of every actual local-ring map.

lem-sfb-smooth-stalk-formally-smooth vs sbc-lem-affine-space-smooth: affine-space projections are a special class of smooth morphisms; this does not state the stalk-map lifting property.

lem-sfb-smooth-stalk-formally-smooth vs sbc-lem-smooth-criterion: the existing criterion characterizes scheme smoothness using flatness and fibres; it does not give formal smoothness of stalk maps.

lem-sfb-smooth-stalk-formally-smooth vs lem-trf-affine-smooth-prime-scheme-neighbourhood: that node obtains a smooth scheme neighbourhood from a ring map smooth at a prime; this leaf starts with a smooth scheme morphism and concludes formal smoothness of its stalk map.

lem-sfb-smooth-stalk-formally-smooth vs lem-trf-localized-presentation-homotopy-equivalence: that node compares localized cotangent presentation complexes, rather than asserting the local-ring lifting property.

lem-sfb-smooth-stalk-formally-smooth vs lem-pc-proper-base-change: that node concerns cohomological base change, not local-ring formal smoothness.

lem-sfb-smooth-stalk-formally-smooth vs lem-sfb-regular-separable-affine-smooth-neighbourhood: regular points over a field yield smooth neighbourhoods there; the new statement applies to arbitrary smooth scheme morphisms and their stalk maps.

lem-sfb-smooth-stalk-formally-smooth vs lem-sc-etale-base-change-geometric: geometric field extension detects etaleness at a point, not formal smoothness of stalk maps of arbitrary smooth morphisms.

lem-sfb-smooth-stalk-formally-smooth vs lem-per-etale-local-infinitesimal-lifts-smooth: that node obtains smoothness from an etale-local lifting condition; this one gives the actual stalk-ring lifting property from smoothness.

lem-sfb-smooth-stalk-formally-smooth vs lem-weil-pbc-smooth-ring-map-iff-smooth-affine: the existing equivalence concerns the full coordinate ring of an affine scheme morphism, not a stalk map, which need not be finitely presented.

lem-sfb-smooth-stalk-formally-smooth vs lem-weil-pbc-localization-square-zero-lifting: that node is a ring-localization lifting statement, not a general theorem about stalk maps of smooth scheme morphisms.

lem-sfb-smooth-stalk-formally-smooth vs lem-weil-pbc-smooth-zero-differentials-affine-open-etale: smoothness together with vanishing differentials gives etaleness on affine opens there; this leaf has no vanishing-differentials hypothesis or etaleness conclusion.

lem-sfb-smooth-stalk-formally-smooth vs lem-weil-pbc-etale-smooth-zero-dimensional-fibres: that node relates etale and smooth morphisms with zero-dimensional fibres; it does not assert the stalk-ring lifting property.

lem-sfb-smooth-stalk-formally-smooth vs lem-weil-pbc-affine-opens-induced-ring-map-spec-square: that node identifies an affine chart's ring map and Spec square, without a smoothness or lifting assertion.

lem-sfb-smooth-stalk-formally-smooth vs lem-weil-pbc-smooth-locally-standard-smooth: standard smooth affine charts characterize smooth morphisms there; formal smoothness of the actual stalk map is a separate consequence stated by this leaf.

lem-sfb-smooth-stalk-formally-smooth vs lem-weil-pbc-smooth-restrict-open-subschemes: preservation of smoothness by restrictions and isomorphisms does not state the lifting property of stalk maps.

lem-sfb-smooth-stalk-formally-smooth vs lem-weil-pbc-smooth-section-etale-lift: that node lifts sections after etale base change; the new node gives an algebra lifting property at each actual point.

lem-sfb-smooth-stalk-formally-smooth vs lem-weil-pbc-smooth-local-on-source: Zariski source locality of smoothness is distinct from formal smoothness of stalk homomorphisms.

lem-sfb-smooth-stalk-formally-smooth vs lem-weil-pbc-popescu-smoothing: the existing node is a filtered-colimit theorem for regular Noetherian ring maps, with different hypotheses and conclusion.

lem-sfb-smooth-stalk-formally-smooth vs lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension: local freeness and rank of smooth differentials is not the square-zero lifting property of local-ring homomorphisms.

lem-sfb-smooth-stalk-formally-smooth vs lem-weil-pbc-smooth-coproduct: smoothness of a coproduct is a scheme permanence statement, not a stalk formal-smoothness theorem.

lem-sfb-formally-unramified-stalk-map vs lem-trf-formally-unramified-from-all-stalks: the existing node proves scheme formal unramifiedness from all formally unramified stalk maps; the new leaf proves the reverse implication and supplies no missing local finite type assumption.

## Validation

The first dry run rejected comma-separated node ids inside one pair of brackets in the two new statements. I changed them to separate bracketed references, preserving the mathematical statements, and regenerated their citation quotations.
