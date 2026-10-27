# Worker report: lem-trf-relative-proj-invertible-twist

## Repair of landing refusal (2026-10-22)

L returned the approved split because its side completion had not been promoted to the live DAG. This repair keeps the retained two-task decomposition and rebases it through deliver.py, which fetches current origin/sheaf-dag and constructs a fresh delivery commit on it. I did not treat the old reviewed=true/split fields as completion: coord/repair-notes/lem-trf-relative-proj-invertible-twist.json remains released for stage 1 and requires this two-node re-split.

The retained node files have the same hashes as the earlier sandbox dry-run receipt 171f03b84e3. Comparing the retained item with the current read-clone node found only proof, proof_deps and split_report different; its statement, statement dependencies, Lean metadata, ancestry and maintainer fields agree. Neither new node exists in the current read clone. I refreshed the item's inherited fields from that current node, preserved its approved stage-1 split, and made two explicit assembly repairs: step 3 now derives the frame-transition unit using the two inverse frame maps, and step 4 specifies the inverse-image source open covers and compositions with target open inclusions used by the morphism-gluing theorem. The two new tasks, citations and actual search log are retained. The historical report below describes their original construction.

The required initial dry run exited successfully at de06d35a971 before these edits. A new final dry run and delivery will check the revised files against the fetched live server baseline. This is a refreshed delivery with an updated proof and review, not an unchanged re-push.

1. Files written:
   - dag/nodes/sec-trace-formula/lem-trf-relative-proj-invertible-twist.json: unchanged theorem statement, repaired split, four assembly steps (2086 characters).
   - dag/nodes/sec-trace-formula/lem-trf-framed-symmetric-twist-comparison.json: statement, unsplit, no Mathlib match. Framed tensor identifications, finite type and quasi-coherence, normalized graded symmetric-algebra isomorphisms, restrictions, and frame-transition scaling.
   - dag/nodes/sec-trace-formula/lem-trf-local-proj-isomorphism-compatibility.json: statement, unsplit, no Mathlib match. Inverse chart morphisms, base restrictions and invariance under degreewise unit scaling.
   - citations.json: verbatim statement quotations for every citation of every assembly step.
2. Attachments: none. The item's Sheaf declaration AlgebraicGeometry.exists_unique_relativeProj_invertible_twist (RelativeProjInvertibleTwist.lean:73) ends in sorry. Searches by tag and projective-bundle/tensor-twist concepts in WeilConjectures found no exact completed item declaration. No Lean was edited or compiled.
3. WANTED: none. All mathematical sources used are available locally.
4. The return requires distributing the old 6008-character proof into at least two new independent tasks, leaving at most 3000 characters of assembly. This is repaired, rather than re-pushing the previous split. There were no retained sandbox JSON nodes, report or searches at session start: only .brief marker files. The required initial dry run exited with “no node files”. I therefore used the current shared repository's complete seven-step version as the returned head, preserving its statement, existing fields, original search records and historical reviews. There is no source-statement dispute, no hypothesis change, and no change to chapter or unit route.
5. Unfinished work: the two new nodes are deliberately statement-only and unsplit, for future workers. Nothing else in the authorized repair remains once the final dry run and push pass.

## Repair of the numbered return

The sole return is the human's re-split decision. The two tasks have comparable scope (1768 and 2202 statement characters) and neither asserts the global canonical twisting theorem. The framed symmetric comparison is algebraic and has no Proj conclusion. The local Proj comparison accepts arbitrary graded sheaf algebras and a supplied local isomorphism, and does not construct any global twisting isomorphism. Neither is merely one global clause of the item. New nodes carry proof=[], proof_deps=[] and proof_origin=null. The parent's assembly has four steps, 2086 characters total, all under 2000 individually.

Coverage of every old argument:

- Old step 1: the affine frame cover remains assembly step 1. The tensor maps, their explicit inverses, the n=0 convention, and preservation of quasi-coherence/finite type are conclusions of the framed symmetric comparison.
- Old step 2: that same new node asserts the uniquely normalized graded algebra isomorphism, its inverse from the inverse module map, identity on scalars, and the ordinary symmetric-algebra description on every affine open.
- Old step 3: the local Proj comparison asserts the induced morphism over the affine base, the exact a/f^m formula, inverse images and chart cover, and uniqueness; no cancellation of f or regularity is assumed.
- Old step 4: the local Proj comparison asserts that the construction for beta inverse is the inverse scheme map, under the specified relative-Proj affine restriction identifications.
- Old step 5: the framed symmetric comparison gives tau_(ue)=u^n tau_e and beta_(ue),k=u^(nk) beta_e,k. The local Proj comparison gives equality of the standard opens and the explicit cancellation of unit powers in the degree-zero fractions, including equality of inverses.
- Old step 6: the framed symmetric comparison carries the generator/universal-property restriction identification. The local Proj comparison carries affine-base restriction, including the coefficient-restriction fraction formula and inverse maps.
- Old step 7: assembly steps 3-4 retain affine refinements of overlaps, equality of both directions, gluing, inverse identities and the over-S equality, independence of frames and covers, uniqueness with local normalization, and inversion to the requested direction.

The intended proofs of the new tasks are preserved verbatim below from the old proof rather than inserted into their statements as sketches. This also records the arguments future workers must keep: universal-property uniqueness and homogeneous monomials for the first task; applying affine scalar extension with the identity base map, comparing inverse chart fractions, comparing coefficient restrictions, and cancelling unit powers for the second. They can be worked on separately; the second is formulated for arbitrary graded algebra isomorphisms and does not depend on the first.

## Searches and route

I read SETUP.md's chapter/unit/node levels, the stage-1 brief and stage document, GOAL.md, roles/worker.md, the chapter sec-trace-formula and unit sk-i-curve-zero, and delivery-errors.md B-E. I retained the inherited 087S/02NC generic-tool route below the projective-bundle-to-H-projective step, with blueprint ancestor lem-trf-local-term-locality and its complete via chain, extended by this item for the new nodes. This item is not the unit's key node; no unit realization record was changed. No SGA source is used.

Before creation I searched the whole DAG by tag 02NC, the Proj tags 01MY/01N2, by graded isomorphism, unit rescaling, frames and symmetric algebras, and by both proposed ids. I ran blueprint_refs.py ancestor on the item and search on 02NC, rescaling, symmetric algebra, graded isomorphism, degree-zero, invertible twist, local Proj, and frame. I read the relevant candidate statements, including prop-nagata-relative-proj-functoriality and def-sfb-relative-proj-iso-of-graded-iso. None states the complete new tasks, so same_as is empty.

For each new node the recorded msearch.py calls include LeanFinder, Loogle, grep and LeanSearch, with a second semantic phrasing and focused second grep. I read all hits; the JSON records use the actual log's tool/query, top hits and digest. All twelve calls succeeded. SymmetricAlgebra.lift and IsSymmetricAlgebra.of_equiv are ordinary module/algebra facts, not the sheaf comparison and transition/restriction assertions. Proj.map, awayι_comp_map, map_comp and map_id in Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Functor.lean (148, 192, 210, 217) cover chart construction and functoriality but not the entire relative sheaf comparison or its degreewise unit invariance. I read their definitions and proofs and the symmetric-algebra universal-property source.

The project also has AlgebraicGeometry.Proj.fromOfGlobalSections_eq_of_unit_pow_mul in WeilConjectures/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:273. I read it: its input is a map into the global functions of a source scheme whose irrelevant ideal generates 1. It proves rescaling for that particular construction, not the new node's complete relative-Proj comparison with inverse and affine-base restriction data. It is a useful prospective tool on normalized charts, not an exact attachment for either new node. Its DAG hit lem-weil-pbc-projective-space-functor-of-points concerns finite projective spaces and line-quotient functors, not this statement.

## Review by Q74


For this landing-refusal repair I reopened the current statements of every external dependency of the item and of both new tasks, and re-read Stacks constructions.tex, lemma-twisting-and-proj (02NC), lemma-morphism-proj (01MY), and lemma-base-change-map-proj (01N2). All twelve retained citation quotes are still verbatim in the current statements; none required replacement. In particular, def-nagata-relative-proj now explicitly records affine restriction identifications and their coefficientwise compatibility without assuming A_0=O_S or affine intersections. The local-Proj task uses exactly those specified identifications, so its arbitrary graded-algebra scope remains valid.

Step 1 still obtains local rank-one frames from def-sc-invertible-module and affine refinements from lem-weil-pbc-affine-opens-basis; the framed symmetric comparison supplies finite type, quasi-coherence and the scalar-fixing graded beta. Step 2 uses the local-Proj task's inverse isomorphisms and affine-restriction clauses. Step 3 uses its equality under degreewise unit scaling with the unit u^n, together with the framed task's u^(nk) formula. I expanded the elementary argument that the scalar u is invertible: if the reverse frame change is v, the two inverse O-linear frames give uv=1. The gluing node states uniqueness for morphisms on an open covering, so it applies after pulling the affine refinement back to the projective bundle, with a common global target. Step 4 now spells out those source opens and target inclusions in the proof itself, glues both directions, and uses the same uniqueness to check identities, the structure maps and independence of choices. The projective-bundle definition is used only for P(E)=Proj(Sym E).

I rechecked the two new task statements hypothesis by hypothesis: S is arbitrary, E is finite type and quasi-coherent, L is invertible, and n includes zero in the first; arbitrary quasi-coherent graded algebra sheaves, an affine base open and a scalar-fixing graded isomorphism are the second task's inputs. The two tasks have no global twisting conclusion and no dependence on their parent. For n=0 the maps are unit identifications; for E=0 or an empty base the projective schemes are empty; on nonreduced bases the fraction comparison cancels only unit powers. The cover argument still works for non-quasi-separated bases because intersections are refined by affine opens. I retained all old proof arguments and source/search records, and no new Mathlib search question arose. B-E were checked again against the open files, with the two assembly clarifications just described as the corrections for this repair.

I read Stacks constructions.tex Tag 02NC, label lemma-twisting-and-proj, including the definition of the graded twist immediately before it and its proof immediately after it. The source says to trivialize the line and glue, leaving the compatibility details omitted. I also read Tag 01MY, label lemma-morphism-proj, and Tag 01N2, label lemma-base-change-map-proj. For the framed comparison these supply the local-trivialization route, specialized to Sym(E) and L tensor-power n. For the local Proj comparison these supply the canonical fraction morphisms and base localization. I checked the new statements against those sources and the full old proof: all omitted compatibility arguments now have explicit conclusions in the new task statements. Source places are tag plus TeX label, not mutable section numbers.

Assembly step 1 uses the actual locally-free-rank-one assertion of def-sc-invertible-module and the pointwise affine-refinement assertion of lem-weil-pbc-affine-opens-basis. The framed comparison explicitly supplies both quasi-coherence and finite type of E_n and the scalar-fixing graded sheaf maps needed for step 2. Its hypotheses are precisely the item's hypotheses, including n in N, with zero allowed.

Assembly step 2 uses the local Proj comparison's U-isomorphism and restriction clauses. Its algebra sheaves are the quasi-coherent symmetric algebras supplied by the framed node (which states their construction via the existing symmetric-algebra node); beta is a graded O_U-algebra isomorphism, so the structural base ring is respected. Its direction is Proj(B) to Proj(A). Both maps and both inverses are explicitly included in the cited statement.

Assembly step 3 uses the affine basis only to refine overlaps; it never assumes an affine intersection. From the two frame isomorphisms O_V to L|V, their composite is an O_V-module automorphism of O_V, hence multiplication by a unit u. The framed comparison explicitly says degree k scales by u^(nk). The local Proj comparison explicitly says scaling by the kth power of any unit gives the same morphism: its unit is u^n here. Its restriction assertion identifies the maps on V before making this comparison. The same statement includes inverse equality. Scheme-morphism gluing's uniqueness clause then extends equality from that cover to the full overlap. Every cited statement is open in the citation audit and the exact text is copied into citations.json.

Assembly step 4 uses the existence and uniqueness clauses of lem-weil-pbc-scheme-morphism-gluing, both for gluing the maps and inverses and for checking their composites and their maps to S. The local identities come from step 2. Comparing two choices means applying step 3 on affine refinements of the intersections of the two covers, so neither a hidden separatedness hypothesis nor an unproved global identification is used. def-trf-projective-bundle-morphism supplies exactly P(E)=Proj_S(Sym E); it is cited for that convention, not as a gluing theorem. The final inversion puts the result in the item's direction. Canonicity means uniqueness with the prescribed local frame formula, not uniqueness among all isomorphisms of projective bundles.

I checked B1-B10: both new nodes are self-contained statements without proof instructions; every scheme, module, grading, tensor power, chart ring and frame is introduced and linked to its defining node (frames are defined inline); TeX is singly escaped; sources use tags and labels; no Mathlib leaf is claimed; searches are actual logged calls with their real results; blueprint provenance is filled; no completed project theorem is re-split. I checked C1-C8: every non-elementary assembly fact is a node citation, and quotes are statements, not proofs; the assembly uses no off-unit theorem besides its inherited definitions/tools, and its two new same-unit nodes do not depend on the parent. I checked D1-D5: the tasks separate the algebraic and Proj compatibility arguments rather than copying the whole item or renaming its clauses. I checked E1-E7: all applications meet their hypotheses; directions and degree exponents agree; restriction and unit cancellation are explicitly stated; no source error was found.

Small-case checks: n=0 gives the module-unit maps, beta the identity under the unit identifications, and all scaling factors 1. Trivial L gives the expected local normalization, with no global frame chosen canonically. E=0 gives empty relative Proj and the unique empty maps. Empty S and the zero ring are allowed. For a nonreduced base such as Z/4 and the unit -1, cancelling only unit powers works even when a homogeneous denominator is a zero divisor or nilpotent; a nilpotent denominator gives an empty chart. For arbitrary graded algebras the irrelevant ideal and homogeneous positive-degree chart cover suffice; no degree-one generation or equality A_0=O_S is assumed. For a non-quasi-separated S, overlaps are handled by affine covers, with no finite-cover assumption. The two new tasks are not independently elementary: together they carry the multiple universal-property, inverse-chart, restriction and frame-transition arguments formerly spread over six steps; the elementary global cover-and-glue assembly remains in the parent.

## Not duplicates

lem-trf-framed-symmetric-twist-comparison vs def-nagata-graded-algebra-pullback-data: the existing node defines coefficientwise pullback data for a base morphism; the new task proves frame-normalized maps or invariance properties and does not define pullback data.

lem-trf-framed-symmetric-twist-comparison vs def-sfb-relative-proj-iso-of-graded-iso: the existing definition specifies the induced relative-Proj isomorphism and its chart formula; it does not state equality of the maps for distinct graded isomorphisms differing by degreewise units, including the explicit cancellation and both inverses; it is not a theorem establishing that compatibility. The framed task also has different input and no Proj conclusion.

lem-trf-framed-symmetric-twist-comparison vs lem-coef-infinity-equivalence-anodyne-factorization: the existing theorem concerns right-anodyne factorization of equivalences of quasicategories and a Kerodon 02NC reference, not Proj or symmetric algebras.

lem-trf-framed-symmetric-twist-comparison vs lem-coef-infinity-equivalence-section-restriction: the existing theorem concerns right-fibration section spaces and a Kerodon identifier 02NC, not the Stacks twisting tag or graded sheaf algebras.

lem-trf-framed-symmetric-twist-comparison vs lem-coef-inner-anodyne-pointwise-lan-invariance: the existing theorem concerns coherent Kan extension diagrams and uses a Kerodon tag in its references; it says nothing about the algebraic-geometric constructions here.

lem-trf-framed-symmetric-twist-comparison vs lem-nagata-affine-proj-scalar-extension: the existing theorem supplies the base-change morphism and its fractions; the local Proj task additionally states inverse maps, sheaf-level affine restriction compatibility and equality for two distinct algebra maps differing by degreewise units; the framed task is about symmetric sheaf algebras, not scalar extension of Proj.

lem-trf-framed-symmetric-twist-comparison vs lem-nagata-homogeneous-localization-scalar-extension: the existing theorem is the tensor/base-change isomorphism of degree-zero chart rings, not a comparison of framed symmetric sheaves or the relative Proj maps and their unit invariance.

lem-trf-framed-symmetric-twist-comparison vs lem-per-finite-graded-proj-morphism: the existing theorem needs a finite-type graded base and module-finite injective algebra map, and concludes finite surjectivity; the local comparison has arbitrary quasi-coherent algebra sheaves, isomorphisms, affine restriction and unit invariance, and no finiteness assumptions.

lem-trf-framed-symmetric-twist-comparison vs lem-sfb-projective-affine-base-blowup: the existing theorem is H-projectivity of blowups over a Noetherian affine base; the new task neither constructs a blowup nor assumes such a base.

lem-trf-framed-symmetric-twist-comparison vs lem-trf-projective-bundle-to-h-projective: the existing theorem converts projective-bundle projectivity into finite-projective-space projectivity on an ample base; neither new task asserts that projectivity conversion.

lem-trf-framed-symmetric-twist-comparison vs lem-trf-relative-proj-invertible-twist: the existing item asserts a global canonical twisting isomorphism; the framed task has no Proj conclusion and the local comparison requires an already supplied local algebra isomorphism and provides its restriction/rescaling identities, not a global twist.

lem-trf-framed-symmetric-twist-comparison vs lem-weil-pbc-projective-space-functor-of-points: the existing theorem concerns finite projective spaces and line-quotient functors, not arbitrary graded quasi-coherent algebra isomorphisms with affine-base restrictions or framed symmetric sheaves.

lem-trf-framed-symmetric-twist-comparison vs lem-weil-pbc-quasi-coherent-symmetric-algebra: the existing theorem supplies the universal algebra and affine comparison; it does not supply the framed tensor-power maps, their graded scaling identity and all frame/restriction data. The local Proj task is about arbitrary graded algebras.

lem-trf-framed-symmetric-twist-comparison vs lem-weil-pbc-symmetric-algebra-graded: the existing theorem gives the ordinary symmetric grading; it has no sheaf frame comparison and no relative-Proj morphism statement.

lem-trf-framed-symmetric-twist-comparison vs prop-nagata-relative-proj-functoriality: the existing theorem says a graded equivalence induces a Proj isomorphism, but gives no equality under degreewise unit rescaling or its fraction cancellation. It does not construct the framed symmetric-algebra data.

lem-trf-local-proj-isomorphism-compatibility vs def-nagata-graded-algebra-pullback-data: the existing node defines coefficientwise pullback data for a base morphism; the new task proves frame-normalized maps or invariance properties and does not define pullback data.

lem-trf-local-proj-isomorphism-compatibility vs def-sfb-relative-proj-iso-of-graded-iso: the existing definition specifies the induced relative-Proj isomorphism and its chart formula; it does not state equality of the maps for distinct graded isomorphisms differing by degreewise units, including the explicit cancellation and both inverses; it is not a theorem establishing that compatibility. The framed task also has different input and no Proj conclusion.

lem-trf-local-proj-isomorphism-compatibility vs lem-coef-infinity-equivalence-anodyne-factorization: the existing theorem concerns right-anodyne factorization of equivalences of quasicategories and a Kerodon 02NC reference, not Proj or symmetric algebras.

lem-trf-local-proj-isomorphism-compatibility vs lem-coef-infinity-equivalence-section-restriction: the existing theorem concerns right-fibration section spaces and a Kerodon identifier 02NC, not the Stacks twisting tag or graded sheaf algebras.

lem-trf-local-proj-isomorphism-compatibility vs lem-coef-inner-anodyne-pointwise-lan-invariance: the existing theorem concerns coherent Kan extension diagrams and uses a Kerodon tag in its references; it says nothing about the algebraic-geometric constructions here.

lem-trf-local-proj-isomorphism-compatibility vs lem-nagata-affine-proj-scalar-extension: the existing theorem supplies the base-change morphism and its fractions; the local Proj task additionally states inverse maps, sheaf-level affine restriction compatibility and equality for two distinct algebra maps differing by degreewise units; the framed task is about symmetric sheaf algebras, not scalar extension of Proj.

lem-trf-local-proj-isomorphism-compatibility vs lem-nagata-homogeneous-localization-scalar-extension: the existing theorem is the tensor/base-change isomorphism of degree-zero chart rings, not a comparison of framed symmetric sheaves or the relative Proj maps and their unit invariance.

lem-trf-local-proj-isomorphism-compatibility vs lem-per-finite-graded-proj-morphism: the existing theorem needs a finite-type graded base and module-finite injective algebra map, and concludes finite surjectivity; the local comparison has arbitrary quasi-coherent algebra sheaves, isomorphisms, affine restriction and unit invariance, and no finiteness assumptions.

lem-trf-local-proj-isomorphism-compatibility vs lem-sfb-projective-affine-base-blowup: the existing theorem is H-projectivity of blowups over a Noetherian affine base; the new task neither constructs a blowup nor assumes such a base.

lem-trf-local-proj-isomorphism-compatibility vs lem-trf-projective-bundle-to-h-projective: the existing theorem converts projective-bundle projectivity into finite-projective-space projectivity on an ample base; neither new task asserts that projectivity conversion.

lem-trf-local-proj-isomorphism-compatibility vs lem-trf-relative-proj-invertible-twist: the existing item asserts a global canonical twisting isomorphism; the framed task has no Proj conclusion and the local comparison requires an already supplied local algebra isomorphism and provides its restriction/rescaling identities, not a global twist.

lem-trf-local-proj-isomorphism-compatibility vs lem-weil-pbc-projective-space-functor-of-points: the existing theorem concerns finite projective spaces and line-quotient functors, not arbitrary graded quasi-coherent algebra isomorphisms with affine-base restrictions or framed symmetric sheaves.

lem-trf-local-proj-isomorphism-compatibility vs lem-weil-pbc-quasi-coherent-symmetric-algebra: the existing theorem supplies the universal algebra and affine comparison; it does not supply the framed tensor-power maps, their graded scaling identity and all frame/restriction data. The local Proj task is about arbitrary graded algebras.

lem-trf-local-proj-isomorphism-compatibility vs lem-weil-pbc-symmetric-algebra-graded: the existing theorem gives the ordinary symmetric grading; it has no sheaf frame comparison and no relative-Proj morphism statement.

lem-trf-local-proj-isomorphism-compatibility vs prop-nagata-relative-proj-functoriality: the existing theorem says a graded equivalence induces a Proj isomorphism, but gives no equality under degreewise unit rescaling or its fraction cancellation. It does not construct the framed symmetric-algebra data.

lem-trf-framed-symmetric-twist-comparison vs lem-trf-local-proj-isomorphism-compatibility: the first concludes framed graded-algebra comparison and scaling before Proj; the second takes arbitrary graded-algebra isomorphisms as input and concludes geometric comparison identities. They can be proved independently.


lem-trf-framed-symmetric-twist-comparison vs lem-coef-weak-equivalence-representable-local-model: the existing statement is a simplicial-presheaf model for derived equivalence spaces, not a statement about schemes, graded algebras or Proj.

lem-trf-framed-symmetric-twist-comparison vs lem-coef-system-localization-universal: the existing statement is universal infinity localization preserving finite products, not the algebraic-geometric comparison.

lem-trf-framed-symmetric-twist-comparison vs lem-sfb-projective-closed-subscheme-homogeneous-ideal: the existing statement recovers closed subschemes of finite projective space from homogeneous ideals, not framed symmetric algebras or unit-rescaling invariance.

lem-trf-framed-symmetric-twist-comparison vs lem-sfb-graded-proj-quotient-twist-comparison: the existing statement concerns a degree-one-generated graded quotient and tautological twist comparisons; it does not assert the framed comparison or affine-base restriction plus unit invariance for arbitrary graded sheaves.

lem-trf-framed-symmetric-twist-comparison vs lem-cbc-simplicial-groupoid-localization: the existing statement is localization of simplicial shapes to a Kan complex, unrelated to homogeneous localization of ring sheaves.

lem-trf-framed-symmetric-twist-comparison vs lem-pur-projective-bundle-base-change-coherence: the existing statement concerns normalized finite-rank vector-bundle frame models and coefficientwise pullbacks with a degree-one twist; it does not state line-tensor frame scaling for finite-type quasi-coherent modules or invariance under distinct graded maps differing by units.

lem-trf-framed-symmetric-twist-comparison vs lem-coef-enriched-category-tensor-calculus: the existing statement concerns enriched infinity categories and their tensor/cotensor calculus, not tensor powers of a line bundle or relative Proj.

lem-trf-framed-symmetric-twist-comparison vs lem-coef-hammock-infinity-localization: the existing statement constructs hammock infinity localization of ordinary relative categories, not graded localization or Proj.

lem-trf-framed-symmetric-twist-comparison vs lem-nagata-proj-affine-restriction: the existing statement compares the local models of one algebra under affine restrictions; it does not compare two graded algebra sheaves or prove invariance under degreewise units, and has no framed symmetric-algebra data.

lem-trf-framed-symmetric-twist-comparison vs lem-trf-hilbert-samuel-near-normal-cone: the existing statement concerns Hilbert-Samuel functions and an exceptional fibre normal-cone decomposition over Q, not either new compatibility statement.

lem-trf-framed-symmetric-twist-comparison vs lem-coef-contractible-factor-universal-localization: the existing statement concerns universally localizing simplicial maps after multiplying by a contractible simplicial set; it is unrelated to Proj or sheaf tensor powers.

lem-trf-framed-symmetric-twist-comparison vs lem-per-projective-finite-group-quotient: the existing statement constructs finite group quotients of quasi-projective schemes, with finiteness and Noetherian hypotheses absent from the new tasks.

lem-trf-framed-symmetric-twist-comparison vs lem-per-excellent-quasiprojective-normalized-blowup: the existing statement proves finiteness and projectivity of a normalized blowup on an excellent base, not graded-algebra frame or local-Proj compatibility.

lem-trf-local-proj-isomorphism-compatibility vs lem-coef-weak-equivalence-representable-local-model: the existing statement is a simplicial-presheaf model for derived equivalence spaces, not a statement about schemes, graded algebras or Proj.

lem-trf-local-proj-isomorphism-compatibility vs lem-coef-system-localization-universal: the existing statement is universal infinity localization preserving finite products, not the algebraic-geometric comparison.

lem-trf-local-proj-isomorphism-compatibility vs lem-sfb-projective-closed-subscheme-homogeneous-ideal: the existing statement recovers closed subschemes of finite projective space from homogeneous ideals, not framed symmetric algebras or unit-rescaling invariance.

lem-trf-local-proj-isomorphism-compatibility vs lem-sfb-graded-proj-quotient-twist-comparison: the existing statement concerns a degree-one-generated graded quotient and tautological twist comparisons; it does not assert the framed comparison or affine-base restriction plus unit invariance for arbitrary graded sheaves.

lem-trf-local-proj-isomorphism-compatibility vs lem-cbc-simplicial-groupoid-localization: the existing statement is localization of simplicial shapes to a Kan complex, unrelated to homogeneous localization of ring sheaves.

lem-trf-local-proj-isomorphism-compatibility vs lem-pur-projective-bundle-base-change-coherence: the existing statement concerns normalized finite-rank vector-bundle frame models and coefficientwise pullbacks with a degree-one twist; it does not state line-tensor frame scaling for finite-type quasi-coherent modules or invariance under distinct graded maps differing by units.

lem-trf-local-proj-isomorphism-compatibility vs lem-coef-enriched-category-tensor-calculus: the existing statement concerns enriched infinity categories and their tensor/cotensor calculus, not tensor powers of a line bundle or relative Proj.

lem-trf-local-proj-isomorphism-compatibility vs lem-coef-hammock-infinity-localization: the existing statement constructs hammock infinity localization of ordinary relative categories, not graded localization or Proj.

lem-trf-local-proj-isomorphism-compatibility vs lem-nagata-proj-affine-restriction: the existing statement compares the local models of one algebra under affine restrictions; it does not compare two graded algebra sheaves or prove invariance under degreewise units, and has no framed symmetric-algebra data.

lem-trf-local-proj-isomorphism-compatibility vs lem-trf-hilbert-samuel-near-normal-cone: the existing statement concerns Hilbert-Samuel functions and an exceptional fibre normal-cone decomposition over Q, not either new compatibility statement.

lem-trf-local-proj-isomorphism-compatibility vs lem-coef-contractible-factor-universal-localization: the existing statement concerns universally localizing simplicial maps after multiplying by a contractible simplicial set; it is unrelated to Proj or sheaf tensor powers.

lem-trf-local-proj-isomorphism-compatibility vs lem-per-projective-finite-group-quotient: the existing statement constructs finite group quotients of quasi-projective schemes, with finiteness and Noetherian hypotheses absent from the new tasks.

lem-trf-local-proj-isomorphism-compatibility vs lem-per-excellent-quasiprojective-normalized-blowup: the existing statement proves finiteness and projectivity of a normalized blowup on an excellent base, not graded-algebra frame or local-Proj compatibility.

## Preserved arguments from the returned seven-step proof

The following is the complete current-repository proof used as the repair baseline. Its arguments are allocated above; these are report material, not proof sketches in the new statement-only nodes.

### Old step 1

Put $\mathcal E'=\mathcal E\otimes\mathcal L^{\otimes n}$, with $\mathcal L^{\otimes0}=\mathcal O_S$. By [def-sc-invertible-module] choose local generators $e_i$ of $\mathcal L$ on an open cover; refine to affine opens $U_i$ using [lem-weil-pbc-affine-opens-basis]. The tensor definition [def-pur-sheaf-tensor-product] gives inverse module maps $\tau_i:\mathcal E|_{U_i}\to\mathcal E'|_{U_i}$, $v\mapsto v\otimes e_i^{\otimes n}$, and $v\otimes a e_i^{\otimes n}\mapsto av$. For $n=0$ these are the unit identifications. In particular $\mathcal E'$ is quasi-coherent and of finite type: near any point these maps identify it with $\mathcal E$, so the affine module presentation and the finite generating surjection in [pqf-def-coherent] also present $\mathcal E'$.

### Old step 2

Let $\mathcal A=\operatorname{Sym}(\mathcal E)$ and $\mathcal B=\operatorname{Sym}(\mathcal E')$. The sheaf symmetric-algebra theorem [lem-weil-pbc-quasi-coherent-symmetric-algebra] supplies these quasi-coherent algebras and their functoriality. Applying its universal property to $\tau_i$ and $\tau_i^{-1}$ gives inverse algebra maps $\beta_i:\mathcal A|_{U_i}\xrightarrow{\sim}\mathcal B|_{U_i}$: each composite fixes the degree-one generators, hence is the identity by uniqueness. The monomial description of [lem-weil-pbc-symmetric-algebra-graded] makes these maps degree preserving and the identity in degree zero. On any affine $V\subseteq U_i$ they are graded $R$-algebra isomorphisms $A\to B$, where $R=\Gamma(V,\mathcal O_S)$, $A=\Gamma(V,\mathcal A)$ and $B=\Gamma(V,\mathcal B)$; the affine-section clause of the sheaf symmetric-algebra theorem identifies these with the ordinary symmetric algebras and their symmetric gradings.

### Old step 3

Here is the local isomorphism induced by any $\beta_i:A\xrightarrow{\sim}B$ of step 2. Apply [lem-nagata-affine-proj-scalar-extension] with both base rings equal to $R$ and the identity $R\to R$, so that $R\otimes_RA=A$, and with the graded $R$-algebra isomorphism $\beta_i$ (both unit maps land in degree zero by step 2). It gives a canonical morphism $r_{\beta_i}:\operatorname{Proj}(B)\to\operatorname{Proj}(A)$ over $\operatorname{Spec}R$ such that, for $f\in A_d$ with $d>0$, the inverse image of $D_+(f)$ is $D_+(\beta_i(f))$, and on it $r_{\beta_i}$ is the spectrum morphism of
$$A_{(f),0}\longrightarrow B_{(\beta_i(f)),0},\qquad a/f^m\longmapsto\beta_i(a)/\beta_i(f)^m\quad(a\in A_{md})$$
[def-nagata-homogeneous-localization-degree-zero]. These opens cover $\operatorname{Proj}(B)$, and the chart formulas determine $r_{\beta_i}$ uniquely. No non-zero-divisor hypothesis on $f$ is used.

### Old step 4

Applying the same lemma to $\beta_i^{-1}$ gives $r_{\beta_i^{-1}}:\operatorname{Proj}(A)\to\operatorname{Proj}(B)$. On every chart, each composite $r_{\beta_i}\circ r_{\beta_i^{-1}}$ or $r_{\beta_i^{-1}}\circ r_{\beta_i}$ is the spectrum morphism of the composite fraction map, i.e. of the identity map $a/f^m\mapsto a/f^m$ [def-weil-affine-spectrum]. These chart opens cover, so both composites are identities by the uniqueness in [lem-weil-pbc-scheme-morphism-gluing]. Hence $r_{\beta_i}$ is an isomorphism over $\operatorname{Spec}R$. For $V=U_i$, the affine restriction isomorphisms $i_{U_i}$ in [def-nagata-relative-proj] for $\operatorname{Sym}\mathcal E$ and $\operatorname{Sym}\mathcal E'$ thus give an isomorphism $g_i:\mathbf P_S(\mathcal E')|_{U_i}\xrightarrow{\sim}\mathbf P_S(\mathcal E)|_{U_i}$ over $U_i$.

### Old step 5

Check a change of generator on any affine $W\subseteq U_i\cap U_j$. Write $e_j=u e_i$ with $u\in\Gamma(W,\mathcal O_S)^\times$; the inverse scalar comes from the inverse change of the two rank-one frames [def-sc-invertible-module]. Then $\tau_j=u^n\tau_i$. Since a homogeneous degree-$k$ element is a sum of degree-$k$ monomials [lem-weil-pbc-symmetric-algebra-graded], $\beta_j(a)=u^{nk}\beta_i(a)$ for $a\in A_k$. Thus $D_+(\beta_j(f))=D_+(\beta_i(f))$ and on each such chart the two ring maps in step 3 satisfy
$$\frac{\beta_j(a)}{\beta_j(f)^m}=\frac{u^{nmd}\beta_i(a)}{(u^{nd}\beta_i(f))^m}=\frac{\beta_i(a)}{\beta_i(f)^m}\qquad(a\in A_{md}).$$
The equality only cancels powers of the unit $u$, using the localization fractions of [def-nagata-homogeneous-localization-degree-zero]; it does not cancel $f$. For $n=0$ both powers are $1$.

### Old step 6

The same local formulas respect restrictions of the affine base. For an affine $V\subseteq U_i$, the module map sends $v$ to $v\otimes(e_i|_V)^{\otimes n}$; this is the restriction of $\tau_i$. Its symmetric-algebra map therefore restricts $\beta_i$ by uniqueness in [lem-weil-pbc-quasi-coherent-symmetric-algebra]. On Proj charts, coefficient restriction $\rho$ sends $\beta_i(a)/\beta_i(f)^m$ to $\rho\beta_i(a)/\rho\beta_i(f)^m$, equal to applying the restricted algebra map after restriction. This is exactly the compatibility with the restriction maps specified in [def-nagata-relative-proj]. It also holds for the inverse maps. Thus the restriction of $g_i$ to $V$ is the map constructed there from $e_i|_V$.

### Old step 7

Cover each $U_i\cap U_j$ by affine opens using [lem-weil-pbc-affine-opens-basis]. Steps 5 and 6, equality of affine spectrum maps [def-weil-affine-spectrum], and the covering by standard charts [prop-nagata-proj-standard-open] show that $g_i$ and $g_j$ agree on each of these restrictions; uniqueness in [lem-weil-pbc-scheme-morphism-gluing] gives agreement on the whole overlap. Apply that lemma to glue $g_i$ to $g:\mathbf P_S(\mathcal E')\to\mathbf P_S(\mathcal E)$. Their inverses agree on the corresponding overlaps, so they glue too, and the two composites are identities by local uniqueness. The equality of the structure morphisms holds locally because each $g_i$ is over $U_i$, hence globally by the same uniqueness. Any other cover and any other local generators compare on affine refinements by steps 5 and 6, so give the same $g$. Its inverse is the requested canonical isomorphism $\mathbf P_S(\mathcal E)\cong\mathbf P_S(\mathcal E')$ over $S$, with the projective-bundle meanings in [def-trf-projective-bundle-morphism].
