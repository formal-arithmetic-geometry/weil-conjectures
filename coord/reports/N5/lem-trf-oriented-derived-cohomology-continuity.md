# Worker report

## Files written

- lem-trf-oriented-derived-cohomology-continuity — statement; split into eight proof steps; no Mathlib match in the inherited searches.
- lem-trf-oriented-triple-limit-descent — new statement-only node; no Mathlib match after LeanFinder, Loogle, LeanSearch, grep, and a second wording.
- citations.json — verbatim statement excerpts for every cited node in every item proof step.

## Attachments

None. The exact blueprint tag has no declaration under WeilConjectures. The closest source declaration, AlgebraicGeometry.Etale.isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit at WeilConjectures/AlgebraicGeometry/Sites/CohomologyContinuity.lean:51, ends in sorry and states only ordinary etale vanishing, so it neither finishes nor states this oriented-product comparison. No exact declaration for the new site-descent statement was found.

## WANTED

None. I used the local ILO PDF and local Stacks source.

## What needed repair

The imported item had an empty proof. Its statement is preserved verbatim. The first draft's spectral-sequence sentence did not supply all its comparisons; I replaced it by an induction on canonical truncations using existing generic nodes. I removed the application of a directed-preorder-only homology theorem to a general filtered category, and added the missing constant-module forgetting and adjunction-normalization statements. The new node has no proof or proof dependencies. Its site-model conclusion includes coherent strictification, rather than demanding literal functorial identities from arbitrary chosen skeletal fibre products.

The source of the item describes the localized coherent-topos situation. This proof supplies its general affine-transition geometric realization via a concrete finite-data site lemma and the existing Stacks finite-cover cohomology-colimit theorem; it does not cite an SGA result. The unit's normal-cone/local-term route is unchanged. The item is not the unit's key node, so no unit record is edited.

## Unfinished work

None for this one-level split. The new child remains unsplit, as required; its own eventual proof must construct the concrete descent and site models. No Lean was written and no compiler was run.

## Review by N5

I read ILO Exposé XI 2.5 and 2.7, including (2.c) and the verification (*) following (2.f), printed pp. 179–180. XI 2.5 constructs the finite-cover triple presentation; XI 2.7 localizes it by inverse limits and identifies the resulting cohomological map with functorial pullback. I also read Stacks sites.tex 09YL (lemma-colimit-sites), 0A35 (lemma-compute-pullback-to-limit), sites-cohomology.tex 09YP (lemma-colimit), limits.tex 01ZM (lemma-descend-finite-presentation) and 07RP (lemma-descend-etale). These last two are the geometric descent input, not an already proved oriented cohomology theorem. The new statement records finite geometric triple data and a site presentation only; it asserts no cohomology isomorphism. General cofiltered indexing can be reduced using the existing filtered-category-directed-cofinal statement, and descent is simultaneous for the finitely many component objects and maps. The two structural triple maps are descended as maps into the pulled-back finite-presentation middle objects; their relations are detected later. Coverings of type (a)/(b) require eventual joint surjectivity, while type (c) is a finite diagram with a specified factorization, so finite composite covers are also finite data. This is why the child is a real geometric lemma and does not duplicate the abstract colimit-site theorem.

For step 1 I checked the statement of initial-functor-cofiltered-criterion, including its slice clause. A common predecessor supplies the required nonempty comma object, and equalizing two arrows in I gives an arrow of the slice after composing with the fixed map to i0. Applying the colimit clause in an opposite target category gives the unchanged component limits. This checks the indexing category, rather than silently replacing a category by an ordered tail.

For step 2 I opened qcqs-oriented-triple-presentation, oriented-triple-limit-descent and colimit-of-sites. The first explicitly has a terminal triple, finite covering refinements, restriction equivalence and representable base change. The child supplies strict continuous cover-preserving site functors, object/arrow colimits and exactly the transported finite coverings; those are precisely the abstract theorem's hypotheses. Its third clause identifies the site inverse images with the stated geometric morphisms, including units. Thus no definition node is being used as a comparison theorem.

For step 3 the cohomology-colimit-of-sites statement explicitly gives all p>=0, arbitrary abelian sheaves, and the actual adjunction-unit map. I checked that the compatible coefficient system is the canonical pullback of F, and after inverse image to the limit it is isomorphic to a constant diagram. The connected-constant-colimit node therefore identifies its colimit with F at the limit. Taking the terminal triple computes global sections; the single-object-derived identification and negative-vanishing nodes give the sheaf case in all integer degrees. I did not assume a module result from an abelian-sheaf statement.

For step 4 the ring-sheaves-Grothendieck node, applied to the constant integer ring, provides the category hypothesis; Grothendieck-K-injective supplies resolutions. The two triangulated-functor nodes say respectively that a right derived functor preserves distinguished triangles and that an exact functor descends termwise as a triangulated functor. The derived-adjunction-shift node is for arbitrary small ringed topoi with commutative coefficients, hence applies to the constant integer sheaf. Composition-adjunction-normalization says the derived units are the composite units. Its K-injective normalization and shift compatibility make the canonical pullback a morphism of triangles, so the cohomology-ladder node applies to the actual boundary maps.

For step 5 I checked the full truncation-triangle, filtered-colimit-exactness and five-lemma statements. The induction assertion is comparison in every degree, with base tau<=a-1 equal to zero, and the inductive third term a single shifted cohomology sheaf already handled by step 3. Thus each adjacent comparison needed by the five lemma is available. Exact inverse images preserve the kernels, images and quotient defining good truncation. Filtered-colimit-exactness is stated for any small filtered category, including the opposite refinement slice, so there is no hidden directed-preorder restriction. For step 6 the derived-functor-truncation-iso statement says explicitly that degree n of Rv sees tau<=n. Negative-vanishing supplies the case n<a. These checks require neither finite cohomological dimension nor inverse images of injectives to be acyclic.

For step 7 I checked constant-left-module-inverse-image and left-module-derived-evaluation-forget. They allow an arbitrary constant unital ring, identify forgotten pullback with abelian pullback, and explicitly preserve units and global-cohomology pullbacks on sites with terminal objects. Hence they apply to this commutative Lambda without any torsion or finite-generation assumption. Underlying filtered module colimits and reflection of isomorphisms are elementary: their elementwise action and inverse are written in the step. In step 8 the sheaf-pullback node supplies the naturality and composition equations, and derived-composition-normalization supplies the same unit equations on complexes. All maps being checked were the canonical unit maps from the start, so the result includes naturality in K, restriction of systems, and unit compatibility.

I tested the new statement on constant diagrams (all site comparisons are identities), the identity inverse system over a singleton, empty schemes (the empty covering is retained), non-separated qcqs schemes (the identity etale morphism is separated and gives the terminal triple), and a limit in which a finite covering is surjective only after going forward. The last case requires eventual covering descent, not an assertion at its original stage. Affine-only input sites would lose the terminal triple for a non-affine scheme, so the new statement uses the existing separated-etale-finite-presentation sites instead. I also checked zero complexes, negative degree below the common lower bound, and a single shifted sheaf in the item proof.

Against delivery-errors B–E: the child is self-contained, statement-only, with notion dependencies, source labels/tags, and actual logged searches. The item statement is unchanged; no axiom or coefficient hypothesis is introduced. The proof is an argument in eight steps rather than applying a cohomology restatement. All cited statements were read; citations.json copies their actual supporting text. Every step is shorter than 2000 characters. The generic off-unit category/site/derived tools are declared in split_report.tool_uses because the unit supplies no replacement for them. The duplicate comparisons below record the distinct scope of the source-tag hits.

## Not duplicates

lem-trf-oriented-triple-limit-descent vs affine-open-etale-map-factorization: the existing statement, Étale morphism factorization from the affine limit, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs affine-open-inverse-image-unit-representatives: the existing statement, Unit representatives of terminal inverse-image sections, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs affine-open-sections-descent: the existing statement, Descent of affine-limit sections, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs affine-open-sections-zero-detection: the existing statement, Finite-stage detection of zero affine sections, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs aux-colimit-site-stage-image-cover-amalgamation: the existing statement, Existence of stage-image amalgamations on a mapped finite stage cover, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs aux-colimit-site-stage-image-local-isSheafFor: the existing statement, Each Grothendieck covering sieve has the stage-image sheaf condition, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs def-cbc-affine-etale-cech-system: the existing statement concerns ordinary affine etale sites of ONE system of schemes, with the affine-site hypotheses it explicitly lists; the new statement concerns the finite-cover oriented TRIPLE sites of three systems and their factorization covers, including non-affine terminal triples.

lem-trf-oriented-triple-limit-descent vs def-weil-pbc-arrows-functor: the existing statement, The functor taking a category to its set of arrows, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs def-weil-pbc-colimit-site-abelian-stage-image: the existing statement, Abelian subpresheaf generated by restrictions of stage images, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs def-weil-pbc-colimit-site-stage-image: the existing statement, Stage-image subpresheaf of the limit inverse image, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs def-weil-pbc-filtered-colimit-hom-fibers: the existing statement, Hom fibers in the filtered arrow colimit, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs def-weil-pbc-finite-precoverage: the existing statement, Finite indexed precoverage closure axioms, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-cbc-affine-cech-system-cocycle-lift: the existing statement, Cocycles in finite affine Čech systems lift to one stage, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-cbc-affine-comparison-cech-cocycle-descent: the existing statement, Finite affine comparison Cech cocycles descend to etale Cech complexes, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-cbc-affine-etale-cech-presentation: the existing statement concerns ordinary affine etale sites of ONE system of schemes, with the affine-site hypotheses it explicitly lists; the new statement concerns the finite-cover oriented TRIPLE sites of three systems and their factorization covers, including non-affine terminal triples.

lem-trf-oriented-triple-limit-descent vs lem-cbc-affine-etale-cover-presentation: the existing statement concerns ordinary affine etale sites of ONE system of schemes, with the affine-site hypotheses it explicitly lists; the new statement concerns the finite-cover oriented TRIPLE sites of three systems and their factorization covers, including non-affine terminal triples.

lem-trf-oriented-triple-limit-descent vs lem-cbc-cech-nerve-presentation-construction: the existing statement, Compatible base and member presentations present every Čech intersection, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-cbc-ordered-cech-ulift-comparison: the existing statement, Categorical and ordered Čech complexes agree after ULift reindexing, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-kun-descent-limit-open: the existing statement, Descent of a quasi-compact open in an affine limit, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-nagata-one-affine-subring-extension: the existing statement, One-affine-open extension of exhaustive finite subring models, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-pbc-affine-etale-common-models: the existing statement concerns ordinary affine etale sites of ONE system of schemes, with the affine-site hypotheses it explicitly lists; the new statement concerns the finite-cover oriented TRIPLE sites of three systems and their factorization covers, including non-affine terminal triples.

lem-trf-oriented-triple-limit-descent vs lem-pbc-affine-etale-model-arrows: the existing statement concerns ordinary affine etale sites of ONE system of schemes, with the affine-site hypotheses it explicitly lists; the new statement concerns the finite-cover oriented TRIPLE sites of three systems and their factorization covers, including non-affine terminal triples.

lem-trf-oriented-triple-limit-descent vs lem-pbc-affine-etale-pullback-arrow-comparison: the existing statement concerns ordinary affine etale sites of ONE system of schemes, with the affine-site hypotheses it explicitly lists; the new statement concerns the finite-cover oriented TRIPLE sites of three systems and their factorization covers, including non-affine terminal triples.

lem-trf-oriented-triple-limit-descent vs lem-pbc-finite-pullback-hom-descent: the existing statement, Finite family descent of pullback morphisms, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-pc-bounded-complex-base-change-enlargement: the existing statement, Functorial enlargement of a bounded finitely presented complex, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-pc-proper-flat-single-noetherian-descent: the existing statement, Geometric Noetherian descent for a proper flat finite-presentation module, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-pd-finite-separable-datum-refinement: the existing statement, Refinement carrying a descent datum, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-pd-finite-separable-scheme-model: the existing statement, Finite separable scheme models, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-pd-finite-separable-universal-transport-model: the existing statement, A finite model of universal transport, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-affine-diagram-smooth-stage: the existing statement, Smoothness of a fixed affine model over an affine inverse system, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-affine-limit-smooth-stage: the existing statement, Eventual smoothness over an arbitrary affine-transition limit, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-affine-section-noetherian-descent: the existing statement, Affine noetherian descent with a compatible section, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-affine-source-limit-smooth-stage: the existing statement, Eventual smoothness for an affine source chart, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-dominant-finite-refinement-limit: the existing statement, Dominant finite integral refinements preserve an approximation limit, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-galois-cover-base-change: the existing statement, Finite Galois torsors admit base change, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-galois-cover-stage-descent: the existing statement, Unpointed finite Galois torsors descend along affine inverse limits, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-generic-fibre-iso-spread-base-open: the existing statement, Descending a whole generic-fibre isomorphism to a base open, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-generic-fibre-partial-iso-spread-open: the existing statement, Spreading a generic-fibre partial isomorphism to a common open, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-generic-open-finite-etale-model: the existing statement, Generic open finite etale model, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-noetherian-approximation-smooth-stage: the existing statement, Eventual smoothness of a noetherian stage model, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-noetherian-approximation-smooth-stage-affine-model: the existing statement, Affine smooth model in a noetherian approximation, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-noetherian-approximation-smooth-stage-gluing: the existing statement, Gluing affine smooth models at a common stage, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-pointed-galois-cover-limit-descent: the existing statement, Pointed finite Galois torsors descend along affine inverse limits, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-pointed-section-stage-descent: the existing statement, Maps to a finitely presented scheme descend over a fixed stage, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-pointed-smooth-family-stage: the existing statement, Descent of a pointed smooth family and invertible integer to one stage, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-section-component-noetherian-model: the existing statement, Local noetherian model for a section component, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sbc-smooth-pushout-filtered-colimit-stage: the existing statement, Eventual smoothness of a fixed finitely presented ring map after pushout, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-sbc-smooth-section-component-noetherian-model-data: the existing statement, Existence of local noetherian model data, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sc-cofiltered-affine-etale-model: the existing statement concerns ordinary affine etale sites of ONE system of schemes, with the affine-site hypotheses it explicitly lists; the new statement concerns the finite-cover oriented TRIPLE sites of three systems and their factorization covers, including non-affine terminal triples.

lem-trf-oriented-triple-limit-descent vs lem-sc-generic-pointed-etale-cofinality: the existing statement, Initiality of generic base change on pointed etale neighbourhoods, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-sc-generic-pointed-etale-extension: the existing statement, Extension of pointed etale neighbourhoods from the generic point, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-trf-oriented-derived-cohomology-continuity: the item asserts bounded-below cohomology continuity and its naturality; the child asserts only finite geometric data descent and a colimit-site presentation, with no cohomological conclusion.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-affine-chart-directed-ring-model: the existing statement, Coordinate-ring comparisons for one affine triple, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-affine-chart-tensor-comparison: the existing statement, Uniform tensor-product arrow comparison for a fixed affine triple, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-affine-etale-colimit-presentation: the existing statement concerns ordinary affine etale sites of ONE system of schemes, with the affine-site hypotheses it explicitly lists; the new statement concerns the finite-cover oriented TRIPLE sites of three systems and their factorization covers, including non-affine terminal triples.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-affine-etale-finite-colimit-construction: the existing statement concerns ordinary affine etale sites of ONE system of schemes, with the affine-site hypotheses it explicitly lists; the new statement concerns the finite-cover oriented TRIPLE sites of three systems and their factorization covers, including non-affine terminal triples.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-affine-etale-finite-diagram-descent: the existing statement concerns ordinary affine etale sites of ONE system of schemes, with the affine-site hypotheses it explicitly lists; the new statement concerns the finite-cover oriented TRIPLE sites of three systems and their factorization covers, including non-affine terminal triples.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-affine-etale-site-colimit: the existing statement concerns ordinary affine etale sites of ONE system of schemes, with the affine-site hypotheses it explicitly lists; the new statement concerns the finite-cover oriented TRIPLE sites of three systems and their factorization covers, including non-affine terminal triples.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-chow-finite-type: the existing statement, Chow's lemma for separated morphisms of finite type over a qcqs base, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-of-sites: the existing theorem STARTS with an abstract strict site system and constructs its colimit; the new lemma verifies geometric triple-data descent and identifies that abstract colimit with the finite triple site of the componentwise scheme limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-of-sites-cech-complex: the existing statement, The Cech complex of the colimit sheaf on a colimit of sites is the colimit of the Cech complexes, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-of-sites-cech-complex-transport: the existing statement, Transport of finite covering products, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-of-sites-reduced: the existing statement, Category colimit site construction after category witness, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-of-sites-sections: the existing statement, Sections of the colimit sheaf on a colimit of sites (degree 0), assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-presieve-indexed-presentation: the existing statement, Finite presieve reindexing over a fixed stage target, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-abelian-cover-section-lift: the existing statement, Individual lifts of generated abelian sections on a stage cover, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-abelian-finite-family-stabilization: the existing statement, Stabilization of finite abelian stage families, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-abelian-finite-family-stabilization-nonempty: the existing statement, Nonempty finite abelian family stabilization, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-abelian-finite-indexed-matching: the existing statement, Finite indexed matching at a common stage transition, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-abelian-finite-object-section-lift: the existing statement, Simultaneous lifts of generated abelian sections at prescribed stage objects, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-abelian-inverse-image: the existing statement, Abelian inverse-image section formula, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-abelian-kan-unit-relations: the existing statement, Eventual equality of abelian Kan unit images, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-abelian-pairwise-eventual-matching: the existing statement, One eventual equality between covering restrictions, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-abelian-section-diagram: the existing statement, Coherent diagram of abelian stage sections, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-abelian-section-eventual-equality: the existing statement, Eventual equality of abelian inverse-image sections, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-abelian-section-representatives: the existing statement, Stage representatives of abelian inverse-image sections, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-abelian-section-universality: the existing statement, Universality of the abelian stage-section cocone, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-abelian-stage-image-refinement: the existing statement, Finite stage-image expressions have forward-stage representatives, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-abelian-stage-image-sheaf: the existing statement, Sheaf condition for the stage-generated abelian subpresheaf, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-abelian-stage-matching-lift: the existing statement, Matching lifts of generated abelian sections on a stage cover, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-abelian-unit-kernel-bound: the existing statement, Raw section-formula bound on the source-unit kernel, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-covering-axioms: the existing statement, Finite covering axioms for the transported precoverage, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-covering-axioms-finitebasechange: the existing statement, Finite base change in the colimit precoverage, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-covering-axioms-finitecomposition: the existing statement, Finite composition in the colimit precoverage, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-covering-axioms-hasisos: the existing statement, Singleton isomorphisms cover in the colimit precoverage, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-covering-axioms-haspullbacks: the existing statement, Covering pullbacks exist in the colimit category, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-covering-construction: the existing statement, Finite covering axioms and continuity on a fixed category colimit, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-covering-continuity: the existing statement, Continuity and pullback preservation for the transported precoverage, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-covering-families-at-stage: the existing statement, Finite one-layer covering lifting over fixed stage targets, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-covering-families-lift: the existing statement, Simultaneous finite covering-family lifting, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-covering-pullback-stage-presentation: the existing statement, Common stage presentation of prescribed covering pullback squares, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-finite-kan-arrow-lift: the existing statement, Finite Kan arrow diagrams lift simultaneously above their stage, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-finite-restriction-family-lift: the existing statement, Finite restriction arrows and triangles lift at one refinement, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-finite-section-colimit-presentation: the existing statement, Finite-site section colimit presentation compatible with all source units, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-finite-section-comparison-bijective: the existing statement, Bijectivity of the comparison for a supplied coherent finite-site section cocone, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-finite-section-eventual-zero: the existing statement, Eventual vanishing of a stage section in the supplied cocone, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-finite-unit-zero-detection: the existing statement, Source-unit zero detection with finite indexed covering axioms, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-kan-unit-relations: the existing statement, Single-stage Kan unit relations vanish after refinement, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-abelian-section-diagram: the existing statement, Raw abelian stage Kan-extension diagram and compatible comparison, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-abelian-section-evaluation: the existing statement, Raw abelian presheaf colimit evaluation at a carried object, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-abelian-section-generators: the existing statement, Stage representatives of raw abelian Kan sections, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-abelian-section-relations: the existing statement, Eventual equality of raw abelian section representatives, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-abelian-section-sheaf: the existing statement, Sheaf condition for the raw abelian stage Kan-extension colimit, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-abelian-stage-restriction: the existing statement, Raw abelian stage restriction as a filtered colimit of stage sheaves, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-finite-equality-stabilization: the existing statement, Finite equality detection for raw stage section representatives, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-finite-matching-refinement: the existing statement, Refinement of finite raw-compatible stage sections, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-finite-sections-lift: the existing statement, Finite simultaneous representatives of raw sections, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-section-amalgamation: the existing statement, Raw section amalgamation on images of stage covers, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-section-compatibility: the existing statement, Compatibility isomorphism for the raw section colimit presentation, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-section-diagram: the existing statement, Raw stage Kan-extension diagram and compatible comparison, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-section-evaluation: the existing statement, Raw presheaf colimit evaluation at a represented object, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-section-generators: the existing statement, Stage representatives in the raw Kan section colimit, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-section-matching-lift: the existing statement, Finite compatible stage lifts of raw matching families, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-section-presentation: the existing statement, Canonical raw presheaf colimit presentation at a represented object, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-section-relations: the existing statement, Eventual equality of raw Kan section representatives, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-section-separated: the existing statement, Raw section separated on images of stage covers, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-section-sheaf: the existing statement, Sheaf condition for the raw stage Kan-extension colimit, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-raw-stage-restriction: the existing statement, Raw stage restriction as a filtered colimit of stage sheaves, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-set-evaluation-presentation: the existing statement, Filtered presentation of each inverse-image evaluation functor, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-set-inverse-image: the existing statement, Set inverse-image section formula and finite-limit preservation, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-set-section-coherence: the existing statement, Unit-compatible section maps satisfy the functor and cocone laws., assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-set-section-eventual-equality: the existing statement, Equal stage-section images become equal after one refinement., assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-set-section-presentation: the existing statement, Section colimit for specified unit-compatible maps, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-set-section-representatives: the existing statement, Every limit inverse-image section is represented by a stage section., assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-stage-image-refinement: the existing statement, Refine a restricted stage image over an image object, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-stage-image-sheaf: the existing statement, The stage-image subpresheaf is a sheaf, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-stage-section-diagram: the existing statement, Functorial inverse-image section diagram over an under category, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-site-unit-zero-detection: the existing statement, Zero detection for a single colimit-site inverse-image unit, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-sites-degree-zero-descent: the existing statement, Degree-zero finite-stage existence on a colimit of sites, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-stage-abelian-kan-cocone: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-stage-kan-cocone: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-colimit-stage-kan-relations: the existing statement, Eventual equality of compatible stagewise Kan representatives, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-constructible-module-limit-descent: the existing statement, A constructible sheaf of $\Lambda$-modules on a limit of qcqs schemes descends to some stage (Stacks 09YU (3), essential surjectivity), concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-descend-etale: the existing statement, Etaleness descends to a finite stage of a limit, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-descend-monomorphism: the existing statement, Monomorphisms descend to a stage under a locally finite type hypothesis, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-etale-affine-chart-descent: the existing statement, Étale descent and persistence on one affine triple, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-etale-finite-cover-factorization-descent: the existing statement, Finite affine covering descent with auxiliary factorizations, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-etale-finite-data-descent: the existing lemma descends finite etale diagrams over ONE inverse system of base schemes indexed by a directed set; the new lemma handles triples over THREE different changing bases, their structural maps and the type-(c) factorization covers, and constructs the coherent colimit-site presentation.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-etale-finite-factorization-data-descent: the existing statement, Simultaneous affine etale source and two-arrow descent without coverings, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-etale-limit-finite-cover-descent: the existing statement, Descent of a finite qcqs etale covering, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-etale-limit-finite-diagram-descent: the existing statement, Finite qcqs etale star diagrams descend to a common stage, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-filtered-colimit-categories: the existing statement, The filtered colimit of a system of categories; finite diagrams and morphisms come from a stage, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-filtered-colimit-category-descent: the existing statement, Finite-diagram and Hom descent from the object and arrow colimits, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-filtered-colimit-category-finite-functor-lift: the existing statement, Construct a finite functor from finite-list lifts, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-filtered-colimit-category-finite-lift: the existing statement, Finite object and arrow lists lift with relations, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-filtered-colimit-category-iso: the existing statement, Invertible representatives from lifting finite functors, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-filtered-colimit-category-list-equality: the existing statement, Finite object and arrow lists agree at a common refinement, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-filtered-colimit-category-structure: the existing statement, The category structure induced on the filtered object colimit, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-filtered-colimit-fiber-laws: the existing statement, Category axioms for filtered arrow fiber operations, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-filtered-colimit-fiber-operations: the existing statement, Identity and composition on filtered arrow fibers, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-filtered-colimit-finite-iso-lift: the existing statement, Finite isomorphisms lift above fixed stage objects, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-filtered-colimit-functor-descent: the existing statement, Descent of compatible functors from an object-and-arrow filtered colimit, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-filtered-colimit-iso-presieve-representation: the existing statement, Isomorphisms in the filtered colimit category have covering stage representatives, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-filtered-colimit-preserves-pullback: the existing statement, A pullback stable at later stages is preserved in the category colimit, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-filtered-colimit-pullback-exists: the existing statement, Factorization existence for a stable pullback image, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-filtered-colimit-pullback-hom-ext: the existing statement, Joint monicity of stable pullback image projections, assumes abstract category/site/section diagrams or their colimit witnesses; it does not prove geometric descent for the three changing scheme bases or identify the oriented triple site of their limits.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-finite-diagram-lift-of-models: the existing statement, Finite diagram arrows and relations lift after object models are chosen, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-finite-etale-algebra-stage: the existing statement, Finite etale descent to a finitely presented algebra stage, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-finite-etale-lifting-limit-descent: the existing statement, Reduction of finite etale lifting over a henselian pair to Noetherian henselian G-ring pairs, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-finite-etale-lifting-limit-descent-core: the existing statement, Limit descent with compatibility witness, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-inverse-image-degree-zero-representative: the existing statement, Finite-stage representatives for one inverse-image sheaf, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-proper-limit-noetherian: the existing statement, A proper morphism is a limit of proper morphisms over schemes of finite type over Z, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-proper-noetherian-stage: the existing statement, A proper finitely presented scheme descends to one proper Noetherian stage, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-sets-eventual-local-stage-matching: the existing statement, Eventual matching of a finite local stage family, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-sets-eventual-local-stage-matching-compatibility: the existing statement, EtaleSetEventualLocalStageCompatibility, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-sets-finite-local-stage-representatives: the existing statement, Finite affine local representatives at a common stage, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-sets-stage-presheaf-locally-injective: the existing statement, Local injective of the stage presheaf comparison, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-sets-stage-presheaf-locally-surjective: the existing statement, Local surjective of the stage presheaf comparison, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-sets-stage-sheaf-colimit: the existing statement, Stage inverse-image sheaf colimit on the affine site, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-stage-section-functor-from-transitions: the existing statement, Section functor from transition maps, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-stage-section-transition-existence: the existing statement, Existence of stage transition maps, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-varying-site-intermediate-unit-zero: the existing statement, Zero of the intermediate section under a later stage unit, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-varying-site-inverse-image-zero-detection: the existing statement, Finite-stage zero detection inside an inverse image, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs lem-weil-pbc-varying-site-sections-zero-detection: the existing statement, Finite-stage zero detection for sections of a varying-site sheaf system, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs new-constructible-limit-descent-general: the existing statement, Constructible limit descent for Noetherian coefficient modules, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs new-def-sbc-etale-triples-prime-localization-cocone-relation: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs new-lem-sbc-etale-triples-prime-localization-cocone-equiv: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs new-lem-sbc-etale-triples-prime-localization-cocone-extension: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs new-lem-sbc-etale-triples-prime-localization-cocone-restriction: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs new-lem-sbc-etale-triples-prime-localization-comparison: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs new-lem-sbc-etale-triples-prime-localization-component-extension: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs new-lem-sbc-etale-triples-prime-localization-component-extension-aux: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs new-lem-sbc-etale-triples-prime-localization-component-extension-aux-factorization: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs new-lem-sbc-etale-triples-prime-localization-component-extension-aux-model: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs new-lem-sbc-etale-triples-prime-localization-component-extension-aux-model-pointing: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs new-lem-sbc-etale-triples-prime-localization-component-extension-aux-model-structure: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs new-lem-sbc-etale-triples-prime-localization-component-extension-exists: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs new-lem-sbc-etale-triples-prime-localization-component-extension-unique: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux-compatible: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux-epi: the existing statement concerns prime-localized/pointed etale models in the smooth-base-change construction; it does not construct the finite oriented-product triple site or its type-(c) covering descent for general qcqs diagrams.

lem-trf-oriented-triple-limit-descent vs new-lem-sbc-prime-localization-etale-algebra-model: the existing statement, Unpointed etale algebra model at a prime, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs thm-pd-spreading-out: the existing statement, Descent of finitely presented data at a filtered limit, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.

lem-trf-oriented-triple-limit-descent vs thm-pqf-immersion-descent: the existing statement, Descent of the immersion to a finite stage, concerns ordinary scheme/algebra finite-presentation descent or its particular geometric application; it does not identify the colimit of oriented triple sites, their three covering types and their geometric inverse images.
