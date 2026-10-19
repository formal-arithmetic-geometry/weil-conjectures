# Stage-1 report: lem-per-noetherian-ctf-flat-model

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-ctf-flat-model.json: statement; split into six proof steps; no exact Mathlib match. Its statement is unchanged.
- dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-constructible-flat-lifting.json: statement; unsplit; no Mathlib match. Finite affine-free lifting covers for arbitrary Noetherian coefficient rings.
- dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-constructible-galois-partition.json: statement; unsplit; no Mathlib match. Simultaneous finite Galois partitions for finite families of constructible modules, with finitely presented values, without flatness.
- citations.json: one verbatim cited-statement quotation per item-step citation. The append-only searches.jsonl was retained, read, and extended by one corrected Loogle search. No Lean files, library, tools, chapter records, unit records, or other existing nodes were changed.

## Attachments

DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn_of_liftsAlongEpi belongs to lem-sf-flat-model-class-resolution (already attached; WeilConjectures/CategoryTheory/DerivedCategory/FlatModelOfClass.lean:72).

AlgebraicGeometry.Scheme.constantSheaf_geometricStalk_isIso belongs to lem-weil-pbc-constant-sheaf-geometric-stalk (already attached; WeilConjectures/AlgebraicGeometry/ConstantSheafGeometricStalk.lean:29).

No attachment for the item or its two new nodes. The nearby AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatConstructibleModel at WeilConjectures/SixFunctors/Etale/Derived/Finiteness/FlatModel.lean:160 and liftsAlongEpi_flat_isConstructibleSheaf at line 119 both assume [Finite Λ]. The item allows A=F_ell[t], so neither declaration proves its full statement. The generic class-resolution declaration does not supply the constructible class hypotheses or the Galois/projective conclusion by itself.

## Wanted literature

None. All source documents used below are present locally.

## Findings and corrections

This continuation retained the previous draft, citations, and all searches. No delivery process was active and no report or successful-delivery receipt was present when work resumed. An early server review_split check passed. The repository item remains unsplit, with no intervening statement change; the sandbox adds its proof and two smaller inputs.

The item genuinely needs Noetherian coefficients, not finite underlying sets. Finite-coefficient constructibility/generation declarations and nodes do not attach it. The source Stacks 03TT is stated for a Noetherian coefficient ring on a qcqs scheme and explicitly preserves the specified Tor interval. Its following remark asserts finite projectivity of stalks. The hypothesis that X is Noetherian is stronger than qcqs and is sufficient. No invertibility of ell on X is needed for this flat-model result.

The reconstruction of a bounded model uses the already existing generic class-resolution theorem: it constructs a bounded-above lifting-class resolution, then truncates by the degree-a cokernel, whose flatness follows from Tor vanishing. Thus no assumption that a flat sheaf is a projective object of the global sheaf category, or that an arbitrary derived morphism between these complexes is a chain map, is hidden in the proof. The Stacks 03TT proof has omitted details and inconsistent degree indices in its final reconstruction paragraph; those lines are not copied as a proof.

I expanded the comparison of local and global constructible partitions: a finite affine cover is disjointized as W_i=U_i minus the preceding opens, then intersected with its local strata. I rewrote the flat-stalk argument by pulling the flat sheaf first to V_i and then to a point of V_i. This avoids an unstated inverse-image/stalk comparison. The constant-stalk isomorphism used is additive in its cited statement; the step explicitly checks A-linearity by scalar multiplication of constant sections. The Galois source reference 03SF was corrected to pione.tex, section-finite-etale-under-galois, rather than a nonexistent etale-cohomology label. The old invalid Loogle pattern SheafOfModules, Epi is retained with an invalid-query verdict, followed by the actual fully qualified search.

## Review by Q59

I read stages/1-dag.md, coord/brief-stage1.md, the three permitted blueprint levels in SETUP.md, GOAL.md, coord/dag-sync.md, and coord/delivery-errors.md B--E. I read the chapter and unit records and the nearest blueprint ancestor lem-per-artin-gabber-affine-curve. This is a descendant input to its Step 1 arbitrary-field relative-duality chain, through the coefficient-comparison theorem; it changes no unit or chapter route. The item's source and both helper sources were read in the local Stacks TeX and ILO volume. The ancestry is recorded for each new node, and whole-blueprint searches for flat constructible, lifting, Galois and Galois partition found no matching arbitrary-Noetherian-coefficient node.

For the item I read etale-cohomology.tex, lemma-when-ctf (03TT), section-ctf and remark-projective-each-degree, and ILO XVII 7.3.1 (printed p.303), 7.6.11 and the proof of 7.6.1 (printed p.314). I also read the generic class-resolution source declaration and its actual proof in the read-only Lean checkout. Its source audit is closed. The proof_origin is deliberately agent: this split combines the source flat-model argument with the existing class-resolution interface and the Galois partition input, rather than claiming to transcribe a single document verbatim.

Step 1 uses lem-sfb-discrete-noetherian-constructible-serre exactly for zero, kernels, cokernels and extensions over a commutative Noetherian ring, on the small etale site. Its statement explicitly permits an infinite coefficient ring. It uses lem-weil-pbc-noetherian-submodule-finite for the kernel of a surjection A^n to a finitely generated module, proving finite presentation. The finite affine disjointization in the step supplies the local/global partition comparison; it is a finite intersection argument, not a further theorem. Conversely the global finite partition restricts to every affine open. Thus the Serre node's convention and this item's convention agree under the stated hypotheses.

Step 2 takes from lem-per-noetherian-constructible-flat-lifting the full lifting square p h = g e, including E flat and constructible and e epic. The biproduct and zero-class conditions are written out directly using the closure proved in Step 1 and additivity of tensor. This helper is not a clause of the derived flat-model theorem: it applies to arbitrary epimorphisms and maps of module sheaves, with no complex, interval or Tor bound at all. For its source I read the finite affine generators and standard-etale lifting refinements in the proof of 03TT, 095N (lemma-category-constructible-modules), and 03S8(3) (lemma-jshriek-constructible). These hold for Noetherian rings. The construction to be split later is: lift each finite generating section locally through p, choose finite affine refinements over each quasi-compact affine generator, and sum the corresponding j_!R. Their flatness is read on free geometric stalks; constructibility is supplied by 03S8(3). This construction, including local lifting and finite refinement, is not asserted by a definition of flatness. Its theorem remains statement-only in this delivery.

Step 3 cites lem-sf-flat-model-class-resolution. I opened its statement: it is for small-etale ModuleCat sheaves over any commutative ring, with T closed under kernels/cokernels/isomorphisms and S a zero/isomorphism/biproduct-closed flat subclass lifting epimorphisms onto T. Every such hypothesis is verified in Steps 1--2. H^n(K) lies in T by the item's definition. Its Tor hypothesis is against every degree-zero sheaf, exactly the hypothesis here. Its conclusion includes concentration in the actual interval [a,b], every term flat and in T, and an isomorphism after localization. No projectivity of sheaves or finite coefficient hypothesis is being imported.

Step 4 uses lem-per-noetherian-constructible-galois-partition for the finite family indexed by a<=q<=b, not for infinitely many resolution terms. That node's statement provides one common finite stratification with nonempty connected reduced strata, one connected finite etale Galois cover per stratum, and finitely presented constant values for every family member. It assumes neither flatness nor finite coefficient sets and does not assert any projectivity. For its source I read 095N and 03S0 (lemma-etale-stratified-finite), pione.tex 03SF (section-finite-etale-under-galois), and ILO XVII 7.3.1 and the cited pp.313--314. The future argument is finite affine-free presentations, common strata on which all presentation charts are finite etale, a common finite Galois splitting cover on each connected reduced stratum, and cokernels of constant matrices on that cover. Noetherianity of R converts the finite module values to finitely presented modules. In particular one must stratify before seeking finite monodromy: on a singular connected scheme, an arbitrary etale-locally constant infinite module sheaf need not already have finite monodromy. The helper includes that necessary stratification and is not using the finite-set Galois classification for an infinite module without a reduction.

Step 5 uses lem-weil-pbc-ringed-topos-flat-module-pullback exactly for flatness after each restriction and after pullback to a geometric point; its statement assumes no flatness of the coefficient-ring map. A point of the nonempty V_i exists, and the constant coefficient stalk is A. I checked the constant-stalk node's actual additive statement and supplied scalar compatibility explicitly in the step. The value M_iq is finitely presented by Step 4, hence lem-weil-pbc-finitely-presented-flat-module-projective applies without adding a hypothesis on A. The finite-free direct-summand description is the two-line projectivity lifting argument given in the step. I checked sites-modules.tex lemma-pullback-flat (05VD) and lemma-stalk-flat (05VB), and algebra.tex lemma-finite-projective (00NX). All three facts are represented by cited existing nodes; the specialized stalk use follows by applying the cited pullback statement to the point morphism.

Step 6 deals with X empty by the empty-cover sheaf axiom, then the zero complex and empty partition. It uses no substantial theorem. I tested a=b separately: the class-resolution theorem still applies and produces a single flat constructible term; this does not require an induction assumption. Zero sheaves and the zero coefficient ring also cause no exception. For X a point, flat finitely presented modules are projective, in agreement with the conclusion. For A=F_ell[t], the new helper hypotheses remain valid while the existing finite-ring declarations do not apply.

Both new nodes have self-contained statements, inline meanings for constructibility/flatness/finitely presented, their relevant definition nodes, statement-only unsplit status, and no proof or proof dependencies. Neither claims to be a Mathlib leaf. The earlier logged LeanSearch/LeanFinder/Loogle/grep results were retained and read; bounded-complex representatives and SheafOfModules local generators/finite presentations do not prove the etale constructible assertions. The corrected Loogle query returns GeneratingSections.ofEpi and its auxiliary declarations, which propagate existing generating sections through an epi; they do not construct the required finite constructible flat cover. No unavailable service is described as a negative mathematical result.

Every proof citation has a verbatim statement quotation in citations.json. I checked all uses against proof_deps and checked that no cited helper depends on this item. All six proof steps are shorter than 2000 characters; the substantive auxiliary inputs are named nodes, while finite biproduct exactness, scalar compatibility and the projective splitting are written out. The off-unit nodes are declared as generic tool uses in split_report, with their reasons. No source route through a prohibited SGA volume is used.

## Not duplicates

The comparison below includes every existing unmerged source-tag match in the shared snapshot, not merely a title search. The helper arguments described in this report are for later splitting and are not inserted into their statements.

lem-per-noetherian-constructible-flat-lifting vs lem-sf-etale-smooth-stratified-ctf: the existing statement gives smooth-stratum finite-tor devissage over an arbitrary algebraically closed field; it asserts no common finite Galois cover trivializing an arbitrary finite family of module sheaves.

lem-per-noetherian-constructible-flat-lifting vs lem-trf-constructible-generator-epimorphism: the existing statement proves finite etale free generators lift epimorphisms onto constructible sheaves with finite-coefficient or scheme-limit/colimit input; it does not give flat constructible lifting of every map from a constructible module along an arbitrary epimorphism for an arbitrary Noetherian ring.

lem-per-noetherian-constructible-flat-lifting vs lem-trf-constructible-etale-finite-affine-syzygy: the existing statement proves finite affine-free syzygies of constructible etale modules with finite-coefficient or scheme-limit/colimit input; it does not give flat constructible lifting of every map from a constructible module along an arbitrary epimorphism for an arbitrary Noetherian ring.

lem-per-noetherian-constructible-flat-lifting vs lem-per-noetherian-ctf-flat-model: the existing item starts from a finite-Tor derived object and constructs a bounded model; the helper concerns arbitrary sheaf epimorphism lifting, with no complex or amplitude hypothesis.

lem-per-noetherian-constructible-flat-lifting vs lem-weil-pbc-constructible-module-finite-stalks: the existing statement proves the geometric stalks of a constructible sheaf of modules are finite with finite-coefficient or scheme-limit/colimit input; it does not give flat constructible lifting of every map from a constructible module along an arbitrary epimorphism for an arbitrary Noetherian ring.

lem-per-noetherian-constructible-flat-lifting vs lem-weil-pbc-constructible-module-finite-zero-cokernel: the existing statement proves finite affine free cover with zero cokernel with finite-coefficient or scheme-limit/colimit input; it does not give flat constructible lifting of every map from a constructible module along an arbitrary epimorphism for an arbitrary Noetherian ring.

lem-per-noetherian-constructible-flat-lifting vs lem-weil-pbc-constructible-module-finite-presentation: the existing statement proves a constructible sheaf of modules on a qcqs scheme is a cokernel of a map between finite sums of extensions by zero of lambda from affine etale objects with finite-coefficient or scheme-limit/colimit input; it does not give flat constructible lifting of every map from a constructible module along an arbitrary epimorphism for an arbitrary Noetherian ring.

lem-per-noetherian-constructible-flat-lifting vs lem-weil-pbc-affine-free-etale-module-arrow-descent: the existing statement proves arrows between finite sums of affine etale free module sheaves descend with finite-coefficient or scheme-limit/colimit input; it does not give flat constructible lifting of every map from a constructible module along an arbitrary epimorphism for an arbitrary Noetherian ring.

lem-per-noetherian-constructible-flat-lifting vs lem-weil-pbc-constructible-large-colimit-factorization: the existing statement proves constructible-source factorization into filtered colimits at the coefficient universe with finite-coefficient or scheme-limit/colimit input; it does not give flat constructible lifting of every map from a constructible module along an arbitrary epimorphism for an arbitrary Noetherian ring.

lem-per-noetherian-constructible-flat-lifting vs lem-weil-pbc-constructible-module-limit-descent: the existing statement proves a constructible sheaf of $\lambda$-modules on a limit of qcqs schemes descends to some stage (stacks 09yu (3), essential surjectivity) with finite-coefficient or scheme-limit/colimit input; it does not give flat constructible lifting of every map from a constructible module along an arbitrary epimorphism for an arbitrary Noetherian ring.

lem-per-noetherian-constructible-flat-lifting vs lem-weil-pbc-etale-free-sheaf-constructible-core: the existing statement proves stalk constructibility of etale lower shriek of a finite constant module with finite-coefficient or scheme-limit/colimit input; it does not give flat constructible lifting of every map from a constructible module along an arbitrary epimorphism for an arbitrary Noetherian ring.

lem-per-noetherian-constructible-flat-lifting vs new-constructible-affine-free-presentation-general: the existing statement gives an affine-free presentation; it does not assert a lift through a prescribed epimorphism or flatness of the lifting cover.

lem-per-noetherian-constructible-flat-lifting vs lem-weil-pbc-module-sheaf-colimit-constructible-data: the existing statement proves filtered constructible maps with factorization and relations with finite-coefficient or scheme-limit/colimit input; it does not give flat constructible lifting of every map from a constructible module along an arbitrary epimorphism for an arbitrary Noetherian ring.

lem-per-noetherian-constructible-flat-lifting vs lem-weil-pbc-constructible-module-surjectivity-locus: the existing statement proves constructible locus of failure of module stalk surjectivity with finite-coefficient or scheme-limit/colimit input; it does not give flat constructible lifting of every map from a constructible module along an arbitrary epimorphism for an arbitrary Noetherian ring.

lem-per-noetherian-constructible-flat-lifting vs lem-weil-pbc-constructible-generation: the existing statement proves constructible module sheaves generate the category with finite-coefficient or scheme-limit/colimit input; it does not give flat constructible lifting of every map from a constructible module along an arbitrary epimorphism for an arbitrary Noetherian ring.

lem-per-noetherian-constructible-flat-lifting vs new-constructible-limit-descent-general: the existing statement descends a constructible sheaf along a scheme inverse limit; it provides neither a prescribed-epimorphism lifting square nor a common Galois partition.

lem-per-noetherian-constructible-flat-lifting vs lem-weil-pbc-spectral-constructible-finite-intersection: the existing statement is compactness for constructible subsets of a spectral space, without sheaf lifting, flatness or Galois trivializations.

lem-per-noetherian-constructible-flat-lifting vs lem-weil-pbc-affine-free-finite-stalk-generation: the existing statement selects finitely many maps generating one given stalk, without a global epimorphism, lifting square, constructible flat cover, or common Galois partition.

lem-per-noetherian-constructible-flat-lifting vs lem-weil-pbc-constructible-module-finite-epimorphism: the existing statement proves finite affine free epimorphisms onto constructible module sheaves with finite-coefficient or scheme-limit/colimit input; it does not give flat constructible lifting of every map from a constructible module along an arbitrary epimorphism for an arbitrary Noetherian ring.

lem-per-noetherian-constructible-flat-lifting vs lem-weil-pbc-etale-free-sheaf-constructible: the existing statement proves extension by zero of a finite constant sheaf along a qcqs etale map is constructible with finite-coefficient or scheme-limit/colimit input; it does not give flat constructible lifting of every map from a constructible module along an arbitrary epimorphism for an arbitrary Noetherian ring.

lem-per-noetherian-constructible-flat-lifting vs lem-weil-pbc-affine-free-etale-family-models: the existing statement proves common-stage models of two finite affine etale free families with finite-coefficient or scheme-limit/colimit input; it does not give flat constructible lifting of every map from a constructible module along an arbitrary epimorphism for an arbitrary Noetherian ring.

lem-per-noetherian-constructible-flat-lifting vs lem-sf-etale-flat-constructible-lifting: the existing statement proves flat constructible sheaves lift epimorphisms with finite-coefficient or scheme-limit/colimit input; it does not give flat constructible lifting of every map from a constructible module along an arbitrary epimorphism for an arbitrary Noetherian ring.

lem-per-noetherian-constructible-flat-lifting vs lem-kun-03sa: the existing statement proves constructible generation with finite-coefficient or scheme-limit/colimit input; it does not give flat constructible lifting of every map from a constructible module along an arbitrary epimorphism for an arbitrary Noetherian ring.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-fixed-puncture-geometric: the existing statement concerns geometric fixed-orbit construction for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-component-image-orbit-backward: the existing statement concerns backward implication of the affine torsor component image orbit criterion for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-fixed-puncture-descent: the existing statement concerns descent along a connected affine torsor to fixed-ring punctures for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-equivariant-descent: the existing statement concerns descent to the whole equivariant function algebra for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-split-point-lifting: the existing statement concerns point lifting to explicit split sections for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-stabilizer-section-mono: the existing statement concerns monomorphy of a descended section with exact stabilizer for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-fixed-puncture-descent-core: the existing statement concerns fixed-orbit affine torsor descent step for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-field-torsor-galois-components: the existing statement concerns galois field components of a finite group torsor for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-invariant-puncture-etale: the existing statement concerns etaleness of the invariant principal open of an affine torsor for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-invariant-basic-open-descent: the existing statement concerns unique descent of an invariant affine basic-open morphism for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-equivariant-orbit-model: the existing statement concerns equivariant orbit model for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs def-sbc-affine-torsor-equivariant-algebra: the existing statement concerns equivariant algebra on the split components for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-fixed-orbit-product-equiv: the existing statement concerns fixed orbit product comparison for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-equivariant-descent-algebra: the existing statement concerns algebraic reconstruction from orbit data for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-split-label-laws: the existing statement concerns cocycle laws for labels in a pulled-back splitting for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-cartier-stalk-normalization-product: the existing statement concerns integral-closure product model of a cartier torsor normalization over the actual dvr stalk for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-fixed-puncture-orbit-data: the existing statement concerns finite orbit representative data for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-single-stabilizer-component: the existing statement concerns descent of one stabilizer component for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-fixed-orbit-product-equiv-compatible-model: the existing statement concerns compatible finite orbit model for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-component-image-orbit: the existing statement concerns image of one stabilizer component is its label orbit for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-single-stabilizer-component-section: the existing statement concerns section equation for the stabilizer component for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-representative-component-cover: the existing statement concerns coverage and disjointness of representative components for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-single-stabilizer-component-open: the existing statement concerns existence of the open stabilizer component for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-fixed-orbit-data-of-action: the existing statement concerns canonical orbit data of a finite action for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-component-image-orbit-forward: the existing statement concerns forward implication of the affine torsor component image orbit criterion for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-equivariant-orbit-product: the existing statement concerns equivariant algebra as product of stabilizer fixed rings for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-fixed-puncture-compatibility: the existing statement concerns fixed-orbit projection compatibility for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-orbit-component-descent: the existing statement concerns descent of individual fixed-orbit components for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-affine-torsor-stabilizer-section-open: the existing statement concerns openness criterion for a descended stabilizer section for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-sbc-field-torsor-component-galois-group: the existing statement concerns galois group of a field component of a finite torsor for a specified affine torsor, invariant algebra or field extension; it neither constructs a stratification for arbitrary constructible module sheaves nor supplies their constant module values.

lem-per-noetherian-constructible-galois-partition vs lem-trf-constructible-generator-epimorphism: the existing statement proves finite etale free generators lift epimorphisms onto constructible sheaves with finite-coefficient or scheme-limit/colimit input; it does not give simultaneous Galois partitions with finitely presented values for arbitrary Noetherian-coefficient constructible module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-trf-constructible-etale-finite-affine-syzygy: the existing statement proves finite affine-free syzygies of constructible etale modules with finite-coefficient or scheme-limit/colimit input; it does not give simultaneous Galois partitions with finitely presented values for arbitrary Noetherian-coefficient constructible module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-immersion-affine-constructible-pieces: the existing statement gives an immersed constructible stratum of an affine scheme splits into finitely many affine constructible pieces; it asserts no common finite Galois cover trivializing an arbitrary finite family of module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-constructible-module-finite-stalks: the existing statement proves the geometric stalks of a constructible sheaf of modules are finite with finite-coefficient or scheme-limit/colimit input; it does not give simultaneous Galois partitions with finitely presented values for arbitrary Noetherian-coefficient constructible module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-constructible-module-finite-zero-cokernel: the existing statement proves finite affine free cover with zero cokernel with finite-coefficient or scheme-limit/colimit input; it does not give simultaneous Galois partitions with finitely presented values for arbitrary Noetherian-coefficient constructible module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-constructible-module-finite-presentation: the existing statement proves a constructible sheaf of modules on a qcqs scheme is a cokernel of a map between finite sums of extensions by zero of lambda from affine etale objects with finite-coefficient or scheme-limit/colimit input; it does not give simultaneous Galois partitions with finitely presented values for arbitrary Noetherian-coefficient constructible module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-finite-monodromy-trivializing-torsor: the existing statement starts with a finite locally constant set or F_ell-module sheaf on one connected base; the helper permits arbitrary Noetherian R and infinite underlying module sets and constructs strata for a finite family.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-affine-free-etale-module-arrow-descent: the existing statement proves arrows between finite sums of affine etale free module sheaves descend with finite-coefficient or scheme-limit/colimit input; it does not give simultaneous Galois partitions with finitely presented values for arbitrary Noetherian-coefficient constructible module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-constructible-large-colimit-factorization: the existing statement proves constructible-source factorization into filtered colimits at the coefficient universe with finite-coefficient or scheme-limit/colimit input; it does not give simultaneous Galois partitions with finitely presented values for arbitrary Noetherian-coefficient constructible module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-constructible-stratification-assembly: the existing statement gives assemble stratifications of a constructible immersed partition; it asserts no common finite Galois cover trivializing an arbitrary finite family of module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-constructible-module-limit-descent: the existing statement proves a constructible sheaf of $\lambda$-modules on a limit of qcqs schemes descends to some stage (stacks 09yu (3), essential surjectivity) with finite-coefficient or scheme-limit/colimit input; it does not give simultaneous Galois partitions with finitely presented values for arbitrary Noetherian-coefficient constructible module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-etale-stratification-local-gluing-core: the existing statement gives global constructible immersed refinement factoring through local strata; it asserts no common finite Galois cover trivializing an arbitrary finite family of module sheaves.

lem-per-noetherian-constructible-galois-partition vs new-constructible-affine-free-presentation-general: the existing statement gives an affine-free presentation; it does not assert a simultaneous finite Galois splitting cover and finitely presented constant values. Its cited constructible definition also uses finite underlying sets, so it cannot silently serve as an infinite-module theorem.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-module-sheaf-colimit-constructible-data: the existing statement proves filtered constructible maps with factorization and relations with finite-coefficient or scheme-limit/colimit input; it does not give simultaneous Galois partitions with finitely presented values for arbitrary Noetherian-coefficient constructible module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-affine-basic-sets-disjoint-refinement: the existing statement gives a finite union of sets d(f) ∩ v(g_1,…,g_n) in an affine spectrum is a finite disjoint union of such sets; it asserts no common finite Galois cover trivializing an arbitrary finite family of module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-constructible-module-surjectivity-locus: the existing statement proves constructible locus of failure of module stalk surjectivity with finite-coefficient or scheme-limit/colimit input; it does not give simultaneous Galois partitions with finitely presented values for arbitrary Noetherian-coefficient constructible module sheaves.

lem-per-noetherian-constructible-galois-partition vs new-constructible-limit-descent-general: the existing statement descends a constructible sheaf along a scheme inverse limit; it provides neither a prescribed-epimorphism lifting square nor a common Galois partition.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-etale-stratified-finite: the existing statement gives etale morphisms become finite etale on a constructible stratification; it asserts no common finite Galois cover trivializing an arbitrary finite family of module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-spectral-constructible-finite-intersection: the existing statement is compactness for constructible subsets of a spectral space, without sheaf lifting, flatness or Galois trivializations.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-representable-pullback-constant-evaluation: the existing statement starts with specified finite etale schemes or a given torsor and proves representable pullback is constant from exhaustive evaluation; it does not stratify general constructible R-module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-affine-basic-set-difference: the existing statement gives the difference of two affine basic sets is a finite disjoint union of affine basic sets; it asserts no common finite Galois cover trivializing an arbitrary finite family of module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-affine-free-finite-stalk-generation: the existing statement selects finitely many maps generating one given stalk, without a global epimorphism, lifting square, constructible flat cover, or common Galois partition.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-etale-stratification-local-gluing: the existing statement gives finite constructible stratifications with a local property glue over a qcqs base; it asserts no common finite Galois cover trivializing an arbitrary finite family of module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-finite-set-monodromy-torsor: the existing statement starts with a finite locally constant set or F_ell-module sheaf on one connected base; the helper permits arbitrary Noetherian R and infinite underlying module sets and constructs strata for a finite family.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-constructible-module-finite-epimorphism: the existing statement proves finite affine free epimorphisms onto constructible module sheaves with finite-coefficient or scheme-limit/colimit input; it does not give simultaneous Galois partitions with finitely presented values for arbitrary Noetherian-coefficient constructible module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-etale-affine-cover-gluing: the existing statement proves finite etale chart and overlap pieces glue to a separated etale base change with finite-coefficient or scheme-limit/colimit input; it does not give simultaneous Galois partitions with finitely presented values for arbitrary Noetherian-coefficient constructible module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-connected-torsor-subgroup-quotient: the existing statement starts with specified finite etale schemes or a given torsor and proves connected subgroup quotients of a finite etale torsor with geometric fibre cardinality; it does not stratify general constructible R-module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-weil-pbc-affine-free-etale-family-models: the existing statement proves common-stage models of two finite affine etale free families with finite-coefficient or scheme-limit/colimit input; it does not give simultaneous Galois partitions with finitely presented values for arbitrary Noetherian-coefficient constructible module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-sf-etale-flat-constructible-lifting: the existing statement proves flat constructible sheaves lift epimorphisms with finite-coefficient or scheme-limit/colimit input; it does not give simultaneous Galois partitions with finitely presented values for arbitrary Noetherian-coefficient constructible module sheaves.

lem-per-noetherian-constructible-galois-partition vs lem-exc-etale-field-gsets: the existing statement concerns etale schemes over a field and continuous g-sets over a field or a given finite Galois cover; the helper constructs strata and simultaneous trivializations for arbitrary constructible modules on a Noetherian scheme.

lem-per-noetherian-constructible-galois-partition vs lem-exc-finite-galois-sheaf-sections-coproduct: the existing statement concerns sections on a finite open-and-closed coproduct in a small etale site over a field or a given finite Galois cover; the helper constructs strata and simultaneous trivializations for arbitrary constructible modules on a Noetherian scheme.

lem-per-noetherian-constructible-galois-partition vs lem-exc-finite-galois-tensor-decomposition: the existing statement concerns tensor decomposition for a finite galois field extension over a field or a given finite Galois cover; the helper constructs strata and simultaneous trivializations for arbitrary constructible modules on a Noetherian scheme.

lem-per-noetherian-constructible-galois-partition vs lem-exc-etale-open-subgroup-fixed-field: the existing statement concerns open subgroups of an absolute galois group over a field or a given finite Galois cover; the helper constructs strata and simultaneous trivializations for arbitrary constructible modules on a Noetherian scheme.

lem-per-noetherian-constructible-galois-partition vs lem-exc-finite-galois-algebra-tensor-decomposition: the existing statement concerns affine fibre-product consequence of a finite galois tensor decomposition over a field or a given finite Galois cover; the helper constructs strata and simultaneous trivializations for arbitrary constructible modules on a Noetherian scheme.

lem-per-noetherian-constructible-flat-lifting vs lem-sf-etale-flat-constructible-lifting: that node explicitly requires a finite ring; this helper allows an arbitrary Noetherian ring such as F_ell[t].

lem-per-noetherian-constructible-galois-partition vs lem-per-constructible-finite-monodromy-filtration: that node supplies a sheaf filtration by stratum extensions. It does not assert one common partition trivializing the original finite family itself or finitely presented constant values.

lem-per-noetherian-constructible-galois-partition vs det-sf-flat-model-generation: that node uses finite coefficients and flat sheaves and gives a stratum extension devissage, not simultaneous arbitrary-Noetherian module trivialization.

## Remaining work

No missing proof step in this one-level split. The two new statement-only inputs are deliberately left for future stage-1 splitting. Maintainer independent review and later formalization remain outside this delivery.
