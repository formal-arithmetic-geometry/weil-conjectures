# Stage-1 repair: lem-per-bounded-above-rhom-hyperext

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-bounded-above-rhom-hyperext.json — item, statement and statement dependencies unchanged; three-step assembly (1536 characters).
- dag/nodes/sec-deligne-laumon-a1/lem-per-rhom-local-cohomological-bound.json — statement-only, unsplit, no Mathlib match; local derived Hom, its cohomological boundaries and lower amplitude (original Steps 1–3).
- dag/nodes/sec-deligne-laumon-a1/lem-per-postnikov-additive-exact-couple.json — statement-only, unsplit, no Mathlib match; a generic additive homological functor's Postnikov couple, E2 identification and additive page/filtered functoriality (original Steps 4, 5 and 9).
- dag/nodes/sec-deligne-laumon-a1/lem-per-postnikov-finite-cutoff-abutment.json — statement-only, unsplit, no Mathlib match; a generic shifted-amplitude functor's finite cutoff, actual image filtration and convergence (original Steps 6–8 and the support part of Step 5).
- citations.json — full verbatim statement quotes for each of the three assembly citations.
- searches.jsonl — actual msearch results; retained as returned by the search tool.

## Attachments

None. Searching lean/WeilConjectures for the blueprint tag, bounded-above RHom and hyper-Ext gave no exact declaration. The project module lean/Sheaf/Algebra/Homology/BoundedAboveRHomHyperExt.lean has the item's theorem CategoryTheory.exists_boundedAbove_rhom_hyperExt at line 130 with sorry at line 246. This is not an attachment. No Lean was edited or compiled.

## WANTED

None. Sources used below are available in the read clone.

## What was wrong and what changed

The released stage-1 repair note of 2026-10-22 explicitly reopens this split despite its earlier reviewed record: the nine-step proof is 6931 characters and must distribute its work into at least two new statement-only nodes. The assigned sandbox initially contained only dispatcher .brief files, no node, report or search log. I copied the current live item, preserving all maintainer metadata, statement and statement dependencies; there was no retained delivered patch to discard or silently overwrite. The delivery tool rebases the worker-owned fields onto current origin.

Three comparable proof packages now share the old work. The first is specific to arbitrary small ringed sites; the second and third are generic homological algebra and can be worked on independently of a construction of derived internal Hom. Their statements explicitly introduce the additive homological functor and coherent shifted family; they have no sibling proof dependency, no proof steps, and no proof sketch hidden in their statements. In the assembly the first node supplies the hypotheses of the other two. This does not move the whole item into one leaf and does not replace its conclusion by a weaker one.

The exact original argument records are preserved below for the next workers, including their sources and existing dependencies. Every old inference is represented in a new node's conclusion: local sheafification and all local naturality, long exact boundary maps, support bounds, exact-couple maps and indexing, the right shift, half-plane translation, all truncation-tail comparisons, the actual image filtration, and additive functoriality on pages, filtrations and graded pieces. No chapter or unit route was altered and no statement dispute was needed.

## Sources and Mathlib search reading

For the item I read Stacks derived.tex, Tag 015W (lemma-ss-filtered-derived), and its actual bounded filtered-derived proof, sites-cohomology.tex at Tags 0A94 and 0A95, homology.tex at the exact-couple definition, derived couple and finite-cycle formulas, and derived.tex Tag 08J5. I also read ILO, Travaux de Gabber, XVII 10.1.1, printed p.325 (PDF p.331): Ext continuity implies commutation with representable sums there, but that proof does not itself state this general spectral sequence. The expanded Postnikov argument remains explicitly agent mathematics; I do not mislabel Tag 015W as a verbatim generalization to a complex first argument. The current blueprint ancestor lem-per-artin-gabber-affine-curve's Step 1 and the inherited coefficient-comparison ancestry were retained; blueprint searches across all chapters for Postnikov, local derived Hom, Postnikov exact couple and finite cutoff found no equal blueprint statement.

For lem-per-rhom-local-cohomological-bound I read Stacks sites-cohomology.tex, lemma-RHom-into-K-injective (0A94) and the sheafification passage of lemma-RHom-well-defined (0A95), plus sites-modules.tex lemma-sheafification-exact (03EI). The source gives local H0 and exact sheafification; the shifted local formula, natural boundaries and orthogonality bound are precisely the extracted tasks, not claimed already proved by the definition. The source-shift sign calculation of old Step 1 is retained below. The existing local-Hom naturality lemma gives arbitrary chain-map compatibility, and the exact restriction lemma really says restriction is exact. This justifies local orthogonality without a Tor or site-dimension assumption.

For lem-per-postnikov-additive-exact-couple I read homology.tex definition-exact-couple (011Q), lemma-derived-exact-couple (011R) and definition-spectral-sequence-associated-exact-couple (011S), and derived.tex remark-truncation-distinguished-triangle (08J5). The project uses E2 indexing with alpha (-1,1), f (2,-1), g (0,0). I checked the existing derived-couple statement, not just its title: it gives iteration, changing type and the correct (s,1-s) differential. I read lem-sp-couple-morphism for its actual graded/abutment claim. Additivity of induced image, kernel and quotient maps is an explicit separate conclusion of the extracted lemma; it is not falsely taken from that morphism theorem.

For lem-per-postnikov-finite-cutoff-abutment I read homology.tex lemma-spectral-sequence-associated-exact-couple (011T), the full statement of thm-sp-half-plane-convergence, and derived.tex 08J5. The new node's work is the translation and actual-truncation comparison beyond the generic half-plane result. I checked that the latter has abutment D(0,N), hence the first-index shift P=p+r forces N=n+r, giving T^n(tau<=n+r L). The positive tail begins at n+r+1, so both T^(n-1) and T^n of it vanish. For larger cutoffs m>=n+r the same calculation holds; this is needed for every p<=-r in the image filtration.

For each new node the log contains LeanFinder, Loogle, Mathlib grep, and a second natural-language phrasing with LeanSearch; all services used here returned answers. The exact queries and digest records are in each node. I read the returned hits. Sheaf.cohomologyPresheafFunctor in Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean:72 uses Ext from a free abelian sheaf, and does not compute our arbitrary-complex sheaf RHom or its boundaries. The K-injective result CochainComplex.HomComplex.CohomologyClass.bijective_toSmallShiftedHom_of_isKInjective (Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean:68) is the local algebraic ingredient, not the sheafified cohomological/amplitude assertion. Functor.homologySequence_exact_1/2/3 (Unicode subscript names in HomologicalFunctor.lean:218–237) give exactness, not the complete Postnikov/page/additivity statement. I read SpectralObject/SpectralSequence.lean, especially its construction at line 482, and HasSpectralSequence.lean:393 onward: the IsFirstQuadrant class assumes a supplied spectral object and supplies a spectral-sequence shape, not the cutoff isomorphism or actual abutment filtration. None is an exact or one-line match. Generic spectral-object infrastructure remains available to the future workers; no Mathlib leaf was missed by treating this infrastructure as absent.

## Review by Q119

I checked delivery-errors B–E against the four node files and the opened sources. The three new statements quantify their own objects, universe conventions where relevant, functors, integers, support hypotheses and comparison maps. Their notion dependencies actually define those notions, including module sheafification, localized sites, K-injectives, homological functors, exact couples and finite filtrations. Every new node is unsplit with empty proof and proof_deps and null proof_origin. They distribute substantial arguments rather than each restating the item's conclusion. The generic couple lemma alone supplies no support, vanishing or convergence; the generic cutoff lemma assumes an existing Postnikov exact couple and an amplitude bound but constructs neither the cohomological RHom calculation nor additive spectral-sequence morphisms; the local lemma constructs no spectral sequence.

In assembly Step 1 the only cited node, lem-per-rhom-local-cohomological-bound, states the natural long exact sequences, coherent shifts, additivity and amplitude for all b that this step uses. The site's smallness, commutative coefficient sheaf and K in D<=r are exactly the item's hypotheses. In Step 2 lem-per-postnikov-additive-exact-couple is applied to A=B=Mod(O); the input additive homological T0 and shift identifications are provided by Step 1. Its statement gives the exact couple, E2=T^p(H^qL[0]), differentials, additive page maps and filtered compatibility, exactly the claims made in Step 2. In Step 3 lem-per-postnikov-finite-cutoff-abutment assumes precisely that couple and the bound from Step 1 plus L in D>=c. It states the reindexing, cutoff isomorphisms, transported image filtration, support interval and graded compatibility; Step 2 gives additivity under that transport. All three citations are quoted verbatim in citations.json. There are no implicit non-elementary facts in the short assembly and no >2000-character assembly step.

I tested the extracted statements at zero K, zero L, zero functor T, a heart object at degree c, and shifted heart K at upper degree r. On a point with field coefficients, K=k[-r] has cohomology in degree r and RHom(k[-r],L)=L[r], so T^n(L)=H^(n+r)(L). This checks both the bound c-r and cutoff n+r with the delivered signs. If n+r<c the support interval is empty and both the abutment and every filtration step are zero. At n=c-r only q=c and p=-r can survive; F^(-r) is the whole object and F^(-r+1)=0. For arbitrary r (including negative r), reindexing P=p+r gives support P>=0 with no differential-degree change. These checks do not introduce constructibility, finite Tor amplitude or a cohomological-dimension hypothesis.

I checked acyclicity by the shape of the new dependencies: the three new nodes cite only existing definition/theorem interfaces for their statements, and none cites the item or a sibling. The item cites exactly those three. The existing unit and ancestor are unchanged. I compared same-tag and concept matches by their statements below, including the ordinary-left-exact-functor truncation theorems which cannot take a complex K as an argument on the heart. I preserved every original step and source in the handoff rather than erasing difficult arguments. The checks and delivery are performed through the required server tools, with no local validator execution, no repository mutation and no compilation.

## Not duplicates

lem-per-rhom-local-cohomological-bound vs lem-pur-hom-complex-sections-derived-naturality: existing statement is 'Shifted local derived comparison with naturality' for homology of sections of fixed Hom complexes and chain maps; it does not give sheafification, triangle boundary sequences or the bound b-r; the new statement computes the sheafified local-derived-Hom family and its natural long exact boundaries and lower amplitude for arbitrary derived inputs.

lem-per-rhom-local-cohomological-bound vs lem-pur-rhom-global-sections: existing statement is 'Global sections of the derived internal Hom' (global hypercohomology H0), not the cohomology sheaf, arbitrary-degree sheafified presheaf or its amplitude; the new statement computes the sheafified local-derived-Hom family and its natural long exact boundaries and lower amplitude for arbitrary derived inputs.

lem-per-rhom-local-cohomological-bound vs lem-pur-rhom-into-kinjective-local: existing statement is 'Hom into a K-injective complex computes localized derived morphisms' for degree-zero local cocycles, not the cohomological family and its amplitude; the new statement computes the sheafified local-derived-Hom family and its natural long exact boundaries and lower amplitude for arbitrary derived inputs.

lem-per-rhom-local-cohomological-bound vs lem-pur-rhom-well-defined-universes: existing statement is 'The Hom complex into K-injective complexes respects quasi-isomorphisms with independent coefficient universe' about quasi-isomorphisms of Hom complexes or their sections, not the cohomological RHom family and its support bound; the new statement computes the sheafified local-derived-Hom family and its natural long exact boundaries and lower amplitude for arbitrary derived inputs.

lem-per-rhom-local-cohomological-bound vs lem-pur-hom-complex-sections-quasi-iso-universes: existing statement is 'Sectionwise invariance of Hom complexes into K-injectives with independent coefficient universe' about quasi-isomorphisms of Hom complexes or their sections, not the cohomological RHom family and its support bound; the new statement computes the sheafified local-derived-Hom family and its natural long exact boundaries and lower amplitude for arbitrary derived inputs.

lem-per-rhom-local-cohomological-bound vs lem-pur-hom-complex-sections-derived-naturality-universes: existing statement is 'Shifted local derived comparison with naturality with independent coefficient universe' for homology of sections of fixed Hom complexes and chain maps; it does not give sheafification, triangle boundary sequences or the bound b-r; the new statement computes the sheafified local-derived-Hom family and its natural long exact boundaries and lower amplitude for arbitrary derived inputs.

lem-per-rhom-local-cohomological-bound vs lem-pur-hom-complex-sections-quasi-iso: existing statement is 'Sectionwise invariance of Hom complexes into K-injectives' about quasi-isomorphisms of Hom complexes or their sections, not the cohomological RHom family and its support bound; the new statement computes the sheafified local-derived-Hom family and its natural long exact boundaries and lower amplitude for arbitrary derived inputs.

lem-per-rhom-local-cohomological-bound vs lem-pur-quasi-iso-of-sections-universes: existing statement is 'Sectionwise quasi-isomorphisms are quasi-isomorphisms of sheaves with independent coefficient universe' detecting quasi-isomorphisms from sectionwise comparisons, not a description of the cohomological RHom family; the new statement computes the sheafified local-derived-Hom family and its natural long exact boundaries and lower amplitude for arbitrary derived inputs.

lem-per-rhom-local-cohomological-bound vs lem-pur-quasi-iso-of-sections: existing statement is 'Sectionwise quasi-isomorphisms are quasi-isomorphisms of sheaves' detecting quasi-isomorphisms from sectionwise comparisons, not a description of the cohomological RHom family; the new statement computes the sheafified local-derived-Hom family and its natural long exact boundaries and lower amplitude for arbitrary derived inputs.

lem-per-rhom-local-cohomological-bound vs lem-pur-rhom-well-defined: existing statement is 'The Hom complex into K-injective complexes respects quasi-isomorphisms' about quasi-isomorphisms of Hom complexes or their sections, not the cohomological RHom family and its support bound; the new statement computes the sheafified local-derived-Hom family and its natural long exact boundaries and lower amplitude for arbitrary derived inputs.

lem-per-postnikov-additive-exact-couple vs lem-sp-filtered-homology-couple-exactness: existing statement is 'Exactness of the explicit filtered homology maps' for homology of a filtered cochain complex; it neither accepts a general homological T on D(A) nor gives its additive Postnikov morphisms; the new statement constructs a Postnikov couple from an arbitrary homological functor and proves additivity of its page and filtered maps.

lem-per-postnikov-additive-exact-couple vs lem-sp-filtered-homology-couple-normalization: existing statement is 'Inclusion and quotient-map normalization of the concrete homology couple' for homology of a filtered cochain complex; it neither accepts a general homological T on D(A) nor gives its additive Postnikov morphisms; the new statement constructs a Postnikov couple from an arbitrary homological functor and proves additivity of its page and filtered maps.

lem-per-postnikov-additive-exact-couple vs def-sp-exact-couple: existing statement is 'Bigraded exact couples' defining arbitrary couples; it does not construct the couple of T and a truncation tower; the new statement constructs a Postnikov couple from an arbitrary homological functor and proves additivity of its page and filtered maps.

lem-per-postnikov-additive-exact-couple vs def-sp-filtered-homology-exact-couple: existing statement is 'Concrete filtered homology exact couple' for homology of a filtered cochain complex; it neither accepts a general homological T on D(A) nor gives its additive Postnikov morphisms; the new statement constructs a Postnikov couple from an arbitrary homological functor and proves additivity of its page and filtered maps.

lem-per-postnikov-additive-exact-couple vs lem-sp-derived-couple-functoriality: existing statement is 'Functoriality of derived exact couples' starting from already supplied exact-couple morphisms; it does not construct Postnikov morphisms or assert additivity in a derived morphism; the new statement constructs a Postnikov couple from an arbitrary homological functor and proves additivity of its page and filtered maps.

lem-per-postnikov-additive-exact-couple vs def-sp-filtered-homology-couple-data: existing statement is 'Explicit homology terms and filtration maps' for homology of a filtered cochain complex; it neither accepts a general homological T on D(A) nor gives its additive Postnikov morphisms; the new statement constructs a Postnikov couple from an arbitrary homological functor and proves additivity of its page and filtered maps.

lem-per-postnikov-additive-exact-couple vs lem-sp-derived-couple-kernel-identities: existing statement is 'Kernel and image identities for the derived differential.' about derived couples already supplied (kernel identities, induced maps, image prefix or iteration), not the Postnikov construction and its additive filtered functoriality; the new statement constructs a Postnikov couple from an arbitrary homological functor and proves additivity of its page and filtered maps.

lem-per-postnikov-additive-exact-couple vs lem-sp-exact-functor-half-plane: existing statement is 'Limiting and large-page comparisons for an exact functor' transporting an already supplied couple by an exact functor of abelian categories; T is instead homological on a derived category; the new statement constructs a Postnikov couple from an arbitrary homological functor and proves additivity of its page and filtered maps.

lem-per-postnikov-additive-exact-couple vs lem-sp-derived-couple-map-uniqueness: existing statement is 'Uniqueness of the induced derived maps.' about derived couples already supplied (kernel identities, induced maps, image prefix or iteration), not the Postnikov construction and its additive filtered functoriality; the new statement constructs a Postnikov couple from an arbitrary homological functor and proves additivity of its page and filtered maps.

lem-per-postnikov-additive-exact-couple vs lem-sp-exact-functor-couple: existing statement is 'Exact functors carry exact couples and their spectral sequences' transporting an already supplied couple by an exact functor of abelian categories; T is instead homological on a derived category; the new statement constructs a Postnikov couple from an arbitrary homological functor and proves additivity of its page and filtered maps.

lem-per-postnikov-additive-exact-couple vs lem-sp-derived-couple-image-prefix: existing statement is 'Recursive image and inclusion properties of iterated derived couples' about derived couples already supplied (kernel identities, induced maps, image prefix or iteration), not the Postnikov construction and its additive filtered functoriality; the new statement constructs a Postnikov couple from an arbitrary homological functor and proves additivity of its page and filtered maps.

lem-per-postnikov-additive-exact-couple vs lem-sp-derived-couple-exact: existing statement is 'The derived couple of an exact couple is exact' about derived couples already supplied (kernel identities, induced maps, image prefix or iteration), not the Postnikov construction and its additive filtered functoriality; the new statement constructs a Postnikov couple from an arbitrary homological functor and proves additivity of its page and filtered maps.

lem-per-postnikov-additive-exact-couple vs lem-sp-derived-couple-boundary-vanishes: existing statement is 'Boundary vanishing in the cycle quotient.' about derived couples already supplied (kernel identities, induced maps, image prefix or iteration), not the Postnikov construction and its additive filtered functoriality; the new statement constructs a Postnikov couple from an arbitrary homological functor and proves additivity of its page and filtered maps.

lem-per-postnikov-finite-cutoff-abutment vs lem-sp-finite-boundary-alpha-kernel: existing statement is 'Finite exact-couple boundaries as initial g-images of iterated alpha kernels' giving cycle, boundary, image, kernel, derived-map or graded comparisons for an already supplied abstract couple; it does not give the shifted truncation-tail comparison with T^n(L); the new statement identifies a shifted Postnikov cutoff with the actual T^n(L) and its all-integer truncation image filtration.

lem-per-postnikov-finite-cutoff-abutment vs thm-sp-half-plane-convergence: existing statement is 'Half-plane convergence' for abstract support p>=0 with abutment D(0,n); it does not identify the shifted cutoff with T^n(L) or all its truncation images; the new statement identifies a shifted Postnikov cutoff with the actual T^n(L) and its all-integer truncation image filtration.

lem-per-postnikov-finite-cutoff-abutment vs lem-sp-finite-cycle-formula: existing statement is 'Finite cycle formula' giving cycle, boundary, image, kernel, derived-map or graded comparisons for an already supplied abstract couple; it does not give the shifted truncation-tail comparison with T^n(L); the new statement identifies a shifted Postnikov cutoff with the actual T^n(L) and its all-integer truncation image filtration.

lem-per-postnikov-finite-cutoff-abutment vs lem-sp-normalized-graded-finite-kernel: existing statement is 'The kernel of a normalized colimit graded-piece map is a finite alpha pullback' giving cycle, boundary, image, kernel, derived-map or graded comparisons for an already supplied abstract couple; it does not give the shifted truncation-tail comparison with T^n(L); the new statement identifies a shifted Postnikov cutoff with the actual T^n(L) and its all-integer truncation image filtration.

lem-per-postnikov-finite-cutoff-abutment vs lem-sp-finite-page-image-quotient: existing statement is 'A finite exact-couple page as a quotient of consecutive colimit images' giving cycle, boundary, image, kernel, derived-map or graded comparisons for an already supplied abstract couple; it does not give the shifted truncation-tail comparison with T^n(L); the new statement identifies a shifted Postnikov cutoff with the actual T^n(L) and its all-integer truncation image filtration.

lem-per-postnikov-finite-cutoff-abutment vs lem-sp-derived-couple-functoriality: existing statement is 'Functoriality of derived exact couples' giving cycle, boundary, image, kernel, derived-map or graded comparisons for an already supplied abstract couple; it does not give the shifted truncation-tail comparison with T^n(L); the new statement identifies a shifted Postnikov cutoff with the actual T^n(L) and its all-integer truncation image filtration.

lem-per-postnikov-finite-cutoff-abutment vs lem-sp-half-plane-graded-canonical: existing statement is 'The half-plane graded identification is the canonical one' giving cycle, boundary, image, kernel, derived-map or graded comparisons for an already supplied abstract couple; it does not give the shifted truncation-tail comparison with T^n(L); the new statement identifies a shifted Postnikov cutoff with the actual T^n(L) and its all-integer truncation image filtration.

lem-per-postnikov-finite-cutoff-abutment vs lem-sp-finite-cycle-kernel-presentation: existing statement is 'The canonical finite-cycle projection is epic with its intrinsic alpha-image kernel' giving cycle, boundary, image, kernel, derived-map or graded comparisons for an already supplied abstract couple; it does not give the shifted truncation-tail comparison with T^n(L); the new statement identifies a shifted Postnikov cutoff with the actual T^n(L) and its all-integer truncation image filtration.

lem-per-postnikov-finite-cutoff-abutment vs lem-sp-finite-cocone-limit-boundaries: existing statement is 'FiniteCoconeLimitBoundaries' giving cycle, boundary, image, kernel, derived-map or graded comparisons for an already supplied abstract couple; it does not give the shifted truncation-tail comparison with T^n(L); the new statement identifies a shifted Postnikov cutoff with the actual T^n(L) and its all-integer truncation image filtration.

lem-per-postnikov-finite-cutoff-abutment vs lem-sp-finite-cocone-limit-cycles: existing statement is 'FiniteCoconeLimitCycles' giving cycle, boundary, image, kernel, derived-map or graded comparisons for an already supplied abstract couple; it does not give the shifted truncation-tail comparison with T^n(L); the new statement identifies a shifted Postnikov cutoff with the actual T^n(L) and its all-integer truncation image filtration.

lem-per-postnikov-finite-cutoff-abutment vs lem-sp-derived-couple-kernel-identities: existing statement is 'Kernel and image identities for the derived differential.' giving cycle, boundary, image, kernel, derived-map or graded comparisons for an already supplied abstract couple; it does not give the shifted truncation-tail comparison with T^n(L); the new statement identifies a shifted Postnikov cutoff with the actual T^n(L) and its all-integer truncation image filtration.

lem-per-postnikov-finite-cutoff-abutment vs lem-sp-exact-functor-half-plane: existing statement is 'Limiting and large-page comparisons for an exact functor' comparing couples under an exact functor on abelian categories, not comparing a Postnikov cutoff with the original derived object; the new statement identifies a shifted Postnikov cutoff with the actual T^n(L) and its all-integer truncation image filtration.

lem-per-postnikov-finite-cutoff-abutment vs lem-sp-derived-couple-map-uniqueness: existing statement is 'Uniqueness of the induced derived maps.' giving cycle, boundary, image, kernel, derived-map or graded comparisons for an already supplied abstract couple; it does not give the shifted truncation-tail comparison with T^n(L); the new statement identifies a shifted Postnikov cutoff with the actual T^n(L) and its all-integer truncation image filtration.

lem-per-postnikov-finite-cutoff-abutment vs lem-sp-derived-couple-exact: existing statement is 'The derived couple of an exact couple is exact' giving cycle, boundary, image, kernel, derived-map or graded comparisons for an already supplied abstract couple; it does not give the shifted truncation-tail comparison with T^n(L); the new statement identifies a shifted Postnikov cutoff with the actual T^n(L) and its all-integer truncation image filtration.

lem-per-postnikov-finite-cutoff-abutment vs lem-sp-derived-couple-image-prefix: existing statement is 'Recursive image and inclusion properties of iterated derived couples' giving cycle, boundary, image, kernel, derived-map or graded comparisons for an already supplied abstract couple; it does not give the shifted truncation-tail comparison with T^n(L); the new statement identifies a shifted Postnikov cutoff with the actual T^n(L) and its all-integer truncation image filtration.

lem-per-postnikov-finite-cutoff-abutment vs lem-sp-derived-couple-boundary-vanishes: existing statement is 'Boundary vanishing in the cycle quotient.' giving cycle, boundary, image, kernel, derived-map or graded comparisons for an already supplied abstract couple; it does not give the shifted truncation-tail comparison with T^n(L); the new statement identifies a shifted Postnikov cutoff with the actual T^n(L) and its all-integer truncation image filtration.

lem-per-postnikov-additive-exact-couple vs lem-sp-truncation-couple-exact: the existing statement assumes a left exact functor v:A->B and its derived functor on bounded-below complexes; the new statement accepts any additive homological T0:D(A)->B and includes additive maps on every page and filtration. There is no such heart functor with RHom(K,-) as its derived functor when K is an arbitrary bounded-above complex.

lem-per-postnikov-finite-cutoff-abutment vs lem-sp-truncation-abutment-cocone: the existing statement is for Rv with v left exact and cutoff n; the new one works under the shifted amplitude bound and cutoff n+r, proving its actual image filtration and stable-page comparison.

lem-per-postnikov-finite-cutoff-abutment vs thm-sp-truncation-e2: the existing theorem assumes v left exact on the heart and uses p>=0; the new statement assumes a general cohomological family and shifted bound, with a cutoff derived from r. It does not identify any sheaf Ext functor.

lem-per-rhom-local-cohomological-bound vs def-weil-pbc-derived-morphism-presheaves: the existing definition supplies Hom/Isom presheaves for constant ring coefficients; it does not identify the internal-RHom cohomology sheaf or give cohomological boundaries and lower amplitude for a sheaf of rings.

## Retained argument handoff (not proof steps of the new nodes)

The following original proof records are reproduced verbatim from the current returned item. They are implementation guidance for the workers who will split the three new nodes; they are deliberately not hidden proof fields on statement-only nodes.

### Original Step 1 → lem-per-rhom-local-cohomological-bound

Write $T^n(M)=H^nR\mathcal Hom(K,M)$. For every $M$, take a representative $P$ of $K$ and a K-injective representative $I$ of $M$ as in [def-pur-derived-internal-hom]. Applying [lem-pur-rhom-into-kinjective-local] to $P[-n]$ and $I$ identifies $H^n\Gamma(U,\mathcal Hom^\bullet(P,I))$ with $\operatorname{Hom}_{D(\mathcal O_U)}(K|_U,M|_U[n])$: the signed source-shift identification gives $\mathcal Hom^\bullet(P[-n],I)\simeq\mathcal Hom^\bullet(P,I)[n]$, directly from the Hom-complex differential. Exact module sheafification [lem-weil-pbc-ringed-site-module-sheafification-exact] commutes with the kernel, image and quotient defining cohomology. Thus $T^n(M)$ is the sheafification of the presheaf $U\mapsto\operatorname{Hom}_{D(\mathcal O_U)}(K|_U,M|_U[n])$. This identification is additive and natural in $M$ and $U$: the local bijection sends a cocycle $f$ to its derived morphism $Q_U(f)$, so postcomposition and restriction give the same maps on both sides.

Existing cited statements: def-pur-derived-internal-hom, lem-pur-rhom-into-kinjective-local, lem-weil-pbc-ringed-site-module-sheafification-exact.

Source: literature/stacks-project/sites-cohomology.tex — Tag 0A94, lemma-RHom-into-K-injective; Tag 0A95, lemma-RHom-well-defined (its sheafification argument); module sheafification Tag 03EI, sites-modules-lemma-sheafification-exact.

### Original Step 2 → lem-per-rhom-local-cohomological-bound

If $M\in D^{\ge b}$, exact restriction [lem-pur-site-restriction-module-adjunction-exact] preserves cohomology, so $K|_U\in D^{\le r}$ and $M|_U[n]\in D^{\ge b-n}$ for every $U$. For $n<b-r$ one has $b-n>r$, hence $\operatorname{Hom}(K|_U,M|_U[n])=0$ by orthogonality of the standard t-structure [def-sbc-standard-tstructure-derived-category, def-weil-t-structure]. The presheaf in Step 1 is zero, so $T^n(M)=0$. Taking $b=c$ already proves the claimed vanishing below $c-r$; taking $b=0$ gives $\mathcal Ext^p(K,F)=0$ for $p<-r$.

Existing cited statements: lem-pur-site-restriction-module-adjunction-exact, def-sbc-standard-tstructure-derived-category, def-weil-t-structure.

Source: literature/stacks-project/derived.tex — Tag 08J5, remark-truncation-distinguished-triangle; standard orthogonality of upper and lower truncations, as recorded in the cited standard t-structure; Tag 0A94 for Step 1.

### Original Step 3 → lem-per-rhom-local-cohomological-bound

The functors $T^n$ carry a distinguished triangle $A\to B\to C\xrightarrow{w}A[1]$ to a natural long exact sequence. Indeed exact restriction induces a functor on derived categories preserving cone triangles: it commutes with shifts and with the finite direct sums in the cone formula [def-weil-abstract-derived-category, lem-pur-site-restriction-module-adjunction-exact]. Over each $U$, apply [lem-weil-pbc-hom-into-triangle-exact] and rotations and shifts of the restricted triangle. The connecting homomorphism is postcomposition with $w[n]$ followed by the shift identification. This gives an exact sequence of presheaves, and exact module sheafification gives the asserted sequence of the $T^n$ by Step 1. Naturality of these connecting maps follows directly from the last commuting square of a morphism of triangles, $a[1]w=w'c$; hence it also holds after sheafification.

Existing cited statements: def-weil-abstract-derived-category, lem-pur-site-restriction-module-adjunction-exact, lem-weil-pbc-hom-into-triangle-exact, lem-weil-pbc-ringed-site-module-sheafification-exact.

Source: literature/stacks-project/sites-cohomology.tex — Tag 0A94, lemma-RHom-into-K-injective; compare Tag 08JC, lemma-RHom-triangulated. Exactness is proved here from local representable Hom, not inferred from the etale-only lem-sf-hom-triangulated.

### Original Step 4 → lem-per-postnikov-additive-exact-couple

Use the functorial triangles of [lem-weil-pbc-truncation-triangle] for $L$: $\tau_{\le q-1}L\to\tau_{\le q}L\to H^q(L)[-q]\to(\tau_{\le q-1}L)[1]$. Put $D^{p,q}=T^{p+q}(\tau_{\le q}L)$ and $E^{p,q}=T^{p+q}(H^q(L)[-q])$. Let $\alpha:D^{p,q}\to D^{p-1,q+1}$ be induced by the next inclusion, $g:D^{p,q}\to E^{p,q}$ by the quotient, and $f:E^{p,q}\to D^{p+2,q-1}$ by the boundary. Step 3 gives respectively $\ker\alpha=\operatorname{im}f$, $\ker f=\operatorname{im}g$, $\ker g=\operatorname{im}\alpha$, and zero consecutive composites. Thus this is the exact couple of [def-sp-exact-couple]. Its derived-couple construction [lem-sp-derived-couple-exact] gives pages starting at $E_2=E$, with $d_s$ of bidegree $(s,1-s)$ and $E_{s+1}=\ker d_s/\operatorname{im}d_s$.

Existing cited statements: lem-weil-pbc-truncation-triangle, def-sp-exact-couple, lem-sp-derived-couple-exact.

Source: literature/stacks-project/homology.tex — Tags 011Q, definition-exact-couple; 011R, lemma-derived-exact-couple; 011S, definition-spectral-sequence-associated-exact-couple. Use the project E2 indexing and the truncation triangles of derived.tex Tag 08J5.

### Original Step 5 → lem-per-postnikov-additive-exact-couple (E2 identification) and lem-per-postnikov-finite-cutoff-abutment (support)

The right-argument shift comparison [lem-pur-derived-internal-hom-shift-right] identifies $E_2^{p,q}=H^{p+q}R\mathcal Hom(K,H^q(L)[-q])$ naturally with $H^pR\mathcal Hom(K,H^q(L)[0])=\mathcal Ext^p(K,H^qL)$. Step 2 makes this zero for $p<-r$; it is zero for $q<c$ because $H^qL=0$. Also $D^{p,q}=0$ for $q<c$: all cohomology of $\tau_{\le q}L$ is zero, so it is the zero derived object. Iterated pages retain these support bounds since they are subquotients.

Existing cited statements: lem-pur-derived-internal-hom-shift-right, def-sbc-standard-tstructure-derived-category, def-weil-abstract-derived-category.

Source: literature/stacks-project/derived.tex — Tag 08J5, remark-truncation-distinguished-triangle; right-argument shift as in sites-cohomology.tex Tag 08JA (definition of internal Hom).

### Original Step 6 → lem-per-postnikov-finite-cutoff-abutment

Reindex the entire exact couple by $\widetilde D^{P,Q}=D^{P-r,Q}$ and $\widetilde E^{P,Q}=E^{P-r,Q}$. All structure-map bidegrees are unchanged; now $\widetilde D=0$ for $Q<c$, and $\widetilde E=0$ unless $P\ge0,Q\ge c$. Apply [thm-sp-half-plane-convergence] with $a=c$. It gives finite exhaustive separated filtrations on $\widetilde A^N=\widetilde D^{0,N}$, whose graded pieces are $\widetilde E_\infty^{P,N-P}$, and stabilization for $s>\max(Q-c+1,P)$. Returning to the original indices, $N=n+r$, $P=p+r$, $Q=q$; the abutment is initially $A_n=T^n(\tau_{\le n+r}L)$. At total degree $n$, the support conditions are $p\ge-r$ and $q\ge c$ with $p+q=n$, hence exactly $c\le q\le n+r$. Stabilization occurs for $s>\max(q-c+1,p+r)$.

Existing cited statements: thm-sp-half-plane-convergence.

Source: literature/stacks-project/homology.tex — Tags 011T, lemma-spectral-sequence-associated-exact-couple, and 0BDU/0BDV, definition-bounded-ss/lemma-relate-boundedness; the cited project theorem provides the complete half-plane abutment assertion.

### Original Step 7 → lem-per-postnikov-finite-cutoff-abutment

The initial abutment map $a_n:A_n\to T^n(L)$ is an isomorphism. In the canonical truncation triangle $\tau_{\le n+r}L\to L\to\tau_{\ge n+r+1}L\to$, the last unshifted term has lower cohomological bound $n+r+1$ [def-sbc-standard-tstructure-derived-category, lem-sf-derived-truncation-triangle]. By Step 2 its $T^j$ vanish for $j<n+1$, in particular at $j=n-1,n$. The exact sequence of Step 3 therefore reads $0\to A_n\xrightarrow{a_n}T^n(L)\to0$. This also works when $n+r<c$, when $A_n=0$. All $a_n$ are induced by the natural inclusion of the truncation, so these isomorphisms are natural in $L$.

Existing cited statements: def-sbc-standard-tstructure-derived-category, lem-sf-derived-truncation-triangle.

Source: literature/stacks-project/derived.tex — Tag 08J5, remark-truncation-distinguished-triangle; Step 2 supplies the necessary tail vanishing without any completeness or cohomological-dimension assumption.

### Original Step 8 → lem-per-postnikov-finite-cutoff-abutment

Transport the filtration from Step 6 along $a_n$. Explicitly its $p$-th step in the original indexing is $F^pT^n(L)=\operatorname{im}(T^n(\tau_{\le n-p}L)\to T^n(L))$. For $p+r\ge0$, this is precisely the image filtration of [thm-sp-half-plane-convergence] under the preceding reindexing. For $p+r\le0$, $n-p\ge n+r$ and the map from this larger truncation is an isomorphism on $T^n$, by the same tail calculation as Step 7; thus its image is the whole object, as required by that theorem. For $p\ge n-c+1$, the truncation index is $<c$, so the filtration step is zero. Consequently $F^{-r}=T^n(L)$, $F^{n-c+1}=0$, and $F^p/F^{p+1}\simeq E_\infty^{p,n-p}$. This is the finite exhaustive separated convergence of the statement, including degrees with empty support.

Existing cited statements: thm-sp-half-plane-convergence, def-sp-filtration, def-sp-convergence.

Source: literature/stacks-project/homology.tex — Tags 011T and 012F (lemma-filtered-differential-ss-converges), with the project half-plane theorem; image filtration spelled out after reindexing.

### Original Step 9 → lem-per-postnikov-additive-exact-couple

For a morphism $u:L\to L'$, functoriality of the truncation triangles [lem-weil-pbc-truncation-triangle] and the explicit natural boundary of Step 3 give maps $D(u),E(u)$ commuting with $\alpha,f,g$. Apply [lem-sp-couple-morphism] to the reindexed couples: the page maps commute with differentials and with the abutment filtrations and graded identifications. Conjugating the abutment map by the natural $a_n$ of Step 7 gives exactly $T^n(u)$; the filtration map is its restriction to the displayed images in Step 8. These constructions are additive in $u$. In fact the canonical truncation and cohomology maps are additive by their kernel/quotient formulas, and postcomposition in each local derived Hom is additive. Thus $D(u+v)=D(u)+D(v)$ and $E(u+v)=E(u)+E(v)$ initially. At every derived-couple stage the maps on images, kernels and their quotients are uniquely characterized by commuting with their inclusions or quotient projections; the sum of the maps for $u,v$ satisfies those equations for $u+v$. Induction proves additivity on all pages, stable pages, filtration steps and graded maps. Identity and composition follow from the same uniqueness and the cited couple-morphism theorem. This proves all the asserted naturality and additivity.

Existing cited statements: lem-weil-pbc-truncation-triangle, lem-sp-couple-morphism, def-sp-exact-couple, lem-sp-derived-couple-exact.

Source: literature/stacks-project/homology.tex — Tag 011Q, definition-exact-couple (morphisms); Tag 011R, lemma-derived-exact-couple; the project couple-morphism statement supplies compatibility with the canonical abutment filtrations.

The original Step 3 proof uses local restriction, covariant representable exactness and exact sheafification, rather than inferring the cohomological assertion from an etale-only theorem. The original Step 9 induction includes the universal-characterization equations on images, kernels and quotient maps that prove additivity; these are the substantive remaining task of the generic couple node, not an implicit appeal to functoriality alone.

## Existing dependency statement excerpts for the handoff

### def-pur-derived-internal-hom

Let $\mathcal C$ be a site whose underlying category is small and $\mathcal O$ a sheaf of commutative rings on $\mathcal C$ (a ringed site); let $\Mod(\mathcal O)$ be its abelian category of sheaves of $\mathcal O$-modules [def-weil-sheaf-of-modules-category] and $D(\mathcal O)$ the derived category [def-weil-abstract-derived-category] of $\Mod(\mathcal O)$, the localization of the category of cochain complexes of $\mathcal O$-modules [def-pc-cochain-complex-modules] at the quasi-isomorphisms [def-pc-quasi-iso-modules]. For complexes $\mathcal L^\bullet,\mathcal M^\bullet$ of $\mathcal O$-modules, let $\mathcal Hom^\bullet(\mathcal L^\bullet,\mathcal M^\bullet)$ be their Hom complex [def-pur-hom-complex], with terms $\prod_{p\in\mathbf Z}\mathcal Hom_{\mathcal O}(\mathcal L^p,\mathcal M^{p+n})$ and differential $d(\varphi)=d_{\mathcal M}\circ\varphi-(-1)^n\varphi\circ d_{\mathcal L}$. Every complex $\mathcal M^\bullet$ has a K-injective resolution $\mathcal M^\bullet\to\mathcal I^\bullet$ [def-pur-kinjective-complex], which can be chosen functorially in $\mathcal M^\bullet$ [prop-pur-kinjective-resolutions-exist]; fix such a functorial choice $\mathcal M^\bullet\mapsto\mathcal I^\bullet(\mathcal M^\bullet)$. For $L,M\in D(\mathcal O)$, represented by complexes $\mathcal L^\bullet$ and $\mathcal M^\bullet$, the *derived internal Hom* is

$$
 R\mathcal Hom_{\mathcal O}(L,M)
 =\mathcal Hom^\bullet\bigl(\mathcal L^\bullet,\mathcal I^\bullet(\mathcal M^\bullet)\bigr)\in D(\mathcal O).
$$

The assignment $(\mathcal L^\bullet,\mathcal M^\bullet)\mapsto\mathcal Hom^\bullet(\mathcal L^\bullet,\mathcal I^\bullet(\mathcal M^\bullet))$ is a functor on pairs of complexes, contravariant in the first and covariant in the second variable; it sends a quasi-isomorphism in either variable to a quasi-isomorphism [lem-pur-rhom-well-defined] (a quasi-isomorphism $\mathcal M^\bullet\to(\mathcal M')^\bullet$ induces a quasi-isomorphism $\mathcal I^\bullet(\mathcal M^\bullet)\to\mathcal I^\bullet((\mathcal M')^\bullet)$ of K-injective complexes, by the two-out-of-three property of quasi-isomorphisms). Hence, by the universal property of the localization, it induces a functor $R\mathcal Hom_{\mathcal O}:D(\mathcal O)^{\mathrm{op}}\times D(\mathcal O)\to D(\mathcal O)$. By the same lemma, the object obtained from any other K-injective complex $\mathcal I'^\bullet$ quasi-isomorphic to $\mathcal M^\bullet$ and any other representative of $L$ is canonically isomorphic to it.

### def-sbc-standard-tstructure-derived-category

Let $\mathcal A$ be an abelian category and $D(\mathcal A)$ its derived category, with cohomology functors $H^i:D(\mathcal A)\to\mathcal A$ [def-weil-abstract-derived-category]. For $n\in\mathbf Z$ let $D(\mathcal A)^{\le n}$ (resp. $D(\mathcal A)^{\ge n}$) be the strictly full subcategory of objects $K$ with $H^i(K)=0$ for all $i>n$ (resp. for all $i<n$); equivalently, of objects isomorphic in $D(\mathcal A)$ to (the image of) a complex $K^\bullet$ with $K^i=0$ for $i>n$ (resp. $i<n$). The pair $(D(\mathcal A)^{\le0},D(\mathcal A)^{\ge0})$ is a t-structure on the triangulated category $D(\mathcal A)$ [def-weil-t-structure], the *standard* (or *natural*) t-structure, with $D(\mathcal A)^{\le n}=D(\mathcal A)^{\le0}[-n]$ and $D(\mathcal A)^{\ge n}=D(\mathcal A)^{\ge0}[-n]$. For a complex $K$ the truncation triangle of axiom (iii) is the image of the short exact sequence $0\to\tau_{\le0}K\to K\to K/\tau_{\le0}K\to0$, where $\tau_{\le0}K$ is the subcomplex $\cdots\to K^{-1}\to\ker(d^0)\to0\to\cdots$ of $K$, and $K/\tau_{\le0}K$ lies in $D(\mathcal A)^{\ge1}$.

### def-sp-convergence

In the situation of [def-sp-exact-couple], regard all cycle and boundary
objects as subobjects of the initial page $E_2$. Set $Z_2=E_2$, $B_2=0$.
Given $E_r=Z_r/B_r$, define $Z_{r+1}\subseteq Z_r$ as the inverse image of
$\ker d_r$, and $B_{r+1}\subseteq Z_r$ as the inverse image of
$\operatorname{im}d_r$ under $Z_r\twoheadrightarrow E_r$, component by
component. Thus $E_{r+1}=Z_{r+1}/B_{r+1}$, the $Z_r$ decrease, and the $B_r$
increase inside $E_2$. When these limits exist, put
$Z_\infty=\bigcap_rZ_r$, $B_\infty=\bigcup_rB_r$, and
$E_\infty=Z_\infty/B_\infty$. The couple is *regular* if each
$Z_r^{p,q}\subseteq E_2^{p,q}$ is eventually constant. It is *complete* if
the subobjects $\operatorname{im}(\alpha^r:D^{p+r,q-r}\to D^{p,q})$ have zero
intersection for every $(p,q)$. It is *bounded* if, for every total degree
$n$, only finitely many pairs $(p,q)$ with $p+q=n$ satisfy $E_2^{p,q}\ne0$.
Assume that for every $n$ the colimit
$A^n:=\operatorname{colim}_{p\to-\infty}D^{p,n-p}$ along $\alpha$ exists in
$\mathcal A$. Define $F^pA^n$ to be the image of the canonical map
$D^{p,n-p}\to A^n$; since $D^{p+1,n-p-1}\to A^n$ factors through $\alpha$, one has
$F^{p+1}A^n\subseteq F^pA^n$, so this is a decreasing filtration in the sense of
[def-sp-filtration]. The exact-couple map $g:D^{p,q}\to E_2^{p,q}$ lands in
$Z_\infty^{p,q}$ and therefore gives a canonical map
$D^{p,q}\to E_\infty^{p,q}$. The filtration map gives a canonical map
$D^{p,q}\to\operatorname{gr}^pA^{p+q}$. The couple *weakly converges
to* the filtered objects $(A^n,F)$ if these two maps are both onto and have
the same kernel, so they induce canonical isomorphisms
$E_\infty^{p,q}\cong\operatorname{gr}^pA^{p+q}$. It *abuts to* $(A,F)$ if it
weakly converges and $\bigcap_pF^pA^n=0$ and $\bigcup_pF^pA^n=A^n$ for
every $n$. It *converges to* $(A,F)$ if it is regular, abuts to $(A,F)$,
and $A^n\cong\varprojlim_p A^n/F^pA^n$ for every $n$ (the abutment);
these are the convergence conventions of Stacks Tag 012U.

### def-sp-exact-couple

Let $\mathcal A$ be an abelian category [def-sp-abelian]. An *exact couple*
$(D,E,\alpha,f,g)$ inside the bigraded objects $D=\bigoplus D^{p,q}$,
$E=\bigoplus E^{p,q}$ consists of maps of bidegrees

$$
 \alpha:D^{p,q}\to D^{p-1,q+1}\quad(-1,+1),\qquad
 f:E^{p,q}\to D^{p+2,q-1}\quad(+2,-1),\qquad
 g:D^{p,q}\to E^{p,q}\quad(0,0)
$$

such that the composite of two consecutive structure maps is zero and at
every $(p,q)$ the following exactness conditions hold (each comparing
subobjects of one single object):

$$
 \ker\!\Bigl(\alpha:D^{p,q}\to D^{p-1,q+1}\Bigr)
  =\operatorname{im}\!\Bigl(f:E^{p-2,q+1}\to D^{p,q}\Bigr),
$$

$$
 \ker\!\Bigl(f:E^{p,q}\to D^{p+2,q-1}\Bigr)
  =\operatorname{im}\!\Bigl(g:D^{p,q}\to E^{p,q}\Bigr),
$$

$$
  \ker\!\Bigl(g:D^{p,q}\to E^{p,q}\Bigr)
   =\operatorname{im}\!\Bigl(\alpha:D^{p+1,q-1}\to D^{p,q}\Bigr).
$$

(The bidegrees are those of the truncation couple of a t-structure
filtration, with the abutment in total degree $p+q$; they are the convention
in which the hypercohomology spectral sequence has $E_2^{p,q}\Rightarrow
\mathcal H^{p+q}$.) Setting $d:=g\circ f:E^{p,q}\to E^{p+2,q-1}$ (bidegree
$(+2,-1)$), the identity $f\circ g=0$ gives $d\circ d=0$, and the *derived
couple* is

$$
 D'^{p,q}:=\operatorname{im}\!\bigl(\alpha:D^{p+1,q-1}\to D^{p,q}\bigr),
 \qquad
 E'^{p,q}:=\frac{\ker\!\bigl(d:E^{p,q}\to E^{p+2,q-1}\bigr)}
                    {\operatorname{im}\!\bigl(d:E^{p-2,q+1}\to E^{p,q}\bigr)},
$$

with

$$
 \alpha':=\alpha|_{D'},\qquad
 f'([x]):=[f(x)]\ \ (x\in\ker d),\qquad
 g'(y):=\overline{g(y')}\ \ (y=\alpha(y')\in D'^{p,q},\ y'\in D^{p+1,q-1}),
$$

so that $\alpha':D'^{p,q}\to D'^{p-1,q+1}$, $f':E'^{p,q}\to D'^{p+2,q-1}$ and
$g':D'^{p,q}\to E'^{p+1,q-1}$ have bidegrees $(-1,+1)$, $(+2,-1)$ and
$(+1,-1)$. These maps are well defined because $f(\ker
d)\subseteq\ker g=\operatorname{im}\alpha$ and $f(\operatorname{im}d)=f\circ g\circ f(\cdot)=0$,
because $d(g(y'))=g\circ f\circ g\,(y')=0$, and because changing $y'$ by
$\ker\alpha=\operatorname{im}f$ changes $g(y')$ by $\operatorname{im}d$.
The derived couple has the shape above except that $g'$ has bidegree
$(+1,-1)$; more generally, call a couple as above but with $g$ of bidegree
$(s,-s)$ ($s\geq0$) a couple of type $s$, and form its derived couple by the
same formulas ($d=g\circ f$ of bidegree $(s+2,-s-1)$, $g'$ of bidegree
$(s+1,-s-1)$). The *spectral sequence of the couple* $C=(D,E,\alpha,f,g)$
is $(E_r,d_r)_{r\geq2}$ where $C_2=C$, $C_{r+1}=C_r'$ is the derived couple
of the type-$(r-2)$ couple $C_r=(D_r,E_r,\alpha_r,f_r,g_r)$, and
$d_r=g_r\circ f_r$, of bidegree $(+r,1-r)$. Thus $E_2=E$, $d_2=d$,
$E_3=E'$, $d_3=g'\circ f'$ (bidegree $(+3,-2)$), and
$E_{r+1}^{p,q}=\ker(d_r)/\operatorname{im}(d_r)$ at $E_r^{p,q}$. That each
$C_r$ is again exact, so that the recursion is defined for all $r$, is the
lemma lem-sp-derived-couple-exact (Stacks Lemma 12.21.2, Tag 011R), stated
about this definition.

(Stacks Project: Definitions 12.21.1 and 12.21.3 (Tags
[011Q](https://stacks.math.columbia.edu/tag/011Q),
[011S](https://stacks.math.columbia.edu/tag/011S)), Lemma 12.21.2 (Tag
[011R](https://stacks.math.columbia.edu/tag/011R)), and the shift-functor
variant Remark 12.21.5 (Tag
[0AMJ](https://stacks.math.columbia.edu/tag/0AMJ)).)

### def-sp-filtration

Let $\mathcal A$ be an abelian category [def-sp-abelian]. A *decreasing
filtration* $F$ on an object $A\in\mathcal A$ is a family
$(F^nA)_{n\in\mathbb Z}$ of subobjects of $A$ with
$A\supseteq\cdots\supseteq F^nA\supseteq F^{n+1}A\supseteq\cdots\supseteq0$. A
*filtered object* is a pair $(A,F)$. A morphism $(A,F)\to(B,F)$ is a
morphism $\varphi:A\to B$ in $\mathcal A$ such that
$\varphi(F^iA)\subseteq F^iB$ for every $i\in\mathbb Z$; filtered objects
form a category $\operatorname{Fil}(\mathcal A)$. For a subobject $X\subseteq A$,
the induced filtration is $F^nX=X\cap F^nA$; for a surjection
$\pi:A\to Y$, the quotient filtration is $F^nY=\pi(F^nA)$. The
filtration is *finite* if $F^nA=A$ and $F^mA=0$ for some integers $n,m$;
it is *separated* if the biggest subobject contained in every $F^iA$ is
$0$, and *exhaustive* if the smallest subobject containing every $F^iA$ is
$A$. Its graded pieces are
$\operatorname{gr}^nA:=F^nA/F^{n+1}A$.
(*Stacks Project: Homology, Definition 12.19.1, label
`definition-filtered` (Tag [0121](https://stacks.math.columbia.edu/tag/0121)).*)

### def-weil-abstract-derived-category

Let $\mathcal A$ be an abelian category [def-sp-abelian]. A cochain complex $K$ of $\mathcal A$ consists of objects $K^r$, $r\in\mathbf Z$, and differentials $d^r:K^r\to K^{r+1}$ satisfying $d^{r+1}d^r=0$; a morphism of complexes is a family of morphisms $f^r:K^r\to L^r$ commuting with the differentials. Its $r$-th cohomology object is $H^r(K)=\ker d^r/\operatorname{im}d^{r-1}$, functorial in $K$. A quasi-isomorphism is a morphism of complexes $f$ such that $H^r(f)$ is an isomorphism for every $r$. The derived category $D(\mathcal A)$ is the localization $Q:\mathrm{CoCh}(\mathcal A)\to D(\mathcal A)$ of the category of cochain complexes at the quasi-isomorphisms (equivalently, of the homotopy category $K(\mathcal A)$ at the images of the quasi-isomorphisms), with morphism sizes taken in the chosen universe [def-weil-size-convention]. Since every $H^r$ inverts quasi-isomorphisms it factors uniquely through $Q$, giving the cohomology functors $H^r:D(\mathcal A)\to\mathcal A$ with $H^r\circ Q\cong H^r$. $D(\mathcal A)$ is additive and carries the triangulated structure [def-weil-triangulated-category] induced from complexes: the shift is $(K[1])^r=K^{r+1}$ with differential $-d_K$, and a triangle of $D(\mathcal A)$ is distinguished if it is isomorphic to the image under $Q$ of the cone triangle $K\xrightarrow{f}L\xrightarrow{i}C(f)\xrightarrow{-p}K[1]$ of a morphism of complexes $f$, where $C(f)^r=L^r\oplus K^{r+1}$ with differential $\begin{pmatrix}d_L&f\\0&-d_K\end{pmatrix}$ and $i$, $p$ the inclusion and the projection. With these, $D(\mathcal A)$ is a triangulated category and $Q$ commutes with the shifts. See [Stacks Project, Section 13.11](https://stacks.math.columbia.edu/tag/05RR), Definition 05RU.

### def-weil-t-structure

A *t-structure* on a triangulated category $\mathcal T$ is a pair $(\mathcal
T^{\le0},\mathcal T^{\ge0})$ of strictly full subcategories such that

1. $\mathcal T^{\le0}[1]\subseteq\mathcal T^{\le0}$ and $\mathcal
   T^{\ge0}[-1]\subseteq\mathcal T^{\ge0}$;
2. $\Hom_{\mathcal T}(A,B[-1])=0$ for all $A\in\mathcal T^{\le0}$ and
   $B\in\mathcal T^{\ge0}$;
3. every $K\in\mathcal T$ occurs in a distinguished triangle $A\to K\to
   B[-1]\to A[1]$ with $A\in\mathcal T^{\le0}$ and $B\in\mathcal T^{\ge0}$.

Write $\mathcal T^{\le n}=\mathcal T^{\le0}[-n]$ and $\mathcal T^{\ge
n}=\mathcal T^{\ge0}[-n]$. The *heart* is $\mathcal T^{\le0}\cap\mathcal
T^{\ge0}$, and the t-structure is *bounded* if every object of $\mathcal T$
lies in $\mathcal T^{\le n}\cap\mathcal T^{\ge m}$ for some $m\le n$. A
bounded t-structure carries truncation functors $\tau^{\le n},\tau^{\ge
n}:\mathcal T\to\mathcal T$ and distinguished truncation triangles

$$
 \tau^{\le n}K\longrightarrow K\longrightarrow
 \tau^{\ge n+1}K\longrightarrow\tau^{\le n}K[1],
$$

characterized by $\tau^{\le n}K\in\mathcal T^{\le n}$ and $\tau^{\ge
n+1}K\in\mathcal T^{\ge n+1}$.

(*Source note:* no Stacks Project entry states this form: Stacks defines no
t-structure on a triangulated category. Its nearest entries are the
truncation of a complex of an abelian category, Homological Algebra, Section
12.15 (Tag [0118](https://stacks.math.columbia.edu/tag/0118)), where the
canonical truncations $\tau_{\le n}$, $\tau_{\ge n}$ of a (co)chain complex
are defined with the properties $H^i(\tau_{\le n}A^\bullet)=H^i(A^\bullet)$
for $i\le n$ and $0$ for $i>n$, and the canonical distinguished triangle
$\tau_{\le a}K^\bullet\to K^\bullet\to\tau_{\ge a+1}K^\bullet\to (\tau_{\le
a}K^\bullet)[1]$ of the Stacks truncation remark (Tag
[08J5](https://stacks.math.columbia.edu/tag/08J5), in $D(\mathcal A)$ for an
abelian $\mathcal A$). Difference: those entries truncate complexes of one
fixed abelian category inside $D(\mathcal A)$; they state no t-structure
axioms on an abstract triangulated category, no heart, no boundedness, and no
truncation functors on such a category — pages checked for a counterpart: the
tables of contents of Chapters 12, 13 and 21 and Sections 12.4, 12.5, 12.15,
13.11, 13.12 and 13.34, and the table of contents of Chapter 61. The
blueprint adds the axiom list together with the truncation functors
$\tau^{\le n},\tau^{\ge n}$ and their triangles, the structure on which the
integral and rational coefficient categories of this manuscript rest.)

### lem-pur-derived-internal-hom-shift-right

On a small ringed site (C,R), with the unbounded derived category D(R) and the internal derived Hom of [def-pur-derived-internal-hom], fix P in D(R) and n in Z. Write F_P(Q)=RHom(P,Q), with morphisms RHom(id_P,q). There is a natural isomorphism F_P followed by shift(n) to shift(n) followed by F_P. No boundedness or K-flatness is assumed.

### lem-pur-rhom-into-kinjective-local

Let $\mathcal C$ be a site and $\mathcal O$ a sheaf of commutative rings on $\mathcal C$, and let $U$ be an object of $\mathcal C$; write $\mathcal O_U=\mathcal O|_U$ for the restriction to the localized site $\mathcal C/U$ and $Q_U$ for the localization functor from cochain complexes of $\mathcal O_U$-modules to the derived category $D(\mathcal O_U)$ [def-weil-abstract-derived-category]. Let $\mathcal L^\bullet$ be a cochain complex of $\mathcal O$-modules [def-pc-cochain-complex-modules] and $\mathcal I^\bullet$ a K-injective complex of $\mathcal O$-modules [def-pur-kinjective-complex]. A degree-$0$ cocycle of $\Gamma(U,\mathcal Hom^\bullet(\mathcal L^\bullet,\mathcal I^\bullet))$ [def-pur-hom-complex] is a morphism of complexes $f:\mathcal L^\bullet|_U\to\mathcal I^\bullet|_U$, and the map
$$
 H^0\bigl(\Gamma(U,\mathcal Hom^\bullet(\mathcal L^\bullet,\mathcal I^\bullet))\bigr)\longrightarrow\operatorname{Hom}_{D(\mathcal O_U)}\bigl(Q_U(\mathcal L^\bullet|_U),Q_U(\mathcal I^\bullet|_U)\bigr),\qquad [f]\longmapsto Q_U(f),
$$
is well defined and bijective.

### lem-pur-site-restriction-module-adjunction-exact

Let $\mathcal C$ be a Grothendieck site [def-weil-pbc-sites-and-cohomology], let $U$ be an object, and let $\mathcal O$ be a sheaf of commutative rings on $\mathcal C$. Give $\mathcal C/U$ the localized topology and write $\operatorname{Mod}_{\mathcal O}(\mathcal C)$ and $\operatorname{Mod}_{\mathcal O|_U}(\mathcal C/U)$ for the categories of sheaves of modules [def-pur-localized-ringed-site] [def-weil-sheaf-of-modules-category]. Let $j_U^*:\operatorname{Mod}_{\mathcal O}(\mathcal C)\to\operatorname{Mod}_{\mathcal O|_U}(\mathcal C/U)$ be restriction, $G\mapsto G|_U$ [def-pur-localized-ringed-site], and for a sheaf $F$ of $\mathcal O|_U$-modules let $j_{U!}F=P_F^\#$ be the sheafification [def-weil-presheaf-modules-sheafification] of its extension-by-zero presheaf of $\mathcal O$-modules $P_F$ [def-weil-extension-by-zero-presheaf], functorial in $F$ (the *extension by zero*). Then $j_U^*$ is an exact functor, and $j_{U!}$ is an exact functor left adjoint to it: $\operatorname{Hom}_{\mathcal O}(j_{U!}F,G)\cong\operatorname{Hom}_{\mathcal O|_U}(F,j_U^*G)$ naturally in the $\mathcal O|_U$-module $F$ and the $\mathcal O$-module $G$.

### lem-sf-derived-truncation-triangle

Let $\mathcal C$ be an abelian category, $D(\mathcal C)$ its derived category [def-weil-abstract-derived-category] with cohomology functors $H^n$, and let $K\in D(\mathcal C)$ and $b\in\mathbf Z$. There is a distinguished triangle\n$$\nK'\longrightarrow K\longrightarrow K''\longrightarrow K'[1]\n$$\nwith $H^n(K')=0$ for all $n>b-1$ and $H^n(K'')=0$ for all $n<b$ (namely $K'=\tau_{\leq b-1}K$, $K''=\tau_{\geq b}K$ for the canonical t-structure).

### lem-sp-couple-morphism

Let $(D,E,\alpha,f,g)$ and $(D',E',\alpha',f',g')$ be exact couples [def-sp-exact-couple] in the same abelian category. A morphism of exact couples is a pair of maps $t_D:D\to D'$ and $t_E:E\to E'$ preserving bidegrees and satisfying $t_D\alpha=\alpha't_D$, $t_Df=f't_E$, and $t_Eg=g't_D$. Such a morphism induces, for every $r$, a morphism $E_r\to E'_r$ of the spectral sequences, compatible with the differentials. If both couples satisfy the hypotheses of [thm-sp-half-plane-convergence], then for every total degree $n$ the map $t_D:D^{0,n}\to D'^{0,n}$ of their canonical abutments respects the filtrations [def-sp-filtration] constructed there, and the induced map $\operatorname{gr}^pA^n\to\operatorname{gr}^pA'^n$ on the associated graded pieces is, under the identifications $E_\infty^{p,n-p}\cong\operatorname{gr}^pA^n$ of [thm-sp-half-plane-convergence], the map $E_\infty\to E'_\infty$ [def-sp-convergence] induced by $t_E$.

### lem-sp-derived-couple-exact

Let $\mathcal A$ be an abelian category [def-sp-abelian] and $s\geq0$ an integer. An *exact couple of type $s$* $(D,E,\alpha,f,g)$ in $\mathcal A$ consists of objects $D^{p,q},E^{p,q}$ ($p,q\in\mathbf Z$) and morphisms $\alpha:D^{p,q}\to D^{p-1,q+1}$, $f:E^{p,q}\to D^{p+2,q-1}$, $g:D^{p,q}\to E^{p+s,q-s}$ such that at every $(p,q)$ the three sequences
$$E^{p-2,q+1}\xrightarrow{f}D^{p,q}\xrightarrow{\alpha}D^{p-1,q+1},\qquad D^{p-s,q+s}\xrightarrow{g}E^{p,q}\xrightarrow{f}D^{p+2,q-1},\qquad D^{p+1,q-1}\xrightarrow{\alpha}D^{p,q}\xrightarrow{g}E^{p+s,q-s}$$
are complexes and exact in the middle (the kernel of each arrow is the image of its predecessor). Type $0$ is the exact couple of [def-sp-exact-couple]. Put $d=g\circ f:E^{p,q}\to E^{p+s+2,q-s-1}$. The *derived couple* $(D',E',\alpha',f',g')$ is: $D'^{p,q}=\operatorname{im}(\alpha:D^{p+1,q-1}\to D^{p,q})$, with inclusion $\iota:D'^{p,q}\hookrightarrow D^{p,q}$ and epimorphism $\bar\alpha:D^{p+1,q-1}\twoheadrightarrow D'^{p,q}$, $\iota\circ\bar\alpha=\alpha$; $E'^{p,q}=\ker(d:E^{p,q}\to E^{p+s+2,q-s-1})/\operatorname{im}(d:E^{p-s-2,q+s+1}\to E^{p,q})$ with projection $\pi$; $\alpha':D'^{p,q}\to D'^{p-1,q+1}$ the unique map with $\iota\circ\alpha'=\alpha\circ\iota$; $f':E'^{p,q}\to D'^{p+2,q-1}$ the unique map with $\iota\circ f'\circ\pi=f|_{\ker d}$; $g':D'^{p,q}\to E'^{p+s+1,q-s-1}$ the unique map with $g'\circ\bar\alpha=\pi\circ\hat g$, where $\hat g:D^{p+1,q-1}\to\ker(d)\subseteq E^{p+s+1,q-s-1}$ is the factorization of $g$. Then:

1. $\ker(d:E^{p,q}\to E^{p+s+2,q-s-1})=f^{-1}(\ker g)=f^{-1}(\operatorname{im}\alpha)$, with $\ker g=\operatorname{im}\alpha\subseteq D^{p+2,q-1}$, and $\operatorname{im}(d:E^{p-s-2,q+s+1}\to E^{p,q})=g(\operatorname{im}f)=g(\ker\alpha)$, with $\operatorname{im}f=\ker\alpha\subseteq D^{p-s,q+s}$ (equalities of subobjects of $E^{p,q}$; $f^{-1}$ is the pullback of a subobject, $g(S)$ the image of $S\hookrightarrow D\xrightarrow{g}E$).
2. The maps $\alpha',f',g'$ exist and are unique as stated (in particular $d\circ d=0$, $f(\ker d)\subseteq\operatorname{im}\alpha$, $g$ factors through $\ker d$, and $\pi\circ\hat g$ vanishes on $\ker\bar\alpha$).
3. The derived couple is an exact couple of type $s+1$: $\alpha'$ has bidegree $(-1,+1)$, $f'$ bidegree $(+2,-1)$, $g'$ bidegree $(s+1,-s-1)$, and its three sequences are complexes, exact in the middle.
4. (Iteration, Stacks 011S.) For an exact couple $C=(D,E,\alpha,f,g)$ of [def-sp-exact-couple] put $C_2=C$ and $C_{r+1}=C_r'$. Then $C_r=(D_r,E_r,\alpha_r,f_r,g_r)$ is an exact couple of type $r-2$ for all $r\geq2$; $D_r^{p,q}=\operatorname{im}(\alpha^{r-2}:D^{p+r-2,q-r+2}\to D^{p,q})$ as a subobject of $D^{p,q}$, $\alpha_r$ is the restriction of $\alpha$, $f_r$ has bidegree $(+2,-1)$, $g_r$ bidegree $(r-2,2-r)$, $d_r=g_r\circ f_r$ bidegree $(r,1-r)$, and $E_{r+1}^{p,q}=\ker(d_r\text{ out of }E_r^{p,q})/\operatorname{im}(d_r\text{ into }E_r^{p,q})$.

### lem-weil-pbc-hom-into-triangle-exact

Let $\mathcal T$ be a pre-triangulated category [def-weil-triangulated-category], $X\xrightarrow{u}Y\xrightarrow{v}Z\xrightarrow{d}X[1]$ a distinguished triangle and $W$ an object of $\mathcal T$. (i) $v\circ u=0$. (ii) If $a:W\to Y$ satisfies $v\circ a=0$, there is $b:W\to X$ with $a=u\circ b$ (exactness of $\Hom(W,X)\to\Hom(W,Y)\to\Hom(W,Z)$). (iii) If $c:W\to X[1]$ satisfies $u[1]\circ c=0$, there is $k:W\to Z$ with $c=d\circ k$ (exactness of $\Hom(W,Z)\to\Hom(W,X[1])\to\Hom(W,Y[1])$).

### lem-weil-pbc-ringed-site-module-sheafification-exact

Let $(\mathcal C,\mathcal O)$ be a ringed site [def-weil-pbc-sites-and-cohomology], let $\mathrm{PMod}(\mathcal C,\mathcal O)$ be the abelian category of presheaves of $\mathcal O$-modules and let $\mathrm{Mod}(\mathcal C,\mathcal O)$ be the full subcategory of sheaves of $\mathcal O$-modules [def-weil-sheaf-of-modules-category], with module sheafification $\#:\mathrm{PMod}(\mathcal C,\mathcal O)\to\mathrm{Mod}(\mathcal C,\mathcal O)$ left adjoint to the inclusion [def-weil-presheaf-modules-sheafification]. Then $\#$ preserves finite limits and finite colimits; in particular, it is exact.

### lem-weil-pbc-truncation-triangle

Let $\mathcal A$ be an abelian category with derived category $D(\mathcal A)$ [def-weil-abstract-derived-category], a triangulated category [def-weil-triangulated-category], with cohomology functors $H^n$ and shift $[1]$, $(M[1])^r=M^{r+1}$, $d_{M[1]}=-d_M$. For a complex $K$ of $\mathcal A$ and $q\in\mathbf Z$ let $\tau_{\leq q}K$ be the canonical truncation, the subcomplex $\cdots\to K^{q-2}\to K^{q-1}\to\Ker(d^q_K)\to0\to\cdots$ of $K$ (the truncation of the standard t-structure [def-sbc-standard-tstructure-derived-category]), so that $\tau_{\leq q-1}K\subseteq\tau_{\leq q}K$, and let $H^q(K)[-q]$ be the complex with the single object $H^q(K)$ placed in degree $q$. Let $i_q:\tau_{\leq q-1}K\to\tau_{\leq q}K$ be the inclusion and $j_q:\tau_{\leq q}K\to H^q(K)[-q]$ the morphism of complexes which in degree $q$ is the projection $\Ker(d^q_K)\to H^q(K)$ and zero in the other degrees. Then there is a unique morphism $k_q:H^q(K)[-q]\to(\tau_{\leq q-1}K)[1]$ in $D(\mathcal A)$ such that
$$
 \tau_{\leq q-1}K\xrightarrow{\,i_q\,}\tau_{\leq q}K\xrightarrow{\,j_q\,}H^q(K)[-q]\xrightarrow{\,k_q\,}(\tau_{\leq q-1}K)[1]
$$
is a distinguished triangle $T_q(K)$ of $D(\mathcal A)$ (namely $k_q=\delta\circ\bar j_q^{-1}$, where $\delta$ is the boundary morphism of the distinguished triangle of the short exact sequence of complexes $0\to\tau_{\leq q-1}K\to\tau_{\leq q}K\to\tau_{\leq q}K/\tau_{\leq q-1}K\to0$ and $\bar j_q:\tau_{\leq q}K/\tau_{\leq q-1}K\to H^q(K)[-q]$ is the quasi-isomorphism induced by $j_q$). The triangle is functorial in $K$: $\tau_{\leq q}$, $\tau_{\leq q-1}$ and $H^q(-)[-q]$ preserve quasi-isomorphisms and so act on morphisms of $D(\mathcal A)$ [lem-weil-pbc-truncation-descends], and for every morphism $f:K\to L$ of $D(\mathcal A)$ between complexes $K,L$ the triple $(\tau_{\leq q-1}f,\tau_{\leq q}f,H^q(f)[-q])$ is a morphism of triangles $T_q(K)\to T_q(L)$. If $K$ is bounded below (as a complex, or only in cohomology: $H^n(K)=0$ for $n\ll0$), so are the three terms; in particular for $\mathcal A=\Ab(T_{\Et})$ the triangle lies in $\Dplus(T_{\Et})$ [def-weil-pbc-derived-categories].

### thm-sp-half-plane-convergence

Let $(D,E_2,\alpha,f,g)$ be the exact couple of
[def-sp-exact-couple]. Assume $D^{p,q}=0$ for $q<a$, and $E_2^{p,q}=0$ unless
$p\geq0$ and $q\geq a$. Put $A^n=D^{0,n}$. Then total degree $n$ contains
only $a\leq q\leq n$, and each entry $E_r^{p,q}$ has stabilized when

$$
 r>\max(q-a+1,\,p),
$$

with the canonical identification $E_r^{p,q}=E_{r+1}^{p,q}$ supplied by page
cohomology. For $q\leq n$, set
$G_qA^n=\operatorname{im}(D^{n-q,q}\xrightarrow{\alpha^{n-q}}A^n)$, and set
$G_qA^n=A^n$ for $q\geq n$. The decreasing filtration
[def-sp-filtration] $F^pA^n=G_{n-p}A^n$ is finite, exhaustive and separated,
and $E_\infty^{p,q}\cong F^pA^{p+q}/F^{p+1}A^{p+q}$. The couple is regular
and complete in the sense of [def-sp-convergence].

## What remains

The three new nodes intentionally remain statement-only for parallel future stage-1 workers, as ordered. There is no unfinished part of this item's assembly. Dry-run and push results are recorded by the delivery command.
