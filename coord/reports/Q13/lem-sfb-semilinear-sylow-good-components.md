# Stage-1 repair: lem-sfb-semilinear-sylow-good-components

Q13, direct delivery, 2026-10-22. This repairs the human's re-split instruction, not a statement change. The sandbox initially held dispatcher briefs only: I compared with the live item and retained its complete thirteen-step proof and prior NJ report below. Its current Sheaf theorem still ends in sorry. No finished project declaration states the item; no attachment is claimed. No Lean was written, and no compiler, Lake, build, git command in the shared repository, or other agent was used. All writes are in the assigned sandbox.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-semilinear-sylow-good-components.json: original statement preserved verbatim; five-step assembly, 1733 characters in proof texts, below 3000.
- dag/nodes/sec-six-functors-basics/lem-sfb-sylow-constants-field-degree.json: statement, unsplit; no Mathlib match. Owns old steps 1--2.
- dag/nodes/sec-six-functors-basics/lem-sfb-semilinear-quotient-projective-geometry.json: statement, unsplit; no Mathlib match. Owns old steps 3--6.
- dag/nodes/sec-six-functors-basics/lem-sfb-sylow-generic-prime-to-ell-lift.json: statement, unsplit; no Mathlib match. Owns old steps 7--9.
- dag/nodes/sec-six-functors-basics/lem-sfb-clopen-generic-projective-cover.json: statement, unsplit; no Mathlib match. Owns old steps 10--12.
- dag/nodes/sec-six-functors-basics/lem-sfb-clopen-geometric-categorical-quotient.json: statement, unsplit; no Mathlib match. Owns old step 13.
- citations.json: one verbatim statement quotation for each of the five parent-step citations.
- report.md: this signed review, exact ownership map and retained arguments. research/ stores the original JSON, previous report, query plan and complete actual msearch outputs. searches.jsonl is generated only by msearch.py.

## Attachments

None. I searched lean/WeilConjectures/ by exact blueprint tag and by semilinear, Sylow, fixed-field and categorical-quotient concepts, and read lean/Sheaf/AlgebraicGeometry/SemilinearSylowGoodComponents.lean. Its declaration AlgebraicGeometry.semilinear_sylow_good_components, line 190, has proof sorry; references to its node elsewhere are not proofs. Mathlib declarations do not qualify as project attachments.

## WANTED

None. The ILO PDF, current blueprint, Stacks sources and Mathlib source used for this repair are available locally. These five statements extract and generalize separate arguments of the already reviewed proof; I do not attribute their exact wording to ILO.

## Errors and changes

The return identifies a 9184-character proof and requires at least three independently stateable new unsplit nodes and at most 3000 characters of parent proof. The repair adds five, with argument workloads 1225, 2905, 2266, 1902 and 886 characters respectively (the exact retained old paragraphs are authoritative). Constants arithmetic, quotient geometry, generic selection and projective assembly are now independent tasks. The smaller final node isolates the categorical extension argument; it is valid over arbitrary schemes, so its task is useful independently of alterations. No single new node contains the whole assertion, and none assumes the other conclusions of the item. This is the expressly requested re-split: the new nodes have no proof steps or proof dependencies. The original arguments have not been shortened into vague references: every original paragraph and its original node citations is retained verbatim in the ownership appendix below.

No STATEMENT-DISPUTED correction was necessary. The item's statement, source, statement dependencies and Lean record are unchanged. Its image-of-L qualification and componentwise rather than total degree convention remain essential. I retained maintainer-owned fields for deliver.py to merge against the current server baseline. No unit or chapter is edited. The blueprint ancestor tool returns None for this already created chain; the new provenance carries that exact value, the existing via chain prefixed by this item, a specific location in the existing blueprint provenance, and old-step ownership. All same_as fields are [] after whole-blueprint searches.

The old proof's 0BD4 norm/ample route is preserved, including the finite structural projectivity and closed-immersion conversion; I did not replace it by the dropped general projective-quotient existence result. The old component stabilizer and faithful-image computations remain in the generic-lift task. The graph/closed-image argument remains in the component-cover task. The disjoint-union extension argument remains in the arbitrary-scheme clopen-restriction task. The formerly elementary step 13 is deliberately made a separate task under the human's re-split instruction; it proves a general categorical universal property rather than merely restricting a finite ring map.

## Unfinished work

The five new nodes are intentionally unsplit: other workers prove them independently. No new node is a Mathlib leaf. The parent is complete relative to those statements; no Lean proof or compiler certification is asserted.

## Searches

Before writing, I searched the whole DAG by Sylow, fixed/purely-inseparable fields, finite geometric/categorical quotient, projective quotient, clopen quotient, and prime-to-ell generic residue degree. I read the matching statements, not just ids. Whole-blueprint searches used tools/blueprint_refs.py search for Sylow, clopen, fixed field, projective quotient, and categorical quotient; no imported blueprint node states any of these five auxiliary results. The ancestor command was also read. Existing field, normal-component, quotient-normal-proper, quotient-generic-field and finite-normal-ample-descent lemmas are retained as the lower inputs in the plans below, rather than recreated.

For every new id, msearch.py ran leanfinder, loogle, grep, leansearch, and a second leanfinder phrasing. The full outputs are copied into each node's mathlib_searches with exact query texts. LeanSearch returned a rate-limit error and is recorded unavailable, never as no match. Loogle rejected the non-Mathlib identifier IsHProjective in two first patterns; those failures are recorded honestly and followed by valid alternative Loogle patterns using IsProper or Surjective. Grep ran successfully on the live clone's Mathlib. Two phrasings were read for each candidate before concluding absence. Fixed-field finrank and Galois instances prove pieces of the constants lemma but do not include both the Sylow-image index argument and inseparable constants-degree argument. IsFinite.instMorphismRestrict proves finiteness in the clopen lemma, not its categorical universal property or invariant/geometric clauses. The other hits concern Proj properness, affine space, ramification/inertia, or topological discrete quotients and do not state the new assertions.

## Not duplicates

- lem-sfb-sylow-constants-field-degree vs lem-wf-finite-field-action-fixed-degree: the existing lemma has a faithful action and computes the degree over its fixed field; the new statement permits an ineffective action, compares two fixed fields via a Sylow subgroup and includes the purely inseparable degree over e.
- lem-sfb-sylow-constants-field-degree vs lem-exc-normal-field-degree-factors: the existing lemma factors a normal extension's degree into separable and characteristic-power factors; it does not have group actions or the Sylow prime-to-ell constants conclusion.
- lem-sfb-sylow-constants-field-degree vs lem-weil-pbc-purely-inseparable-pth-root-tower: the existing lemma constructs a characteristic-p tower; it does not compare fixed fields of G and L or identify the Galois group over F.
- lem-sfb-semilinear-quotient-projective-geometry vs lem-sfb-finite-normal-ample-descent: the latter produces some ample sheaf for a given finite surjection onto an integral normal target; the new input must descend constants, establish normality/properness, handle disconnected targets and produce a finite projective embedding. Its route uses the existing ample lemma on each component.
- lem-sfb-semilinear-quotient-projective-geometry vs lem-sfb-finite-quotient-normal-proper: the latter assumes a linear action over a specified common field and gives normal proper finite type, but no constants descent, projectivity or change from K to its invariant constants field.
- lem-sfb-semilinear-quotient-projective-geometry vs lem-per-projective-finite-group-quotient: the dropped node constructs quotients and presupposes an action over the specified base. The new node assumes q already exists, descends the invariant constants structure from a semilinear K-action and proves normality and projectivity via the retained componentwise norm route. It has no quotient-existence conclusion and does not cite or reconstruct the dropped existence argument.
- lem-sfb-sylow-generic-prime-to-ell-lift vs lem-sfb-finite-quotient-generic-fields: the existing lemma identifies stabilizer fixed fields for a single quotient; the new statement selects a conjugate with a prime-to-ell intermediate residue degree over the external base B, using two quotients and the generically radicial map.
- lem-sfb-sylow-generic-prime-to-ell-lift vs lem-per-torsor-subgroup-quotient-finite-etale: the latter needs a connected finite etale torsor and counts geometric fibres. The new statement allows disconnected schemes and ineffective residue actions, proves no etaleness and selects a generic point by a decomposition subgroup.
- lem-sfb-sylow-generic-prime-to-ell-lift vs lem-exc-normal-field-degree-factors: the degree factorization is a field input, not the scheme/component selection with a prescribed Sylow subgroup and radicial quotient.
- lem-sfb-sylow-generic-prime-to-ell-lift vs lem-weil-pbc-purely-inseparable-pth-root-tower: the tower theorem does not compare quotient component fields or choose a good generic point; it only supplies the inseparable-degree factor.
- lem-sfb-sylow-generic-prime-to-ell-lift vs lem-per-admissible-quotient-generic-degree: the dropped statement assumes an integral generically free action and gives a subgroup-index degree. The new statement allows permuted components and generic inertia and proves a per-base-component existence conclusion using decomposition groups. The dropped statement cannot be applied.
- lem-sfb-sylow-generic-prime-to-ell-lift vs lem-sfb-sylow-conjugate-containment: conjugate containment is only the group-theoretic choice within a single decomposition group; it has neither schemes nor residue-field degrees.
- lem-sfb-clopen-generic-projective-cover vs rem-pc-regular-normal: normality supplies clopen components but gives no projective graph, proper image, cover of B or selected residue degrees.
- lem-sfb-clopen-generic-projective-cover vs lem-trf-smooth-component-pure-transcendental: the latter gives geometric integrality of one smooth component from a rational-type residue field, not a projective surjection assembled over a proper target.
- lem-sfb-clopen-generic-projective-cover vs lem-sc-smooth-connected-curve-local-rings: the latter concerns integral curves and their DVR local rings; the new statement works in arbitrary dimension and proves projectivity and surjectivity of a component union over B.
- lem-sfb-clopen-generic-projective-cover vs lem-weil-pbc-normalization-projective-components: the latter constructs a normalization and proves each of its components projective over one field; it gives no selection relative to B, finite change of constants, graph embedding or cover.
- lem-sfb-clopen-generic-projective-cover vs lem-weil-pbc-geonormal-dim-one-smooth: that lemma derives smoothness and irreducibility in dimension at most one under geometric normality; no dimension or geometric normality is imposed here, and the conclusion is a cover of B.
- lem-sfb-clopen-geometric-categorical-quotient vs lem-sfb-admissible-finite-type-field-quotient: the existing restriction assertion assumes a separated locally finite-type scheme over a field and constructs its quotient. The new lemma works for an arbitrary supplied quotient of arbitrary schemes, including ones with no field structure, no finiteness of type and no separatedness. It isolates the clopen categorical descent/uniqueness argument. It is not a specialization of the existing field theorem.
- lem-sfb-clopen-geometric-categorical-quotient vs lem-per-projective-finite-group-quotient: the dropped construction needs a quasi-projective finite-type scheme over a Noetherian base; the new statement assumes the quotient and only restricts it on a clopen target with none of those hypotheses. Neither a quotient nor projectivity is constructed.
- lem-sfb-clopen-geometric-categorical-quotient vs def-per-admissible-finite-scheme-quotient: that node defines a property. The new statement proves its preservation, the geometric-points property and the separate categorical universal property.

## Review by Q13

I read the current chapter and unit, GOAL.md, the three blueprint levels in SETUP.md, the worker/stage-1 contract and delivery-errors B--E in full. I read the current main-20261015 direct-images proof, as well as the original item's provenance. This is a local refinement of the existing alteration input; it does not change the unit route. In particular no SGA source, trace/PD assumption or new six-functor route is used.

For the item I read ILO Expose X 2.3 Step 2, printed pp.150--151, especially diagram (2.c) and its constants and generic-degree assertions. I also read Step 3's decomposition-group/inertia discussion on p.151. ILO's unqualified degree phrase cannot justify every omitted component: the item already selects only good components and I keep that convention. For the constants task I read fields.tex Tag 09HI, label lemma-finite-purely-inseparable, and the faithful finite-field-action, finite-Galois automorphism-count, field-degree multiplicativity and normal-field-degree-factor statements. All are retained by name in the plan below. The necessary reduction is to image groups H and J; the coset map need not be a group homomorphism, since L need not be normal. Its uniform fibre size gives the index identity. Purely inseparable normality and the single embedding justify the p-power degree only in positive characteristic; characteristic zero is handled separately. This new node is not the whole item: it contains no schemes, quotient maps, component selection or projectivity.

For the geometry task I read Stacks varieties.tex 056S (lemma-smooth-regular), properties.tex 033M (lemma-normal-Noetherian), divisors.tex 0BD4(2) (proposition-push-down-ample), and the exact existing statements used in old steps 3--6. The new statement requires the original action to be e-linear and semilinear for Y/K, and the quotient categorical among all schemes. Those hypotheses descend the actual map to Spec F; the e-structure is forced by the same categorical uniqueness. This avoids applying the existing normal-proper quotient theorem to an unrelated field structure. Finite structural maps Spec K to Spec e and Spec F give projectivity of Y over both bases. The target component C is normal integral, its inverse image is closed projective, and the map onto C is finite surjective, so 0BD4(2) applies. Finitely many ample sheaves glue on disjoint components; the nonvanishing section extended by zero proves ampleness. Properness and the ample immersion give a closed finite-projective-space embedding. This is the exact retained route, with no unsupported quotient-existence or linearization argument.

For the generic-lift task I read groupoids.tex 03BK(3), label lemma-invariants-base-change, the existing generic-field statement, and the two Sylow statements. I checked that the source quotient schemes are normal Noetherian before their use. The unique radicial point t over b has finite purely inseparable residue extension. The quotient comparison is with the component stabilizer D, not all of G. I choose a Sylow subgroup of D and a conjugate inside the fixed L separately for each b, so S=D' intersect L is Sylow in D'. Image groups of D' and S on the function field account for generic inertia. The ratio [A:A0] divides [D':S] by coset fibre counting; multiplying by the inseparable p-power preserves coprimality with ell. No global freeness or simultaneous conjugation is assumed. The resulting statement provides a good generic c for every b, exactly what the next task needs.

For the component-cover task I read the normal-component theorem and the finite-projective-bundle, ample-base conversion, H-projective composition, closed-immersion base-change/composition, and projective-implies-proper statements. The finite F/e hypothesis is explicit, and d is an e-morphism; without the latter the graph cannot be taken over e. B proper over e provides its closed diagonal. A clopen selection has precisely its chosen generic points, so there are no bad new generic points. The graph and the base change of a projective embedding give a closed immersion into projective space over B; its bundle interpretation is the trivial bundle. Finally the proper image is closed and contains each component's generic point, hence all of B. The argument is stronger than mere dominance over a connected target and imposes no restriction on discarded components.

For the clopen quotient task I read ILO IX 1.4, pp.132--133, for the quotient context, then checked old step 13 directly. No source claims this exact arbitrary-scheme formulation verbatim. On each affine open of U, the finite algebra and invariant-section equality are the old ones. Geometric point orbits restrict because the target open is invariantly pulled back. For categoricity the clopen complement is essential: extend an invariant V_U to T map on the other summand by q, with target T disjoint union (X minus U); descend through q and restrict. Surjectivity forces the descended restriction into the summand T. Given two possible restricted factorizations, extend them on the complement by its identity, apply the original uniqueness and restrict again. If q is admissible, every restricted orbit has an affine neighbourhood from the finite inverse image of an affine open of U, the restricted finite surjection is a quotient map, and the invariant structure sheaf is unchanged. This checks the extra admissibility clause. General arbitrary base-change preservation has not been asserted.

For the five parent steps I opened the cited new statement after writing it and tested the application, not its planned proof: (1) all constants hypotheses appear verbatim; (2) the same scheme action and supplied quotients satisfy the geometry input twice, and its statement supplies normality, Noetherianness, descended F-structure and projectivity; (3) the normal Noetherian schemes from step 2, the two quotient maps, the original h and the given generic-open hypothesis are precisely those in the lift statement; (4) step 1 gives finite F/e, step 3 gives every c_b, and the item's B is proper of finite type, so the cover input supplies every projective/normal/surjective and generic residue clause; (5) the new general restriction statement takes the clopen open from step 4 and the original q_L, and states every remaining finite/geometric/categorical clause. citations.json quotes the actual statements verbatim. No parent step relies on an unquoted conclusion hidden in a child proof. Every step is marked non-elementary and is well below 2000 characters.

I tested the five statements on small cases. For constants: G=1, G=L, a trivial action with nontrivial kernel, char zero and a characteristic-p purely inseparable base all give the correct image group and degree. For quotient geometry: Y empty, a trivial action, and a finite set of components permuted transitively are allowed; normality does not mean geometric integrality. For generic lifts: a swapped pair, several component orbits, nontrivial generic inertia, and S3 with ell=2 confirm that one can select good components without requiring all components good. For the cover: B a finite disjoint union of points gives the field-degree assertion directly; a non-surjective morphism cannot meet every generic fibre when proper. A single chosen generic cannot lie over two distinct b, so repetitions in the selection introduce no issue. For quotient restriction: U empty, U=X, a trivial action and a clopen permutation-stable union all retain the stated universal property. The extension argument uses actual morphisms on disjoint open subschemes and works without a field or finite-type assumptions.

B1--B10: each new file is statement-only with empty proof and proof_deps, introduces its own objects, cites definitions (or defines its terminology inline), has a sourced location and specific blueprint provenance, and has real logged Mathlib searches. C1--C8: the five non-elementary parent inputs are named nodes with checked verbatim citations; no definition stands in for a theorem, no child cites the parent, and all five have the parent's unit. D1--D5: none restates the whole result, no whole-proof transfer, no cyclic construction or hidden induction; the return explicitly asks for extracting these strictly smaller arguments. E1--E7: the checked hypotheses and counterexample-sensitive cases above did not require changing the item statement. The repair changes proof structure substantively, rather than re-pushing the prior node unchanged.

## Full retained arguments and new task ownership

The following thirteen paragraphs and their uses are transcribed from the returned live node without edits. They are a handoff plan in this report, not proof steps in the five new unsplit files. Future workers have every argument and citation the original proof had. In particular none of the norm, closed-graph, conjugation, ineffective-action or categorical-uniqueness work has been erased.

### lem-sfb-sylow-constants-field-degree

Old step 1 (475 characters):

Put $E=K^G$, $H=\operatorname{im}(G\to\operatorname{Aut}_eK)$ and $J=\operatorname{im}(L\to\operatorname{Aut}_eK)$. These image groups act faithfully. The finite-field-action theorem gives $[K:E]=|H|$ and $[K:F]=|J|$, and makes $K/F$ finite Galois. Its automorphism group has order $[K:F]=|J|$ by the finite-Galois theorem, so the inclusion of $J$ into that group is equality. This proves the asserted Galois-group clause without assuming the original action of $L$ faithful.

Uses: lem-wf-finite-field-action-fixed-degree, lem-weil-pbc-finite-galois-fixed-field.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; X 2.3 Step 2, printed p.151: K/K^L, with the kernel of the constants action removed.

Old step 2 (750 characters):

Let $N=\ker(G\to H)$. Counting cosets gives $[G:L]=[H:J][N:N\cap L]$: the map $G/L\to H/J$ is onto and each fibre has cardinal $[N:N\cap L]$. Thus $[H:J]$ is prime to $\ell$. The degree tower $E\subseteq F\subseteq K$ gives $[F:E]=|H|/|J|=[H:J]$. In positive characteristic $p$, the finite purely inseparable extension $E/e$ is normal (each minimal polynomial has only its one root), and has exactly one embedding into an algebraic closure; the normal-field-degree-factors theorem therefore makes $[E:e]$ a power of $p$. In characteristic zero $E=e$ by the meaning of purely inseparable. As $p\ne\ell$, the second degree tower gives $[F:e]=[F:E][E:e]$ prime to $\ell$. All towers are finite since their fields lie in the given finite extension $K/e$.

Uses: lem-weil-pbc-field-degree-multiplicativity, lem-exc-normal-field-degree-factors.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; X 2.3 Step 2, printed p.151: the prime-to-ell constants degree; inseparable degree is a characteristic power (Stacks 09HI).


### lem-sfb-semilinear-quotient-projective-geometry

Old step 3 (390 characters):

Smoothness over $K$ makes $Y$ regular and locally Noetherian, hence normal. Projectivity makes $Y/K$ proper, hence finite type; since a field is Noetherian, the finite-type theorem makes $Y$ Noetherian. The normal-component theorem decomposes $Y$ as a finite disjoint union of open-and-closed normal integral components. This applies even when the components are not geometrically integral.

Uses: lem-weil-pbc-smooth-scheme-over-field-regular, rem-pc-regular-normal, lem-kun-projective-implies-proper, lem-weil-pbc-finite-type-over-noetherian.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; X 2.3 Step 2, printed p.151: normality and components of the smooth projective model; Stacks 056S, 033M.

Old step 4 (1163 characters):

For $k=e$ and for $k=F$, the morphism $\operatorname{Spec}K\to\operatorname{Spec}k$ is finite because $K/k$ is finite-dimensional. The finite-projective-bundle theorem followed by the ample-base conversion makes it H-projective: the trivial line on $\operatorname{Spec}k$ is ample, since its unit section has the whole affine scheme as nonvanishing locus. Compose with the given H-projective $Y/K$ to obtain $Y/k$ H-projective, hence proper. The invariant map $Y\to\operatorname{Spec}F$ descends by the categorical property of $q_L$, and gives $Q$ its $F$-structure; the descended map agrees with the original $e$-structure. Likewise the $G$-invariant structure map $Y\to\operatorname{Spec}e$ descends through $q_G$ and gives $Z=Y/G$ its $e$-structure, so $q_G$ is a morphism of $e$-schemes and $q_L$ a morphism of $F$-schemes; uniqueness in the categorical property shows that an invariant $e$- (resp. $F$-)morphism factors through a morphism of $e$- (resp. $F$-)schemes. Apply the normal-proper-quotient lemma to $(Y,G,e)$ and $(Y,L,F)$. Thus $Z=Y/G$ is normal proper finite type over $e$, and $Q=Y/L$ is normal proper finite type over $F$; both are Noetherian.

Uses: def-weil-finite-integral-morphism, def-weil-pbc-ample-invertible-module, lem-trf-finite-projective-bundle, lem-trf-projective-bundle-to-h-projective, lem-trf-h-projective-composition, lem-kun-projective-implies-proper, lem-sfb-finite-quotient-normal-proper.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; X 2.3 Step 2, diagram (2.c), printed p.151. Constants descent by the assumed categorical quotient; finite structural maps are projective by Stacks 0B3I and 087S.

Old step 5 (1000 characters):

Decompose $Q$ into its finitely many clopen normal integral components $C$. For each $C$, its inverse image $X_C=q_L^{-1}C$ is clopen in $Y$. A clopen subscheme is also a closed subscheme, as the defining ideal is zero on it and the unit ideal on its complement. Compose this closed inclusion with a projective embedding of $Y/F$ to obtain a projective embedding of $X_C/F$, and hence an ample invertible sheaf on $X_C$. The restricted map $X_C\to C$ is finite surjective: on an affine open of $C$ it is the same finite algebra as for $q_L$. Apply finite-normal ample descent to obtain an ample invertible sheaf on $C$. Glue these sheaves on the disjoint components to an invertible sheaf on $Q$. It is ample: extend an affine-nonvanishing section on a chosen component by zero on all other components; its nonvanishing locus is the original affine open. Quasi-compactness holds because there are finitely many components. This uses the definition of ample, without descending a chosen linearization.

Uses: rem-pc-regular-normal, lem-weil-pbc-closed-immersion-comp, lem-weil-pbc-projective-ample-invertible, def-weil-finite-integral-morphism, lem-sfb-finite-normal-ample-descent, def-weil-pbc-ample-invertible-module.

Source: literature/stacks-project/divisors.tex; Tag 0BD4(2), applied to each normal integral target component; finite disjoint gluing of ample sheaves is the defining affine-nonvanishing criterion.

Old step 6 (352 characters):

The ample-immersion theorem, applicable since $Q/F$ is finite type, gives an immersion $Q\to\mathbf P^n_F$. The target is separated over $F$ and $Q$ is proper over $F$, so the proper-to-separated-target theorem makes the immersion proper. A proper immersion is closed. Thus $Q$ is projective over $F$ in the required finite-projective-space convention.

Uses: lem-weil-pbc-ample-very-ample-immersion-affine-base, lem-weil-pbc-projective-space-proj-separated, lemma-nagata-proper-to-separated-target, lem-weil-pbc-proper-immersion-closed, def-kun-projective.

Source: literature/stacks-project/morphisms.tex; Tags 01VS and 01VT (ample immersion over an affine base), Constructions 01NH (projective space separated), 01W6 (map from a proper scheme to a separated target), and Schemes 01IQ (immersion with closed image is closed).


### lem-sfb-sylow-generic-prime-to-ell-lift

Old step 7 (853 characters):

Fix a generic point $b$ of $B$. It lies in the specified dense open $U$. The finite universal homeomorphism $Z_U\to U$ has exactly one point $t$ over $b$, which is generic: on the component containing $b$ it is a homeomorphism. Its residue extension $T=\kappa(t)/\kappa(b)$ is finite by finiteness of this morphism and purely inseparable because a universal homeomorphism is universally injective, hence radicial. The generic-field comparison for $q_G:Y\to Z$ identifies the components above $t$ as one $G$-orbit. Choose a generic point $\eta$ in this orbit, put $M=\kappa(\eta)$ and $D=\operatorname{Stab}_G(\eta)$. The same comparison gives $T=M^D$ with its canonical embedding in $M$. All components of $Z$ meet $Z_U$: every generic of $Y$ maps to a generic of $B$ by hypothesis, and the quotient comparison maps these onto the generic points of $Z$.

Uses: def-weil-universal-homeomorphism, def-weil-radicial-morphism, def-weil-finite-integral-morphism, lem-sfb-finite-quotient-generic-fields.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; X 2.3 Step 2, printed p.151: the dense-open radicial quotient. Generic-field identification is applied without freeness; Stacks 01S4 gives inseparable residue extensions.

Old step 8 (645 characters):

Choose an $\ell$-Sylow subgroup $P$ of the finite stabilizer $D$. Regard $P$ as an $\ell$-subgroup of $G$ and apply Sylow conjugate containment to obtain $g$ with $gPg^{-1}\subseteq L$. Replace $\eta$ by $\eta'=g\eta$, and write $D'=gDg^{-1}$ and $M'=\kappa(\eta')$. Put $S=D'\cap L$. It contains the $\ell$-Sylow subgroup $gPg^{-1}$ of $D'$, while it is itself an $\ell$-group as a subgroup of $L$. Hence $|S|=|P|$ and $[D':S]$ is prime to $\ell$. The point $\eta'$ still maps to $b$ because $h$ is invariant. This chooses a conjugate separately for this generic point of $B$, rather than imposing a simultaneous containment on all stabilizers.

Uses: lem-weil-pbc-sylow-subgroup-prime-index, lem-sfb-sylow-conjugate-containment.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; X 2.3 Step 2, printed p.151, explicit stabilizer-wise Sylow selection for the all-generic-points convention.

Old step 9 (768 characters):

Let $c=q_L(\eta')$, a generic point of $Q$. The quotient comparison gives $\kappa(c)=(M')^S$ and $T=(M')^{D'}$. Let $A$ and $A_0$ be the images of $D'$ and $S$ in $\operatorname{Aut}(M')$. The faithful finite-action theorem gives $[M':T]=|A|$ and $[M':\kappa(c)]=|A_0|$. The tower law gives $[\kappa(c):T]=[A:A_0]$. Counting fibres of $D'/S\to A/A_0$ shows that this index divides $[D':S]$, so it is prime to $\ell$. Since $T/\kappa(b)$ is finite purely inseparable, its degree is a characteristic power (or one in characteristic zero), by the normal-field-degree-factors theorem as in step 2. Multiplying degrees now proves that $[\kappa(c):\kappa(b)]$ is finite and prime to $\ell$. The field-action theorem is applied to image groups, so generic inertia is allowed.

Uses: lem-sfb-finite-quotient-generic-fields, lem-wf-finite-field-action-fixed-degree, lem-weil-pbc-field-degree-multiplicativity, lem-exc-normal-field-degree-factors.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; X 2.3 Step 2, diagram (2.c), printed p.151: intermediate invariant-field degrees, with decomposition groups and possible generic inertia made explicit.


### lem-sfb-clopen-generic-projective-cover

Old step 10 (614 characters):

Do this for each of the finitely many generic points $b$ of $B$, choosing one resulting component of $Q$ over each. Let $Q^\circ$ be the union of those components. By the normal-component theorem it is open and closed, normal, and its generic points are precisely the finitely many selected generic points; each has the finite prime-to-$\ell$ residue degree proved in step 9. It meets every generic fibre of $B$. Its closed inclusion into the projective $F$-scheme $Q$, composed with the projective embedding of $Q$, makes $Q^\circ/F$ projective. No condition is inferred for any component omitted from this union.

Uses: rem-pc-regular-normal, lem-weil-pbc-closed-immersion-comp, def-kun-projective.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; X 2.3 Step 2, printed p.151, retaining good components for the every-generic-point definition of prime-to-ell alteration.

Old step 11 (802 characters):

The finite map $\operatorname{Spec}F\to\operatorname{Spec}e$ is H-projective by the finite-projective-bundle theorem and the ample-base conversion, again using the unit section of the trivial line on the affine base. Composition therefore gives a closed immersion $i:Q^\circ\hookrightarrow\mathbf P^N_e$. Let $d:Q^\circ\to B$ be the descended map, restricted to this union. The diagonal of $B/e$ is closed because $B/e$ is proper. Its base change is the graph $Q^\circ\to Q^\circ\times_eB$, so the graph is closed. The map $Q^\circ\times_eB\to\mathbf P^N_e\times_eB$ is the base change of $i$, hence closed. Their composite is a closed immersion over $B$, exhibiting $d$ as H-projective, and thus also projective in the projective-bundle convention (the ambient bundle is that of $\mathcal O_B^{N+1}$).

Uses: def-weil-finite-integral-morphism, def-weil-pbc-ample-invertible-module, lem-trf-finite-projective-bundle, lem-trf-projective-bundle-to-h-projective, lem-trf-h-projective-composition, def-weil-proper-morphism, lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-closed-immersion-comp, def-kun-projective, def-trf-projective-bundle-morphism.

Source: literature/stacks-project/morphisms.tex; Tags 0B3I, 087S, 01W9 for finite structural maps and projective composition; closed graph is base change of the diagonal, with closed immersions stable under base change and composition.

Old step 12 (486 characters):

Projectivity makes $d$ proper, so its image is closed by the definition of universally closed applied to the identity base change. This image contains every generic point of $B$ by construction. A closed subset containing the generic point of every irreducible component contains every component, so the image is all of $B$. Thus $d$ is surjective. The generic-point and residue-degree clauses were established for every component retained in $Q^\circ$, not just for their total degree.

Uses: lem-kun-projective-implies-proper, def-weil-proper-morphism.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; X 2.3 Step 2, printed p.151: proper dominant components give the desired projective surjection.


### lem-sfb-clopen-geometric-categorical-quotient

Old step 13 (886 characters):

Set $Y^\circ=q_L^{-1}(Q^\circ)$. It is clopen and $L$-stable. The restricted quotient is finite and surjective, has the same orbit geometric fibres, and has invariant structure sheaf by restricting the corresponding statements for $q_L$ to the open $Q^\circ$; on each affine open the same finite algebra occurs. Its categorical property can be checked directly. Given an invariant morphism $f:Y^\circ\to T$, extend it on the disjoint complement by $q_L$ to obtain an invariant map $Y\to T\amalg(Q\setminus Q^\circ)$. Descend it through $q_L$, then restrict to $Q^\circ$: surjectivity on points forces this restriction to land in the summand $T$. This gives the required factorization; uniqueness follows either from the categorical uniqueness for the extended map or from that same descent construction. Hence $Y^\circ\to Q^\circ$ is the finite quotient by $L$ claimed in the statement.

Uses: def-weil-finite-integral-morphism, def-weil-open-immersion.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; X 2.3 Step 2, printed p.151: restriction to the selected clopen union; categorical restriction proved by extension to a disjoint-union target.


## Prior delivery report, retained for continuity

# Stage-1 report: lem-sfb-semilinear-sylow-good-components

Group NJ; direct delivery; 2026-10-22. Only this sandbox was written. No Lean source, compiler, Lake, build, git command in the shared repository, or sub-agent was used.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-semilinear-sylow-good-components.json: item, split in 13 steps, statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-normal-ample-descent.json: statement-only; no Mathlib match; exactly Stacks 0BD4 case (2).
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-quotient-normal-proper.json: statement-only; no Mathlib match; normality, finite type and properness for an already supplied finite geometric quotient of a normal proper scheme.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-quotient-generic-fields.json: statement-only; no Mathlib match; component orbits and stabilizer fixed fields for a disconnected normal quotient.
- dag/nodes/sec-six-functors-basics/lem-sfb-sylow-conjugate-containment.json: Mathlib leaf; IsPGroup.exists_le_sylow (Sylow.lean:195), followed by Sylow.isPretransitive_of_finite (343), with coe_smul (300).
- citations.json: every step citation backed by a verbatim statement quote. The entire statement is retained where several clauses are used.
- report.md: this report. research/ retains actual search outputs, the query index, source-pair comparisons, and sandbox writing scripts; searches.jsonl is the search command's own log.

## Attachments

None. I searched WeilConjectures for the exact blueprint tag and for the concepts. No sorry-free project declaration gives the whole item. A reference to this node in Sheaf/GabberGlobalSNCAlteration is not an attachment. Mathlib's abstract quotient and fixed-field results are not project declarations proving this item.

## WANTED

None. The ILO PDF, Stacks source, and Mathlib source used here are available locally. Two new nodes explicitly identify agent-formulated general consequences of those sources rather than claiming a verbatim theorem in ILO.

## Errors and changes

No statement dispute was found. The item already corrects the two hazards in an unqualified reading of ILO X 2.3: the constants Galois group is the image of L, and prime-to-ell total degree does not mean that every component is good. I retained its full statement, including the restriction to a selected clopen union.

The existing nodes lem-per-projective-finite-group-quotient, lem-per-admissible-quotient-generic-degree and lem-per-artin-tate-subalgebra-finite-type are on coord/route-pivot-dropped.txt. I read their statements, but none is cited. Nor are their dropped quotient-construction children cited. The new proof uses an existing quotient as a hypothesis, the general norm theorem on a normal integral target, and an explicit stabilizer argument; it does not reconstruct the dropped projective quotient existence theorem. I inspected the transitive statement/proof dependency closure of the actual citations: it meets no dropped id.

The normal-proper quotient input does not assert existence, quasi-projectivity, projectivity, or a generic-degree formula. Its hypothesis allows normal proper schemes with no projective embedding. The generic-field input makes no generic freeness hypothesis and allows permuted components; the old generic-degree node's integral generically free setting cannot be substituted. The norm input is about an arbitrary finite surjection, with no group or quotient hypothesis, and asserts existence of some ample sheaf, not descent of a specified sheaf.

## Unfinished work

The three new unsplit auxiliary statements are intentionally not split in this one-level delivery. There is no unfinished argument in the item's proof. No Lean implementation or verification was attempted, as this run authorizes stage 1 only.

## Not duplicates

- lem-sfb-finite-quotient-normal-proper vs lem-trf-relative-nodal-point-pinching: the existing statement constructs nodal pushouts along finite sets on semistable curves; the new statement assumes a finite group quotient already exists and proves normality and properness in every dimension.
- lem-sfb-finite-quotient-normal-proper vs sk-thm-picard-main: the existing statement represents the Picard functor of a smooth proper curve; the new statement concerns existing finite group quotients of arbitrary normal proper schemes.
- lem-sfb-finite-quotient-normal-proper vs lem-pc-bounded-complex-tensor-proper-support-bound: the existing statement bounds derived tensor supports by a proper closed subset; the new statement concerns the structure sheaf and properness of a scheme quotient.
- lem-sfb-finite-quotient-normal-proper vs lem-sc-picg-geometrically-integral: the existing statement proves geometric integrality of a represented Picard degree-g functor; no Picard scheme or curve occurs in the new finite-quotient assertion.
- lem-sfb-finite-quotient-normal-proper vs thm-pc-hilb-curves: the existing statement concerns Hilbert schemes of points on curves and their addition; the new statement concerns an already given finite geometric group quotient.
- lem-sfb-finite-quotient-normal-proper vs lem-per-artin-tate-subalgebra-finite-type: the existing dropped Mathlib leaf is only a ring-theoretic finite-type theorem; the new statement is a geometric assertion about normality and properness, requiring the additional invariant-ring and proper-image arguments. It is not a renamed Artin--Tate theorem and the dropped leaf is not cited.
- lem-sfb-finite-quotient-normal-proper vs lem-weil-pbc-universally-closed-product-map: the existing statement only says a product of universally closed maps is universally closed; the new assertion additionally derives finite type and normality of an existing scheme quotient.
- lem-sfb-finite-quotient-normal-proper vs lem-weil-pbc-surjective-universally-closed-separated: the existing statement supplies separatedness of a target of a universally closed surjection, not finite type, normality or properness of a finite group quotient.
- lem-sfb-finite-quotient-normal-proper vs lem-weil-pbc-finite-surjective-affine-target: the existing statement descends affineness under a finite surjection from an affine scheme; the new source may be an arbitrary normal proper scheme and the conclusion is normal proper finite type.
- lem-sfb-finite-quotient-normal-proper vs lem-weil-pbc-eventually-proper: the existing statement descends properness to a stage of an inverse system; the new statement has no inverse system and requires invariant-ring normality and finite type.
- lem-sfb-finite-quotient-normal-proper vs lem-weil-pbc-surjective-universally-closed-affine-target: the existing statement asserts that a target covered by an affine universally closed surjection is affine; the new statement has no affine-source hypothesis and proves normality and properness of an existing group quotient.
- lem-sfb-finite-quotient-normal-proper vs lem-weil-pbc-scheme-theoretic-image-proper: the existing statement assumes a separated locally finite-type target to obtain a proper scheme-theoretic image; the new statement must establish finite type and separatedness of the quotient target and its normality.
- lem-sfb-finite-quotient-normal-proper vs lem-weil-pbc-image-universally-closed: the existing statement supplies universal closedness (and properness when separatedness and local finite type are already known); the new statement also establishes those missing hypotheses and invariant-ring normality.
- lem-sfb-finite-quotient-generic-fields vs lem-per-torsor-subgroup-quotient-finite-etale: the existing statement requires a connected finite etale G-torsor and computes geometric fibre cardinalities. The new statement concerns generic residue fields of disconnected normal schemes with possibly nonfaithful action and nontrivial inertia; it asserts no etaleness.

The following additional conceptual comparisons were checked even though their source tags differ:

- lem-sfb-finite-normal-ample-descent vs lem-per-projective-finite-group-quotient: the latter constructs finite group quotients and projective embeddings from quasi-projective data; 0BD4 instead starts with any finite surjection to a normal integral scheme and gives an ample sheaf without a group, properness or Noetherian base.
- lem-sfb-finite-quotient-normal-proper vs lem-per-projective-finite-group-quotient: the former assumes the quotient map and starts with an arbitrary normal proper scheme; it asserts no projectivity or quotient construction. Proper normal nonprojective inputs are permitted, so this is not a special case of the latter.
- lem-sfb-finite-quotient-generic-fields vs lem-per-admissible-quotient-generic-degree: the old statement assumes an integral generically free admissible action and gives subgroup-index degrees; the new statement compares fields under the actual component stabilizer for disconnected schemes with nonfaithful actions. The old degree formula would not apply.
- lem-sfb-finite-normal-ample-descent vs lem-sc-ample-on-reduction-noetherian: the latter tests a specified line bundle on a nilpotent thickening, whereas the norm theorem produces some ample line bundle on a normal integral target. Neither specializes to the other.

## Review by NJ

I read ILO Expose X 2.3 Step 2 through diagram (2.c), printed p.151 (PDF pages 157-158 also include Step 3's component/stabilizer discussion). The source supplies the semilinear constants, radicial generic quotient and Sylow intermediate quotient. My proof makes the selection of good components and possible ineffective action explicit. I read the current unit and chapter: this remains the alteration input of the constructible-finite-Tor direct-image route. The general field/group/projective-scheme citations are tools, declared as off-unit uses when necessary; no alternate six-functor route or SGA source is used.

For the new ample-descent statement I read divisors.tex Tag 0BD4 case (2) and its proof, and the preceding norm lemmas 0BD3 and 0BD0. Its exact hypotheses are finite surjectivity, an ample sheaf on X, and integral normal target. The new statement neither adds flatness nor promises descent of the same sheaf. In step 5 the target C is an entire clopen normal integral component, not an arbitrary reducible quotient, so case (2) really applies. A field-valued target and a disconnected source satisfy the statement; nonnormal targets are deliberately excluded.

For the new normal-proper quotient statement I read Stacks 00IS, 09MQ(4), and 03GN in algebra.tex and morphisms.tex, as well as ILO's existing quotient context. On an affine open V of Z, its finite inverse image has coordinate algebra A finite over B=A^H. A is a finite-type k-algebra because X/k is finite type and this open is affine. Artin--Tate gives finite type of B. Since X is normal Noetherian, A is a finite product of normal domains, permuted by H. Its invariant subring is the product over component orbits of stabilizer-invariant normal domains. Such an invariant domain is integrally closed: a fraction of invariant elements integral over it is integral over the original normal domain, lies there, and remains invariant. Thus Z is normal. The finite surjection is universally closed, so 09MQ gives separatedness of Z; 03GN then gives universal closedness and properness. This is why merely citing a definition of quotient, or the proper-image lemma without establishing finite type, would be insufficient. Empty X forces empty Z; a trivial action gives Z=X; disconnected permuted components and nonfaithful actions cause no failure. No projective assertion is hidden in this input.

For the new generic-field comparison I read groupoids.tex 03BK(3), including the kernel/difference-map proof for flat base change. Normal Noetherian components are disjoint. The invariant idempotents given by a component orbit descend through the invariant structure sheaf and separate the quotient components. Over the generic point of one such component the finite algebra becomes a product of the component fields. Localization is flat, so 03BK identifies its invariants with the base field. Projection of an invariant tuple onto a chosen field identifies those invariants with the fixed field of its stabilizer: to reconstruct the tuple transport the chosen element along H, and stabilizer invariance makes it independent of the transport choice. This proves exactly the comparison used, including when the stabilizer action has a kernel. A swapped pair of copies of an integral scheme gives one quotient component; a trivial action gives one quotient component per original component. Neither example supports replacing the stabilizer by the whole group.

For the Sylow Mathlib leaf I read Sylow.lean:195 and 290-355, not just semantic hit names. The first theorem contains a p-subgroup in a Sylow subgroup; the pretransitive instance conjugates that Sylow to the prescribed one; coe_smul spells out conjugation. The finite group hypothesis supplies the finite type of Sylow subgroups required by the instance. The leaf records one declaration for each part of this short specialization. Tests P=1, P=L, G a p-group and p not dividing |G| all agree. All Mathlib queries are copied from msearch runs. I read the saved results before drawing conclusions, tried two semantic phrasings, and retained the raw outputs and query log. General category quotients and domain fraction-field theorems do not supply either new scheme statement.

I opened every cited existing node and compared its statement with the precise use in the following steps; citations.json contains verbatim quotations, not paraphrases:

1. The faithful finite-action theorem gives both Galois and order for H and J, and the finite-Galois automorphism-count node identifies the full group. Applying it directly to L could have been wrong when the action is ineffective; the proof explicitly uses J instead.
2. The degree-multiplicativity node applies to both finite field towers. The normal-degree-factors node assumes positive characteristic and normality; I verify normality and the unique embedding for a purely inseparable extension, and handle characteristic zero separately. The coset fibre count proves the index divisibility without assuming L normal.
3. Smooth-field regularity and regular-normal-components give exactly regularity, normality and clopen integral components. The finite-type-over-Noetherian node is applied after projective-implies-proper supplies finite type; a field is Noetherian. No geometric integrality is assumed.
4. Finite-projective-bundle and the ample-base conversion are applied to Spec K over the two smaller fields, where the trivial line is ample by its unit section. H-projective composition and projective-implies-proper then give the proper source required by the new quotient lemma. The categorical hypothesis gives the F-structure, so the L-action really is over F; the G-action is over e as assumed.
5. The normal-component node supplies finite clopen integral targets. Closed-immersion composition supplies projectivity of each inverse image, and projective-ample supplies its ample sheaf. The finite-morphism definition verifies the restricted finite map; 0BD4 now applies with all hypotheses. Finite disjoint gluing of the resulting lines is proved using affine nonvanishing sections extended by zero; no extra gluing theorem is asserted as a new node.
6. The ample-immersion node requires local finite type, available from step 4. Projective-space-separated and proper-to-separated-target make this immersion proper; proper-immersion-closed then makes it a closed immersion. This establishes the finite-projective-space convention, not just a locally projective morphism.
7. Universal-homeomorphism and radicial nodes together justify pure inseparability, which the homeomorphism definition alone does not say. Finiteness gives finite residue extension. The new generic-field comparison supplies both the orbit and T=M^D, with no freeness. Every source component reaches the chosen dense open because h sends all generics to target generics.
8. The existing Sylow-existence node gives P in D, and the new Mathlib leaf moves it into the specified L. The subsequent order count is written out. Only the chosen component is replaced by a conjugate; there is no assertion that one conjugation works for all components.
9. The generic-field node now applies to L with stabilizer S=D' intersect L. Faithful-action degrees are taken for image groups A and A0. Tower degrees and coset fibres give the prime-to-ell index even with generic inertia. The inseparable-degree argument has the same verified hypotheses as in step 2. This checks every selected residue extension, not a sum of degrees.
10. Normal components are clopen, so their selected union is clopen and normal. Closed-immersion composition restricts the projective embedding to this union. There is at least one selected component per generic point of the nonempty B, and every retained generic has the degree from step 9.
11. Finite-projective-bundle, ample-base conversion and H-projective composition make Q-circle projective over e. The definition of proper supplies B's closed diagonal; closed-immersion base change and composition give the graph embedding into projective space over B. A finite projective space is a projective bundle, so both projectivity conventions required by the statement hold.
12. Projective-implies-proper plus the definition of universally closed make d's image closed. Containing the finitely many generic points forces that image to contain all components of B, proving surjectivity; no separate dominance-implies-surjectivity theorem is assumed.
13. Finite restriction is checked on the unchanged affine algebras, using the finite-morphism definition. The open-immersion definition identifies the restricted sheaves, so invariant sections restrict. The categorical property is proved by extending a map to the disjoint complement target, descending the whole map, and restricting again. It is a direct argument from the given quotient, not an unsupported claim that arbitrary quotients commute with arbitrary base change.

I checked small cases of the whole item: G=1 forces F=K purely inseparable over e and selects the radicial component over each generic point; if G=L all index factors are one; dimension-zero bases reduce to the displayed finite field towers. The nonfaithful constants and generic inertia cases still use image groups throughout. For a transitive permutation of components the stabilizer, rather than G, controls the component field; for several orbits the construction chooses good ones independently over B's components. Empty Y cannot occur because h is onto a nonempty B. No selected component acquires a new generic point by taking the clopen union.

The B--E checklist was applied to the node files and sources: all introduced notions have definition citations or inline meanings, every non-elementary step has statement-level node citations, no cited node is merely a definition standing in for a theorem, every new node has its own complete statement and blueprint provenance, no auxiliary node restates the item or carries its Sylow selection, no project declaration with sorry was attached, and no test of an edge case forced weakening the statement. All 13 proof steps are under 2000 characters. The elementary thirteenth step contains the full direct extension/descent argument; there is no hidden external quotient-restriction lemma. The three new unsplit lemmas are real general inputs; their future proofs are not silently counted as proved. Source-tag overlap pairs were read and distinguished above.

Dry-run repair: the first server preflight rejected only missing notion citations in the Sylow leaf. I opened def-sfb-finite-infinite-set and added it for finiteness of the underlying group set, with the corresponding stmt_dep and verbatim citation update. The mathematical statement and search question are unchanged.
