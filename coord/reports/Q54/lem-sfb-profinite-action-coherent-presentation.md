# Worker report: Q54

This is the repair of L's 2026-10-22 06:35 UTC landing return at branch head d963b232ccc. The earlier reader approved the mathematics; landing refused because completion in the side DAG had not been promoted into the live DAG. I retained all seven node files, the report, citations and original search logs, compared the archived parent against the current repository, and re-read the current dependency statements. The delivery command rebuilds the split on freshly fetched origin/sheaf-dag and preserves its current maintainer-owned fields. The explicit adjustment is the module-sheaf abelian-category citation in assembly step 3, with a matching verbatim quotation. The retained six-node split still realizes the released keep_plan re-split order.

The following paragraph records the earlier repair's starting state and work, retained as history:

This repairs the human's 2026-10-21 re-split return, applied on 2026-10-22. The sandbox initially contained only dispatcher marker files: no node, report or search log survived. I copied the current live item, which has the fifteen-step returned proof, without changing its statement. The archived copy is returned-item.json in the sandbox; the report below retains every original proof step verbatim. The delivery adds six independent statement-only tasks rather than moving the whole proof into one replacement. The final four-step assembly has 2138 characters of proof text, below 3000. No chapter or unit route, target statement, Lean file or launcher file was changed, and no compiler was run.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-profinite-action-coherent-presentation.json: statement; six-node re-split, unchanged statement and statement dependencies; Mathlib verdict unchanged, not a leaf.
- dag/nodes/sec-six-functors-basics/lem-sfb-profinite-action-finite-cover-site.json: statement-only, status unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-profinite-action-yoneda-free-evaluation.json: statement-only, status unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-profinite-action-free-restriction.json: statement-only, status unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-profinite-action-cech-recovery.json: statement-only, status unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-profinite-action-module-lift.json: statement-only, status unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-profinite-action-trivial-parameter-fixed.json: statement-only, status unsplit, no Mathlib match.
- report.md: this report and retained argument.
- citations.json: verbatim statement quotes for all eight node citations across four assembly steps.
- searches.jsonl and *.search.txt: actual search logs and full responses, retained in the sandbox; not node deliveries.

## Attachments

None. The project-source search for the exact blueprint tag under lean/WeilConjectures found no completed declaration. The corresponding lean/Sheaf/CategoryTheory/ProfiniteActionCoherentPresentation.lean has sorry in profiniteAction_coherentPresentation and its subsidiary theorems. The main signature at line 521 asserts the existence of a SetPresentation, its PresentsDirectImage property, and ModulePresentation for every commutative condensed ring; the docstring reproduces the same fifteen-step argument. It is not an attachment. Partial data definitions in that file do not prove the item.

## WANTED sources

The main-20261015 direct-images proof, paragraph (3), supplies the surrounding route but no proof of this auxiliary presentation. I read that entire proof file, the chapter and the unit records, and retained proof_origin.by = agent. I have not promoted the discrete-group result Stacks 00W0 to a theorem about an internal represented profinite group. All six new source records explicitly identify their statements as extractions of an agent argument, not claims asserted by that blueprint paragraph.
WANTED: an exact non-SGA external reference for the represented internal profinite-group argument in lem-sfb-profinite-action-finite-cover-site, below main-20261015 direct-images paragraph (3).

WANTED: an exact non-SGA external reference for the represented internal profinite-group argument in lem-sfb-profinite-action-yoneda-free-evaluation, below main-20261015 direct-images paragraph (3).

WANTED: an exact non-SGA external reference for the represented internal profinite-group argument in lem-sfb-profinite-action-free-restriction, below main-20261015 direct-images paragraph (3).

WANTED: an exact non-SGA external reference for the represented internal profinite-group argument in lem-sfb-profinite-action-cech-recovery, below main-20261015 direct-images paragraph (3).

WANTED: an exact non-SGA external reference for the represented internal profinite-group argument in lem-sfb-profinite-action-module-lift, below main-20261015 direct-images paragraph (3).

WANTED: an exact non-SGA external reference for the represented internal profinite-group argument in lem-sfb-profinite-action-trivial-parameter-fixed, below main-20261015 direct-images paragraph (3).

For the topology part I also read Stacks topology.tex Tag 08YD, lemma-closed-map, and Tag 0AAU, lemma-closed-morphism-quotient-topology, using the tags/tags mapping. The former makes a continuous map from a quasi-compact source to a Hausdorff target closed; the latter makes a closed continuous surjection a quotient map. These support the already existing lem-sfb-compact-hausdorff-surjection-quotient; they do not alone prove the new equivariant descent or presentation statements. No SGA route is used.

## What changed, and what was wrong

The return concerned granularity: 12346 characters of proof in one node made independent work impossible. The statement is mathematically consistent with the returned explicit construction, so it is unchanged. I extracted the finite-limit/topological-descent infrastructure, the equivariant Yoneda and free-evaluation formulas, the right-translation reconstruction, the action-cover recovery maps, the module lift, and the trivial-parameter/fixed-section formulas as six tasks. They have comparable individual scope and introduce their own group, sites, actions, maps and coefficient hypotheses. Each has proof = [], proof_deps = [], proof_origin = null and status unsplit. In particular no proof sketch is hidden in a new statement. The full existing arguments are preserved below as handoff material, outside the new node statements. The generic coherence theorem remains a citation and the elementary kernel/cokernel transport remains in the parent assembly.

The inherited nearest blueprint ancestor is null: tools/blueprint_refs.py ancestor prints None for this creation chain. I retained that provenance and prepended this item to each child's via list. Whole-blueprint searches for profinite action, free restriction, right translation, finite cover action, equivariant Yoneda, module lift, trivial parameter and coherent presentation found no equal statement. The right-translation hit concerns group schemes; the module-lift hit is the Kunneth-map definition, neither is a duplicate.

## Mathlib searches and results

For every proposed new id I ran msearch.py with leanfinder, loogle, grep, and two distinct natural-language phrasings through leansearch. I read the saved hits. Several initial unqualified Loogle names were rejected by the service as unknown identifiers; those queries are recorded as invalid patterns, never as evidence of absence. Refined quoted-name Loogle searches were run, and grep was narrowed to CategoryTheory/Action or Condensed. Every recorded tool/query pair occurs in searches.jsonl with its original result record, and the complete outputs are saved alongside it. No unavailable response has been labelled no match.

The finite-cover-site searches find Profinite.hasLimits and ContAction. I read Mathlib/CategoryTheory/Action/Continuous.lean (definition of ContAction at line 74 and its restriction functors) and Mathlib/Condensed/Explicit.lean (ordinary profinite sheaf constructors). Neither states the equivariant finite-cover pretopology, subcanonicity or trivial-parameter preservation. The Yoneda/free and reconstruction searches find ordinary Yoneda, ordinary/light condensed sheaf constructors, and free ordinary representations. They neither impose the universal action equation on J times T nor reconstruct an internal action by F(r_g). The Cech searches find ordinary comparison equivalences and abstract presheaf counits, not the specific action-cover coordinate identification. The module searches find additive Yoneda and free module adjunctions, not the coefficient ring Q_R or this linear descent lift. The fixed-section searches find Rep.invariantsAdjunction. Reading Mathlib/RepresentationTheory/Invariants.lean confirms its base ring is a single ordinary ring and its group action is an ordinary representation; it does not quantify over every profinite base change. Thus all six nodes remain unsplit rather than Mathlib leaves.

## Not duplicates

lem-sfb-profinite-action-finite-cover-site vs lem-sfb-profinite-action-coherent-presentation: this is a proper subargument of the returned fifteen-step proof, not the full coherent set/module/direct-image presentation. The precise allocation is in the coverage table below.

lem-sfb-profinite-action-yoneda-free-evaluation vs lem-sfb-profinite-action-coherent-presentation: this is a proper subargument of the returned fifteen-step proof, not the full coherent set/module/direct-image presentation. The precise allocation is in the coverage table below.

lem-sfb-profinite-action-free-restriction vs lem-sfb-profinite-action-coherent-presentation: this is a proper subargument of the returned fifteen-step proof, not the full coherent set/module/direct-image presentation. The precise allocation is in the coverage table below.

lem-sfb-profinite-action-cech-recovery vs lem-sfb-profinite-action-coherent-presentation: this is a proper subargument of the returned fifteen-step proof, not the full coherent set/module/direct-image presentation. The precise allocation is in the coverage table below.

lem-sfb-profinite-action-module-lift vs lem-sfb-profinite-action-coherent-presentation: this is a proper subargument of the returned fifteen-step proof, not the full coherent set/module/direct-image presentation. The precise allocation is in the coverage table below.

lem-sfb-profinite-action-trivial-parameter-fixed vs lem-sfb-profinite-action-coherent-presentation: this is a proper subargument of the returned fifteen-step proof, not the full coherent set/module/direct-image presentation. The precise allocation is in the coverage table below.

lem-sfb-profinite-action-finite-cover-site vs lem-sfb-compact-hausdorff-surjection-quotient: the existing theorem concerns one continuous surjection and its quotient topology, without an action category, finite limits, covering-family axioms or equivariant descent.

lem-sfb-profinite-action-finite-cover-site vs def-sfb-continuous-map-condensed-ring: the latter constructs a ring sheaf on P from a topological ring, without an equivariant action-space site or its limits.

lem-sfb-profinite-action-finite-cover-site vs lem-sfb-profinite-action-finite-quotients: the latter describes inverse limits of finite invariant clopen partitions, not covering axioms, limits in the action category or subcanonical descent.

lem-sfb-profinite-action-finite-cover-site vs lem-sfb-field-profinite-galois-site: the existing theorem identifies a field's pro-etale basis with profinite Galois spaces. The new statement has an arbitrary profinite group and proves the action-space site's own properties without a field or schemes.

lem-sfb-profinite-action-yoneda-free-evaluation vs lem-galois-yoneda-hom-bijection: ordinary Yoneda does not give the internal equivariance equation, sheaf gluing on P_J or evaluation on a free action parameter.

lem-sfb-profinite-action-yoneda-free-evaluation vs lem-sfb-internal-action-site-presentation: that site's objects are base-site objects with twisted arrows (f,a); P_J has all continuous profinite action spaces as objects.

lem-sfb-profinite-action-free-restriction vs lem-sfb-internal-action-site-presentation: free restriction on J times S and right translations is a different construction from restriction to (f,1) on the twisted-arrow site.

lem-sfb-profinite-action-cech-recovery vs lem-sfb-internal-action-site-presentation: the new statement identifies the action-cover fibre square and its equalizer, not descent on the twisted-arrow category.

lem-sfb-profinite-action-module-lift vs lem-sfb-internal-action-site-presentation: the new coefficient ring is the varying equivariant-section ring Q_R(T) on actual profinite action spaces; the existing twisted-arrow-site ring has R_K(U)=R(U).

lem-sfb-profinite-action-module-lift vs def-weil-pbc-internal-abelian-sheaf-module-equivalence: the latter identifies internal modules with sectionwise modules on one fixed site, not free restriction and equivariant Yoneda between the two sites or their linear recovery maps.

lem-sfb-profinite-action-trivial-parameter-fixed vs lem-sfb-action-topos-geometric-restriction: the latter constructs a geometric morphism right adjoint to inflation, but does not identify its direct image with evaluation on trivial profinite action parameters or give the free evaluation formula and the component formulas in this presentation.

lem-sfb-profinite-action-trivial-parameter-fixed vs def-sfb-condensed-action-module: the existing definition specifies the image required of a normalized invariants datum; it does not identify that image with equivariant maps from tS.

## Review by Q54

### Landing-return repair, 2026-10-22

I read the current return entry naming d963b232ccc and the current released stage-1 repair note. Compared with returned-item.json, the current parent has exactly the same statement, statement dependencies, fifteen proof steps, proof dependencies, blueprint provenance and Lean record. The retained split also agrees with current main on its statement, statement dependencies, blueprint, Lean and review metadata. None of the six proposed child ids exists in the current read repository. Thus there is no changed parent hypothesis or superseding child to reconcile. I kept the six statements, their sources, complete archived arguments and all actual search results instead of regenerating them. The initial fresh-base server dry run passed at d7844c5c50d before this documented adjustment.

Because the retained packet has no historical copies of every external dependency, I conservatively re-read all current external statements used to state the seven nodes, as well as the original Yoneda, tensor-sheafification and compact-quotient inputs. For assembly step 1, lem-trf-finitary-site-coherent-generators still states coherent representables for precisely the small finite-limit finite-cover site supplied by finite-cover-site. For step 2, the three retained child statements still supply the actual functors, action-cover equalizer and natural recovery isomorphisms. For step 3, module-lift still supplies the additive linear equivalence data; def-weil-sheaf-of-modules-category explicitly says the target is abelian for a small site. I added that latter citation and its exact quote, and wrote the transported abelian structure explicitly before using kernels and cokernels. For step 4, trivial-parameter-fixed still supplies the same direct-image, normalized fixed-section, free-evaluation and morphism formulas. The current geometric-restriction and normalized-invariants definitions have exactly the adjunction and inclusion hypotheses those statements require. All eight parent citations have verbatim current statement quotes.

I re-read the main-20261015 direct-images source paragraph (3), the chapter and unit, and the two Stacks quotient-topology lemmas. These still support the recorded route and the qualified agent-origin provenance; I have not recast an ordinary-group theorem as an internal-group theorem. The cases J=1, empty parameters and covers, trivial action and R=0 preserve the six statements and their formulas; right-translation composition and the Cech inverse retain the displayed order for noncommutative J. Each child remains statement-only and no parent step exceeds 2000 characters. The final parent proof has 2138 characters. No statement, statement dependency, chapter route, unit route, Lean source, repository or launcher file was changed. The fresh-base final dry run and direct push follow this review; promotion of side completion remains L's operation, not a worker edit.

I checked the return by allocating each old argument to a genuine smaller task; the coverage table and verbatim paragraphs below account for all fifteen steps. The new nodes do not assert the entire original theorem: coherence is still obtained from the pre-existing finitary-site theorem; the set equivalence requires combining the two constructed functors and their recovery maps; exactness is still the parent universal-property argument; the geometric direct-image and normalized invariant formulas are then applied to that same presentation. No new proof step exceeds 2000 characters, and the whole parent proof is below 3000.

For new finite-cover-site, I checked that products and closed equalizers remain compact Hausdorff with clopen bases, that the induced actions are continuous, and that the quotient of a finite coproduct makes glued maps continuous. Equivariance is checked on lifts, so no section of a covering map is assumed. The trivial-action functor preserves the same underlying finite limits and covers. Its source is the old steps 1--3 and the first assertion of old step 14, with the Stacks quotient facts above. No noncompact group is silently used in the free-object assertions.

For new yoneda-free-evaluation, I checked old steps 5--6 against the full statement of lem-galois-yoneda-hom-bijection: evaluation and naturality in both variables are actually stated there. Equality of the two sheaf maps is tested on their representing object J times T, so the equation is universal, not just a point test. Gluing of that equation uses the cover J times T_i. The inverse free map is defined on every profinite V by (a,b) mapping to a acting on b-star x; this is the same natural evaluation used later for modules and morphisms.

For new free-restriction, I checked old steps 7--8: the fibre product over H(S) forces the two J coordinates to agree, giving exactly H(S_i times_S S_j). The action is a left action: r_h composed with r_g equals r_(gh), and contravariance gives F(r_g)F(r_h)=F(r_(gh)). The identity H(f) r_(g composed f)=r_g H(f) checks naturality at every profinite parameter, including noncommutative J. The node includes those equations and naturality for transformations; it requires no comparison lemma hidden in another proof.

For new cech-recovery, I checked old steps 9--10 by composing the displayed coordinate maps and their inverse. The fibre-square condition is j u=j' v, and the inverse is (j,j^{-1}j',v), which indeed maps back to the original pair. The second projection has the order H(pi_T) composed with r_gamma. Applying the contravariant F therefore yields exactly the internal-action equation with the right order, as written. Naturality in u is u a_T=a_T' H(u); free evaluation intertwines the reconstructed action because precomposition by r_g evaluates at (g(s),s). These claims are explicitly conclusions of the new node, not unstated access to its proof.

For new module-lift, I checked old steps 11--12 and the additivity part of 13. The scalar ring on T is Q_R(T), which can be smaller than R(T); the statement does not replace it by R(T). Closure of Q_N under r x uses alpha-star r=pi-star r, since the action on R is trivial. On H(S), free evaluation is the ring map to R(S) and right translation acts identically on that ring. M(a_T) is initially semilinear, and its scalar map evaluates to the inclusion Q_R(T) into R(T), making the recovery isomorphism linear over exactly Q_R(T). I read the full statements of sk-def-sfb-sheaf-tensor and def-weil-pbc-internal-abelian-sheaf-module-equivalence: on the small P site the former supplies strong monoidal abelian sheafification, which satisfies the latter's hypothesis. Thus reconstruction really gives the recorded internal module category rather than silently substituting fixed-ring modules. The module node has no assertion that evaluation on an arbitrary T is exact.

For new trivial-parameter-fixed, I checked old steps 14--15 against lem-sfb-action-topos-geometric-restriction, which explicitly supplies p_J with inverse image trivial inflation. Yoneda and that adjunction identify its sections with equivariant maps from the trivial h_S. Equivariance says that every pulled-back section is fixed by every continuous V to J, exactly the fully fixed condition stated in def-sfb-condensed-action-module. The node quantifies over any specified normalized invariants datum, rather than inventing an unspecified choice of invariants. It records scalar linearity, all base restrictions, and both original-component formulas for a map v. Its geometric assertion is compatible with the same Phi, not some unrelated abstract equivalence.

For parent step 1, I opened the new finite-cover-site statement and lem-trf-finitary-site-coherent-generators. The latter really assumes a small finite-limit site with topology generated by finite covers, and gives coherent sheafified representables and generation. Those hypotheses are exactly the conclusions of the former; subcanonicity then identifies sheafified representables with representables. This remains the declared generic off-unit tool use, with the existing justification retained.

For parent step 2, I opened all three cited new statements. They give the actual restricted Yoneda sheaf functor, the actual free-restriction action functor, and natural isomorphisms in both directions. Therefore the assembly uses their statements to form an equivalence, not a concealed argument from their proofs.

For parent step 3, I opened the module-lift statement. It supplies both additive functors and both linear natural recovery isomorphisms, so they are quasi-inverse on module categories. The remaining exactness argument is just the kernel/cokernel universal property: transport any proposed factorization through the quasi-inverse, obtain the unique factorization there, and transport back; full faithfulness gives uniqueness. The target module-sheaf category is abelian as in def-weil-sheaf-of-modules-category; this also transports the abelian structure to the source. This does not assume section evaluation is exact.

For parent step 4, I opened the new trivial-parameter-fixed statement. It states precisely the p_* comparison, both normalized parameter identifications, the coefficient formula, and naturality on maps and parameters which the assembly claims. The inverse image trivial inflation is part of its hypotheses and the original geometric-morphism node, so the unique right adjoint identifies the same morphism. The separate finite-limit and cover preservation of t has already been supplied in step 1. citations.json quotes the exact statements for each citation; no quote is bent into a claim absent from its node.

I tested J=1 (both parameters and both reconstruction functors become the ordinary ones), S or T empty (the unique empty maps and sheaf sections agree, and the empty family covers only the empty object), the one-point trivial action (the equation is the all-base-change invariant condition), arbitrary nonabelian finite J (the right-translation order and fibre-square inverse remain correct), and R=0 (all module statements reduce to zero modules). These checks exposed no statement error. No STATEMENT-DISPUTED or statement correction is needed.

## Coverage of the returned argument

| Returned step | Destination |
| --- | --- |
| 1 | lem-sfb-profinite-action-finite-cover-site |
| 2 | lem-sfb-profinite-action-finite-cover-site |
| 3 | lem-sfb-profinite-action-finite-cover-site |
| 5 | lem-sfb-profinite-action-yoneda-free-evaluation |
| 6 | lem-sfb-profinite-action-yoneda-free-evaluation |
| 7 | lem-sfb-profinite-action-free-restriction |
| 8 | lem-sfb-profinite-action-free-restriction |
| 9 | lem-sfb-profinite-action-cech-recovery |
| 10 | lem-sfb-profinite-action-cech-recovery |
| 11 | lem-sfb-profinite-action-module-lift |
| 12 | lem-sfb-profinite-action-module-lift |
| 14 | lem-sfb-profinite-action-trivial-parameter-fixed |
| 15 | lem-sfb-profinite-action-trivial-parameter-fixed |
| 4 | Parent assembly step 1, existing lem-trf-finitary-site-coherent-generators |
| 13 | Additivity in module-lift; universal-property exactness in parent assembly step 3 |

The preservation of finite limits and covers by t in old step 14 is included in finite-cover-site as well as used by the final direct-image assembly. This is a coverage overlap, not a missing argument. Every paragraph below is retained as handoff material for the worker proving the corresponding statement-only task; it is not a proof field or a proof sketch inside a new node statement.

## Retained original arguments, verbatim

### Returned step 1

Construct products with diagonal action and equalizers with restricted action. The one-point space with trivial action is terminal. Finite products of compact spaces are compact by [lem-weil-pbc-tychonoff-product-quasi-compact]. Their coordinatewise separating neighbourhoods give the Hausdorff property. By [lem-weil-pbc-profinite-clopen-basis], products have a basis of clopen rectangles. Equalizers of two maps to a Hausdorff space are closed: if their values differ, disjoint neighbourhoods pull back to a neighbourhood disjoint from the equalizer. Hence equalizers are compact by [lem-weil-pbc-closed-in-quasi-compact], Hausdorff by restriction of separating neighbourhoods, and have a clopen basis by intersecting the product basis. A space with a clopen basis separating points is totally disconnected: a subset containing two distinct points is separated by such a clopen and its complement. All restricted actions are continuous, since their composites with the subspace embeddings are the original continuous actions. The universal product and equalizer maps are equivariant, as checked in each coordinate. These constructions give all finite limits, with the underlying-space formulas. Choose the bounded skeleton of [def-weil-size-convention]; its morphisms are subsets of sets of continuous maps, so this is a small category.

Original cited nodes: lem-weil-pbc-tychonoff-product-quasi-compact, lem-weil-pbc-profinite-clopen-basis, lem-weil-pbc-closed-in-quasi-compact, def-weil-size-convention.

### Returned step 2

The covering axioms of [def-weil-pbc-sites-and-cohomology] hold pointwise. An isomorphism is surjective. If $v\in V$ maps into $T$ and $\{T_i\to T\}$ is jointly surjective, choose $t_i$ over its image; then $(t_i,v)\in T_i\times_TV$ lies over $v$. Thus the pulled-back family covers. Given a covering of $T$ and coverings of its members, lift a point first to one member and then to one of that member's covering objects. This proves joint surjectivity of the composite family. A finite union of finite index sets is finite. The empty family covers only the empty object; its pullbacks are again empty. Thus these families are a finite-cover pretopology.

Original cited nodes: def-weil-pbc-sites-and-cohomology.

### Returned step 3

For a finite cover $\{T_i\to T\}$, the map $q:\coprod_iT_i\to T$ is a continuous surjection from a compact space to a Hausdorff space: compactness of the finite disjoint union follows by taking a finite subcover on each summand. It is a quotient map by [lem-sfb-compact-hausdorff-surjection-quotient]. Equivariant continuous maps $u_i:T_i\to U$ agreeing on every $T_i\times_TT_j$ therefore define a unique set map $u:T\to U$. For an open $V\subseteq U$, $q^{-1}(u^{-1}V)$ is open on each summand, hence open; the quotient property makes $u^{-1}V$ open. If $t$ lifts to $t_i$, then $jt$ lifts to $jt_i$, so $u(jt)=u_i(jt_i)=j u_i(t_i)=j u(t)$. Thus the glued map is equivariant. This is the sheaf condition for every representable on $P_J$, proving subcanonicity. With $J$ trivial the same argument proves that $h_T$ is a sheaf on $P$.

Original cited nodes: lem-sfb-compact-hausdorff-surjection-quotient.

### Returned step 4

Apply [lem-trf-finitary-site-coherent-generators] to the small site just constructed. Step 1 verifies finite limits and step 2 gives a finite-cover pretopology generating its topology. The cited theorem gives coherent sheafified representables and a generating family. Step 3 makes sheafification of each representable the representable itself. This proves the coherence and generation assertion, including the empty representable.

Original cited nodes: lem-trf-finitary-site-coherent-generators.

### Returned step 5

For an internal $\underline J$-object $X$ as in [lem-sfb-action-topos-geometric-restriction], Yoneda [lem-galois-yoneda-hom-bijection] identifies a map $h_T\to X$ with $x\in X(T)$. Since $h_J\times h_T=h_{J\times T}$ sectionwise, its equivariance is precisely the equation
$$X(\alpha_T)(x)=\gamma\cdot X(\operatorname{pr}_T)(x)\quad\text{in }X(J\times T),$$
where $\alpha_T(j,t)=jt$ and $\gamma=\operatorname{pr}_J:J\times T\to J$. This tests the equality of the two sheaf maps on the representing object, so tests all profinite base changes, not just ordinary points. For a cover in $P_J$, compatible such $x_i\in X(T_i)$ glue uniquely to $x\in X(T)$ by the $P$-sheaf condition. Their equivariance equations imply the equation for $x$, since $\{J\times T_i\to J\times T\}$ covers $P$ and $X$ is separated. Thus $\Phi(X)$ is a sheaf. Its restrictions and maps are those on these subsets of $X(T)$, by the naturality in the cited Yoneda statement.

Original cited nodes: lem-sfb-action-topos-geometric-restriction, lem-galois-yoneda-hom-bijection.

### Returned step 6

Write $H(S)=J\times S$ with translation on $J$. The free-action formula is
$$\operatorname{Hom}_{\mathscr E^{\underline J}}(h_{H(S)},X)\simeq X(S).$$
Forward evaluation restricts along $s\mapsto(1,s)$. In the reverse direction, $x\in X(S)$ defines the map on a profinite test $V$ by $(a:V\to J,b:V\to S)\mapsto a\cdot b^*x$. Naturality follows from naturality of the action, and equivariance from $c\cdot(a\cdot b^*x)=(ca)\cdot b^*x$. The identity action recovers $x$. Conversely, equivariance says that every $(a,b)$ is obtained by acting by $a$ on $(1,b)$, so recovers the original map. Both constructions commute with maps of $X$ and $S$. This proves the free evaluation formula directly from the definition of internal action.

Original cited nodes: .

### Returned step 7

Construct a quasi-inverse on a sheaf $F$ on $P_J$ by $G(F)(S)=F(H(S))$ and $G(F)(f)=F(\mathrm{id}_J\times f)$. This is a $P$-sheaf: a finite jointly surjective family $\{S_i\to S\}$ gives a cover $\{H(S_i)\to H(S)\}$, and
$$H(S_i)\times_{H(S)}H(S_j)\cong H(S_i\times_SS_j).$$
The isomorphism sends $((j,s_i),(j,s_j))$ to $(j,s_i,s_j)$; the $J$-coordinates must be equal. Therefore the matching families and unique gluings are exactly those for $F$ on this cover, using the sheaf condition of [def-weil-pbc-sites-and-cohomology]. A transformation $F\to F'$ gives $G(F)\to G(F')$ on these sections.

Original cited nodes: def-weil-pbc-sites-and-cohomology.

### Returned step 8

For $g:S\to J$, let $r_g:H(S)\to H(S)$ send $(j,s)$ to $(jg(s),s)$ and define $g\cdot x=F(r_g)(x)$. These are continuous equivariant maps. The identities $r_1=1$ and $r_h\circ r_g=r_{gh}$ give $F(r_g)F(r_h)=F(r_{gh})$, the left-action law. For $f:V\to S$ the equality $H(f)r_{g\circ f}=r_gH(f)$ gives naturality. Thus the sectionwise operations define an internal $\underline J$-action on $G(F)$: on each $S$ the action of $\underline J(S)$ is the displayed map, and the equalities just checked are the sheaf action equations. Transformations commute with $F(r_g)$ and hence are equivariant.

Original cited nodes: .

### Returned step 9

For every $T\in P_J$, the action map $a_T:H(T)\to T$, $(j,t)\mapsto jt$, is a singleton cover. Its fibre square is identified with $H(J\times T)$ by
$$(j,k,t)\longmapsto\big((j,kt),(jk,t)\big).$$
The inverse takes $((j,u),(j',v))$ with $ju=j'v$ to $(j,j^{-1}j',v)$. The maps and inverse are continuous and equivariant, with $J$ acting on the first coordinate. Under this identification the projections are $H(\alpha_T)$ and $H(\operatorname{pr}_T)\circ r_\gamma$, where $\gamma(k,t)=k$. The sheaf condition of [def-weil-pbc-sites-and-cohomology] consequently says that $F(a_T)$ is a bijection from $F(T)$ onto
$$\{x\in G(F)(T):G(F)(\alpha_T)(x)=\gamma\cdot G(F)(\operatorname{pr}_T)(x)\}.$$
Indeed the two pullbacks of $x$ are respectively $F(H(\alpha_T))x$ and $F(r_\gamma)F(H(\operatorname{pr}_T))x$, exactly the displayed equation by step 8. This is the equivariant Yoneda subset of step 5. No comparison lemma for a new site is being assumed.

Original cited nodes: def-weil-pbc-sites-and-cohomology.

### Returned step 10

Step 9 gives $F\simeq\Phi G(F)$. It is natural in $F$ by functoriality and in an equivariant $u:T\to T'$ because $u a_T=a_{T'}H(u)$. Step 6 gives $G\Phi(X)\simeq X$ on underlying sheaves. It respects actions: precomposing the free map of a section $x$ with $r_g$ changes its value at $(1,s)$ to its value at $(g(s),s)$, namely $g\cdot x$. It is natural in all equivariant maps by the same evaluation formula. Hence $G$ and $\Phi$ with these natural isomorphisms are quasi-inverse functors, proving the claimed equivalence of topoi.

Original cited nodes: .

### Returned step 11

On the small profinite site, [sk-def-sfb-sheaf-tensor] with coefficient category $\Ab$ supplies abelian sheafification and its strong symmetric monoidal structure, verifying the sheafification hypotheses of [def-weil-pbc-internal-abelian-sheaf-module-equivalence]. Pass from internal modules to their section modules using that equivalence; it preserves section groups and restriction maps identically. By [def-sfb-condensed-action-module], the action on each $N(T)$ is $R(T)$-linear and compatible with every base restriction. The subset defining $\Phi(N)(T)$ is closed under addition and negatives. For $r\in\mathcal R_J(T)=\Phi(R)(T)$ and $x\in\Phi(N)(T)$ put $rx$ equal to their ordinary product in $N(T)$. On $J\times T$, $\alpha_T^*r=\operatorname{pr}_T^*r$, since $R$ has trivial action and $r$ is equivariant. Thus
$$\alpha_T^*(rx)=(\operatorname{pr}_T^*r)(\gamma\cdot\operatorname{pr}_T^*x)=\gamma\cdot\operatorname{pr}_T^*(rx).$$
This proves closure under scalars. The module laws and semilinear restrictions hold in $N(T)$, so also in these subsets. Therefore $\Phi(N)$ is a sheaf of $\mathcal R_J$-modules in the sense of [def-weil-sheaf-of-modules-category], and an equivariant linear map induces its sectionwise restriction.

Original cited nodes: sk-def-sfb-sheaf-tensor, def-weil-pbc-internal-abelian-sheaf-module-equivalence, def-sfb-condensed-action-module, def-weil-sheaf-of-modules-category.

### Returned step 12

Conversely, if $M$ is a sheaf of $\mathcal R_J$-modules, give $G(M)(S)=M(H(S))$ its section module structure through the free evaluation isomorphism $\mathcal R_J(H(S))\simeq R(S)$ of step 6. The right translation $r_g$ induces the identity on this ring: an equivariant map from $J\times S$ to trivially acted-on $R$ takes $(j,s)$ to the pullback of a section on $S$, independent of $j$. Consequently $M(r_g)$ is $R(S)$-linear. Restrictions along $H(f)$ are semilinear for $R(f)$ by the naturality of free evaluation. These section modules reconstruct an internal $R$-module by [def-weil-pbc-internal-abelian-sheaf-module-equivalence], and step 8 supplies its linear action. The isomorphism $G\Phi(N)\simeq N$ evaluates the same section operations at the identity, so is linear. For $M\simeq\Phi G(M)$, the map $M(a_T)$ is semilinear over $\mathcal R_J(a_T)$. Evaluating that ring map at $(1,t)$ recovers the original section $r\in\mathcal R_J(T)\subseteq R(T)$, so the isomorphism is linear over precisely $\mathcal R_J(T)$. Thus the quasi-inverses restrict to the asserted module equivalence.

Original cited nodes: def-weil-pbc-internal-abelian-sheaf-module-equivalence.

### Returned step 13

Both module functors preserve addition of maps: $\Phi$ restricts the componentwise sums and $G$ evaluates them on $H(S)$. They are therefore additive for the structure in [def-sfb-condensed-action-module]. An equivalence preserves kernels and cokernels: transport a proposed factorization along a quasi-inverse, apply the original unique factorization, and transport back; faithfulness preserves its uniqueness. Hence this additive equivalence preserves the kernel and cokernel diagrams defining exact sequences of module sheaves [def-weil-sheaf-of-modules-category], and so is exact. This assertion does not claim that evaluation on $T$ is an exact functor.

Original cited nodes: def-sfb-condensed-action-module, def-weil-sheaf-of-modules-category.

### Returned step 14

Equipping spaces with trivial action leaves terminal objects, products and equalizers as in step 1 and leaves the underlying covering maps unchanged, so $t$ preserves finite limits and coverings. The direct image $p_{J,*}$ of [lem-sfb-action-topos-geometric-restriction] is right adjoint to trivial inflation. For an action $X$, sections $(p_{J,*}X)(S)$ are, by Yoneda and this adjunction, the equivariant maps from trivially inflated $h_S$ to $X$. This is $\Phi(X)(tS)$. Equivalently, an ordinary section $x\in X(S)$ lies in this set precisely when every pullback $f^*x$ is fixed by every $g:V\to J$, which is exactly the condition that the corresponding $h_S\to X$ is equivariant. Thus restriction $F\mapsto(S\mapsto F(tS))$ is the direct image of $p_J$ under $\Phi$, so $t$ presents the indicated geometric morphism, with its inverse image identified by the unique adjunction.

Original cited nodes: lem-sfb-action-topos-geometric-restriction, lem-galois-yoneda-hom-bijection.

### Returned step 15

For trivial $R$, every map $h_{tS}\to R$ is equivariant, giving $\mathcal R_J(tS)=R(S)$. For a module $N$, the last description of step 14 identifies $\Phi(N)(tS)$ with the fully fixed sections of [def-sfb-condensed-action-module], hence with the normalized invariants object via its specified inclusion and image. The free formula of step 6 gives $\Phi(N)(H(S))=N(S)$. These are module identifications: fixed sections use the ordinary scalar action, and free evaluation uses $\mathcal R_J(H(S))\simeq R(S)$. For an equivariant linear map $v:N\to N'$, fixed evaluation sends $x$ to $v_S(x)$ in the fixed subset; free evaluation sends an equivariant map $b$ to $b_S(1,\mathrm{id}_S)$, and $v\circ b$ evaluates to $v_S(b_S(1,\mathrm{id}_S))$. Under $f:S'\to S$ both operations pull back the same sections by $f$. This proves every stated naturality and the two on-morphism formulas.

Original cited nodes: def-sfb-condensed-action-module.

## Remaining work

The six new unsplit nodes intentionally require independent stage-1 splitting and later formalization. This delivery completes only the authorized one-level re-split. An exact external source for the auxiliary internal-group presentation remains wanted as above. Required server dry run and direct push are performed after this review; their terminal output is the delivery evidence.
