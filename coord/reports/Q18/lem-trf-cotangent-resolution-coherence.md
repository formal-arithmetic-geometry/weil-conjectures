# Q18 stage-1 repair: lem-trf-cotangent-resolution-coherence

## Files written

- Item: lem-trf-cotangent-resolution-coherence, statement unchanged; three-step assembly.
- lem-trf-polynomial-augmentation-boundary: statement-only, unsplit; no Mathlib match. Polynomial augmentations: standard resolution and boundary lifting criterion.
- lem-trf-polynomial-presentation-homology: statement-only, unsplit; no Mathlib match. Representable contractibility and homology of polynomial presentations.
- lem-trf-polynomial-square-bar-naturality: statement-only, unsplit; no Mathlib match. Explicit ring-square maps and naturality of polynomial bar comparisons.

## Attachments

None. Read-only project-source searches for the blueprint tag, standard resolutions and polynomial resolutions found no complete WeilConjectures declaration. The library's Sheaf.RingTheory.CotangentResolutionCoherence theorem Algebra.CotangentResolution.exists_coherence still ends in sorry (lines 341–344).

## WANTED

None. All Stacks sources used are in literature/stacks-project/.

## What was wrong and what changed

The released stage-1 repair note of 2026-10-22 explicitly reopens the landed split despite its reviewed record. The return is about distributing a 7900-character proof into parallel tasks, not changing the statement. The sandbox initially contained only dispatcher marker files: there was no returned node/report/search log to reuse. I copied the current live node as the repair baseline. No repository or launcher file was changed and no git/compiler/Lake command was run.

The three new nodes own old Steps 1–3, 4–6 and 7–9, respectively. Each statement introduces its own rings, complexes and maps. The first is an augmentation/boundary theorem independent of cotangent modules. The second works for arbitrary module-valued functors on the presentation category, not only differentials. The third gives the explicit recursive maps and their equality under the canonical bar comparisons, not the existence of all cotangent-resolution coherence data. The parent constructs its canonical comparisons and proves their compatibility by cancellation. These are three substantial arguments of comparable size, not a single renamed copy of the item. No dropped model/realization machinery is added.

## Mathlib and duplicate searches

Ran leanfinder, loogle, grep and leansearch for each prospective task using the required msearch.py wrapper. Different semantic phrasings were used before concluding absence. searches.jsonl holds the exact queries, result counts, names and digests; new nodes record precisely those queries. Grep searches covered RingTheory for algebra assertions and the whole Mathlib for derived colimits. Read candidate sources: RingTheory/Extension/Cotangent/Basic.lean:53–65 and 194–207 (a single conormal differential and its map), :339–344 (H1 of that differential); AlgebraicTopology/ExtraDegeneracy.lean:410–433 (requires preadditivity and additive extra degeneracies, unlike the set-valued contraction here); AlgebraicTopology/DoldKan/HomotopyEquivalence.lean:79 (normalization vs alternating complex); CategoryTheory/Functor/Derived/PointwiseRightDerived.lean:45–90 (pointwise localization/Kan extension, not representable resolutions); Algebra/Module/Presentation/Differentials.lean:117–131 (conormal presentation square). The other hits are generic simplicial definitions, free algebras, filtered-colimit/coyoneda preservation, or free Yoneda objects; none asserts the new statements or a one-line specialization.

Searched the entire DAG by relevant tags 08PM/08PN/08QI/08QL/08PS/08PT and concepts polynomial resolution, representable contractibility and ring-square maps. Ran tools/blueprint_refs.py ancestor on the item and searches for polynomial resolution, 08PS, 08QL, resolution, cotangent, representable contractibility, ring square and standard simplicial. No blueprint node states a prospective task. All three inherit the exact existing historical ancestor and via chain, with this item prepended. Read every same-source-tag candidate's statement (differences below). Some downstream statements have overlapping consequences but depend on this item, so importing them would be circular; no such import is made.

## Original proof retained and ownership of each argument

The following text is copied verbatim from the current returned split. It is source material and handoff detail for workers, not proof steps in the new unsplit nodes.

### Old Step 1 — owned by lem-trf-polynomial-augmentation-boundary

Apply [lem-trf-adjunction-standard-simplicial-homotopy] to the adjunction $F_A:\mathrm{Set}\rightleftarrows A\text{-}\mathrm{Alg}:U$; its adjunction bijection sends an algebra map $A[E]\to C$ to its values on the variables. This gives exactly the faces, degeneracies and augmentation in the statement, and gives a simplicial-set homotopy inverse to the underlying standard augmentation. Each term is polynomial. Each evaluation $A[UC]\to C$ is surjective because $[c]\mapsto c$; iterating these evaluations shows that every standard augmentation is surjective. The unit is a map of sets; no additivity of this section is asserted.

Cited inputs: lem-trf-adjunction-standard-simplicial-homotopy.

### Old Step 2 — owned by lem-trf-polynomial-augmentation-boundary

Forget the standard augmented simplicial algebra of Step 1 to simplicial abelian groups. Its underlying simplicial-set augmentation is a homotopy equivalence, so [lem-trf-simplicial-abelian-set-homotopy-quasi-iso] applies directly and gives a quasi-isomorphism $s(P^{\mathrm{std}})\to s(\operatorname{const}B)$. The map $s(\operatorname{const}B)\to B[0]$ is the identity in degree zero. In degree $-n$ its differential for $n>0$ is zero when $n$ is odd and the identity when $n$ is even, since it is the alternating sum of $n+1$ identity maps. Consequently its negative degrees form exact two-term identity pairs and it is a quasi-isomorphism. Composing these two maps proves that the standard augmentation is a polynomial resolution in exactly the stated sense. The homotopy inverse used here is only a map of simplicial sets; it is not asserted to be additive.

Cited inputs: lem-trf-simplicial-abelian-set-homotopy-quasi-iso.

### Old Step 3 — owned by lem-trf-polynomial-augmentation-boundary

Let $Q_\bullet\to B$ be any polynomial resolution in the statement. Forgetting multiplication makes its augmentation a morphism of simplicial abelian groups, termwise surjective by hypothesis. The hypothesis gives a quasi-isomorphism $s(Q)\to B[0]$. Factor it as $s(Q)\to s(\operatorname{const}B)\to B[0]$. The second map induces isomorphisms on cohomology by the constant-complex calculation of Step 2, so the first one does also: on each cohomology group its map is the inverse of the second map followed by the given isomorphism. Thus [lem-trf-simplicial-abelian-surjective-quasi-iso-boundary-lifting] applies and says that $Q\to\operatorname{const}B$ has every boundary lift, including dimension zero. In particular it is a trivial Kan fibration in the boundary-defined sense of [def-weil-pbc-trivial-kan-fibration]. The same applies to the standard resolution by Steps 1 and 2.

Cited inputs: lem-trf-simplicial-abelian-surjective-quasi-iso-boundary-lifting, def-weil-pbc-trivial-kan-fibration.

### Old Step 4 — owned by lem-trf-polynomial-presentation-homology

Choose universes $\mathcal U\in\mathcal V$ as in [def-weil-size-convention], with the rings and all the resolutions in question $\mathcal U$-small. Let $\mathcal D_{B/A}$ have as objects all $\mathcal U$-small polynomial $A$-algebras $T$ equipped with an $A$-algebra map $T\to B$ (not required to be surjective), and as arrows algebra maps over $B$. All their structure data and maps form sets in $\mathcal V$, so this is a small category there; complexes and modules below are taken in $\mathcal V$. A resolution is a simplicial object of this category. For $T=A[E]\to B$, maps $T\to Q_n$ over $B$ are precisely choices, for every $e\in E$, of an element of $Q_n$ mapping to the prescribed image of $e$ in $B$. This bijection commutes with all simplicial operators, by evaluation on generators.

Cited inputs: def-weil-size-convention.

### Old Step 5 — owned by lem-trf-polynomial-presentation-homology

The simplicial set $\operatorname{Hom}_{\mathcal D_{B/A}}(T,Q_\bullet)$ maps to a singleton by a trivial Kan fibration. To check the boundary lifting condition of [def-weil-pbc-trivial-kan-fibration], a boundary of algebra maps is, on each generator $e$, a boundary in $Q$ above the constant simplex $\epsilon_T(e)\in B$. Step 3 supplies a filler for each generator; choose these fillers and extend them uniquely to an algebra map out of $A[E]$. This gives the required filler of algebra maps, and degree-zero surjectivity is proved by the same choice of generator lifts. This works for an empty set or an infinite set of generators, without finite-generation assumptions. Now [lem-weil-pbc-trivial-kan-homotopy-equivalence] supplies a homotopy equivalence with the singleton. This argument applies both to $Q$ and to the standard resolution.

Cited inputs: def-weil-pbc-trivial-kan-fibration, lem-weil-pbc-trivial-kan-homotopy-equivalence.

### Old Step 6 — owned by lem-trf-polynomial-presentation-homology

Define the covariant functor $\mathcal F_{B/A}(T)=\Omega^1_{T/A}\otimes_T B$ on $\mathcal D_{B/A}$. An arrow $v:T\to T'$ induces $dt\otimes b\mapsto d(vt)\otimes b$; existence and equality under composition follow from the universal derivation in [def-weil-pbc-kahler-differentials]. Set $K(Q)=s(\mathcal F_{B/A}(Q_\bullet))$ and $H_{B/A}=\mathbf H(\mathcal D_{B/A},\mathcal F_{B/A})$. Steps 4 and 5 verify precisely the smallness and representable-contractibility assumptions of [lem-trf-simplicial-derived-colimit-computation]. Its isomorphisms are $a_Q:K(Q)\simeq H_{B/A}$ and $a_{\mathrm{std}}:L_{B/A}\simeq H_{B/A}$. Define $c_Q=a_{\mathrm{std}}^{-1}a_Q$. Its naturality says $a_R K(h)=a_Q$ for any augmented resolution morphism $h:Q\to R$, so $c_R K(h)=c_Q$. This proves the canonical comparison and its naturality in the derived category [def-weil-abstract-derived-category]. No maps in both directions between arbitrary algebra resolutions have been assumed.

Cited inputs: def-weil-pbc-kahler-differentials, lem-trf-simplicial-derived-colimit-computation, def-weil-abstract-derived-category.

### Old Step 7 — owned by lem-trf-polynomial-square-bar-naturality

For a ring square $(\alpha:A\to A',\beta:B\to B')$, define $t_{-1}=\beta$ and recursively $t_{n+1}:A[UP_n]\to A'[UP'_n]$ by $a\mapsto\alpha(a)$ and $[p]\mapsto[t_n(p)]$; similarly $t_0:A[UB]\to A'[UB']$. Evaluation commutes with these maps because both composites send $[p]$ to $t_n(p)$. Insertion of the unit commutes as well because both composites send a variable to the variable labelled by its image. Applying this at the relevant iteration gives commutation with every face, degeneracy and augmentation. For an identity square the recursion fixes coefficients and variables; for two squares the composite recursion sends $[p]$ to $[t'_nt_n(p)]$. Uniqueness of a map from a polynomial algebra with specified generator values therefore gives strict identity and composition in every degree. Finally the rule $dp\otimes b\mapsto d(t_np)\otimes\beta(b)$ is balanced and kills the relative-derivation relations, by [def-weil-pbc-kahler-differentials]; it gives the required semilinear map of differential complexes and preserves those strict identities.

Cited inputs: def-weil-pbc-kahler-differentials.

### Old Step 8 — owned by lem-trf-polynomial-square-bar-naturality

The square also defines a functor $u:\mathcal D_{B/A}\to\mathcal D_{B'/A'}$ by $T\mapsto T\otimes_A A'$ with augmentation $t\otimes a'\mapsto\beta(\epsilon_T(t))a'$. It remains polynomial: $A[E]\otimes_A A'\simeq A'[E]$, as follows from the mutually inverse maps fixing coefficients and variables. The maps $dt\otimes b\mapsto d(t\otimes1)\otimes\beta(b)$ define $\theta:\mathcal F_{B/A}\to\operatorname{Res}_\beta(\mathcal F_{B'/A'}\circ u)$ by [def-weil-pbc-kahler-differentials]. A supplied semilinear augmented simplicial map $h:Q\to Q'$ gives $k:uQ\to Q'$ by $q\otimes a'\mapsto h(q)a'$, and the standard map of Step 7 gives such a $k$ for the standard resolutions. Neither $uQ$ nor its augmentation is claimed to be a resolution: only the endpoints $Q,Q'$ need be resolutions.

Cited inputs: def-weil-pbc-kahler-differentials.

### Old Step 9 — owned by lem-trf-polynomial-square-bar-naturality

Apply the reindexing naturality clause of [lem-trf-simplicial-derived-colimit-computation] to the data of Step 8. Write $H(\alpha,\beta)=\mathbf H(u,\theta)$. It gives $a_{Q'}K(h)=H(\alpha,\beta)a_Q$; for standard resolutions it gives $a'_{\mathrm{std}}K(t)=H(\alpha,\beta)a_{\mathrm{std}}$. Restriction of scalars is understood on every target. Substituting $c_Q=a_{\mathrm{std}}^{-1}a_Q$ and $c_{Q'}=(a'_{\mathrm{std}})^{-1}a_{Q'}$ yields $c_{Q'}K(h)=K(t)c_Q$. Thus whenever a map between chosen resolutions is supplied it gives exactly the standard derived map through the canonical comparisons. For arbitrary choices of resolutions define the transported map by $c_{Q'}^{-1}K(t)c_Q$; the same equation proves agreement with every supplied $h$. Its identity law is $c_Q^{-1}c_Q=1$, and its composition law follows by cancelling the middle $c_{Q'}c_{Q'}^{-1}$ and using the strict composition of Step 7. Changing resolutions is likewise transitive by cancelling the common factor. This proves the final compatibility clause without asserting the existence of algebra homotopy inverses.

Cited inputs: lem-trf-simplicial-derived-colimit-computation.

## Review by Q18

I read cotangent.tex's definition-standard-resolution (08PM), definition-cotangent-complex-ring-map (08PN), lemma-identify-pi-shriek (08PS), both proofs of lemma-pi-shriek-standard (08PT), remark-resolution (08QI), and section-functoriality (08QL), together with the statements of all nine old proof inputs. The old Steps 1–3 use the adjunction contraction only after forgetting to sets, then the set-homotopy-to-quasi-isomorphism statement (which explicitly permits nonadditive inverse/homotopies), and finally the surjective-quasi-isomorphism boundary-lifting criterion. I checked these hypotheses against their node statements; nothing requires an additive unit or a model structure. Constant s(B) has d^{-n}=0 for odd n and 1 for positive even n, so the augmentation to B[0] is a quasi-isomorphism, including the zero ring. New task 1 preserves this calculation and both augmentation conclusions. It does not claim arbitrary polynomial algebras have additive contracting homotopies.

For old Steps 4–6, I checked the size-convention statement and the generic simplicial-derived-colimit-computation statement: the category must be small in the working universe and EVERY representable evaluation must be contractible. The category of all U-small polynomial presentations is a V-set, rather than an unbounded large category. New task 2 includes smallness, the exact generator-fibre identification, boundary lifting including n=0, and the homotopy equivalence to the singleton, so its comparison really has the required hypotheses. Empty generators give the singleton and infinite generators are handled by choice; no finite-generation hypothesis was smuggled in. The old trivial-kan-homotopy-equivalence input supplies exactly the claimed homotopy inverse after fillers are supplied. Its statement was read, rather than inferred from its name. The differential functor remains in the parent, where existence and composition follow by evaluating universal differentials on dx. This uses precisely the universal-property statement of def-weil-pbc-kahler-differentials.

For old Steps 7–9 I read the reindexing clause of lem-trf-simplicial-derived-colimit-computation: it allows k:uQ→Q' without contractibility of uQ and interprets scalar restriction degreewise on bar models. New task 3 retains the coefficient/variable recursion, commutation with faces and degeneracies, strict identity/composition, the polynomial base-change isomorphism, the augmentation of u(T), theta, k and the equality of the bar comparisons. It includes the standard case. I checked the identity and composite ring squares and nonflat squares: neither base-change functoriality nor k assumes uQ remains a resolution. There is no claim of algebra homotopy inverses. The report's old text retains the full explicit arguments the future worker must formalize.

Assembly Step 1 cites new task 1 for exactly the standard augmentation and the criterion applying to arbitrary polynomial resolutions. Assembly Step 2 cites new task 2 for a_Q and its naturality, and the Kähler definition for functorial differential maps; its hypotheses were established by Step 1. Assembly Step 3 cites new task 3 for the recursive standard maps and a_{Q'}K(h)=H(u,theta)a_Q, including its standard specialization. Multiplying by a_{P'}^{-1} proves c_{Q'}K(h)=K(t)c_Q; adjacent inverse cancellations give all transport laws. These equations are valid in D(B) with the indicated restriction of scalars; no scalar-extension isomorphism is assumed. citations.json quotes the cited statements verbatim. All new nodes are statement-only (empty proof and proof_deps, null proof_origin, unsplit), use genuine Stacks places, and retain the historical blueprint route. There is no statement dispute, no target change and no unit/chapter edit. The return's two-node minimum is exceeded by three comparable tasks; the parent assembly has fewer than 3000 characters. Every former argument has a named owner and is preserved verbatim above.

## Not duplicates

lem-trf-polynomial-augmentation-boundary vs def-trf-cotangent-resolution-data: this is only a definition of coherence data and predicates, with no existence, contractibility or comparison theorem.

lem-trf-polynomial-augmentation-boundary vs lem-trf-adjunction-standard-simplicial-homotopy: the existing node states Standard simplicial object of an adjunction and its homotopy equivalences; this new task isolates the indicated polynomial-resolution supporting construction with its own hypotheses, rather than that assertion.

lem-trf-polynomial-augmentation-boundary vs lem-trf-cotangent-resolution-coherence: the parent combines augmentation, canonical cotangent comparisons and all ring-square coherence; this task isolates only its indicated supporting argument and adds no replacement whole-coherence claim.

lem-trf-polynomial-augmentation-boundary vs lem-trf-cotangent-sheaf-model: this downstream sheaf-site formulation depends on the parent coherence theorem; it neither supplies the boundary criterion nor establishes its representable hypotheses or the explicit general h comparison construction. Citing it here would be circular.

lem-trf-polynomial-augmentation-boundary vs lem-trf-simplicial-abelian-set-homotopy-quasi-iso: the existing node states Underlying simplicial-set homotopy equivalence induces an abelian-group quasi-isomorphism; this new task isolates the indicated polynomial-resolution supporting construction with its own hypotheses, rather than that assertion.

lem-trf-polynomial-augmentation-boundary vs lem-trf-simplicial-abelian-surjective-quasi-iso-boundary-lifting: the existing node states Surjective simplicial abelian-group quasi-isomorphisms fill boundaries; this new task isolates the indicated polynomial-resolution supporting construction with its own hypotheses, rather than that assertion.

lem-trf-polynomial-augmentation-boundary vs lem-trf-surjective-qis-simplicial-group-trivial-kan: the existing node states Termwise surjective quasi-isomorphisms of simplicial abelian groups are trivial Kan fibrations; this new task isolates the indicated polynomial-resolution supporting construction with its own hypotheses, rather than that assertion.

lem-trf-polynomial-augmentation-boundary vs lem-trf-tor-independent-cotangent-base-change: this is the additional Tor-independent criterion ensuring tensoring a resolution stays a resolution; this task imposes no Tor-independent base-change assumption and does not assert that tensoring stays a resolution.

lem-trf-polynomial-presentation-homology vs def-trf-cotangent-resolution-data: this is only a definition of coherence data and predicates, with no existence, contractibility or comparison theorem.

lem-trf-polynomial-presentation-homology vs lem-trf-cotangent-lower-shriek-polynomial-top: the existing node states Polynomial target evaluation of the presentation-pair derived colimit; this new task isolates the indicated polynomial-resolution supporting construction with its own hypotheses, rather than that assertion.

lem-trf-polynomial-presentation-homology vs lem-trf-cotangent-resolution-coherence: the parent combines augmentation, canonical cotangent comparisons and all ring-square coherence; this task isolates only its indicated supporting argument and adds no replacement whole-coherence claim.

lem-trf-polynomial-presentation-homology vs lem-trf-cotangent-sheaf-model: this downstream sheaf-site formulation depends on the parent coherence theorem; it neither supplies the boundary criterion nor establishes its representable hypotheses or the explicit general h comparison construction. Citing it here would be circular.

lem-trf-polynomial-presentation-homology vs lem-trf-simplicial-derived-colimit-computation: the existing node states Contractible representable evaluations compute derived colimits, with reindexing naturality; this new task isolates the indicated polynomial-resolution supporting construction with its own hypotheses, rather than that assertion.

lem-trf-polynomial-presentation-homology vs lem-trf-tor-independent-cotangent-base-change: this is the additional Tor-independent criterion ensuring tensoring a resolution stays a resolution; this task imposes no Tor-independent base-change assumption and does not assert that tensoring stays a resolution.

lem-trf-polynomial-square-bar-naturality vs lem-sfb-scheme-cotangent-transitivity: this is a transitivity triangle for schemes and its functoriality, not a polynomial augmentation or presentation-category/bar theorem.

lem-trf-polynomial-square-bar-naturality vs def-trf-cotangent-resolution-data: this is only a definition of coherence data and predicates, with no existence, contractibility or comparison theorem.

lem-trf-polynomial-square-bar-naturality vs def-trf-derived-colimit-bar-system: the existing node states Category-colimit bar models and functorial bar systems; this new task isolates the indicated polynomial-resolution supporting construction with its own hypotheses, rather than that assertion.

lem-trf-polynomial-square-bar-naturality vs lem-trf-cotangent-lower-shriek-polynomial-top: the existing node states Polynomial target evaluation of the presentation-pair derived colimit; this new task isolates the indicated polynomial-resolution supporting construction with its own hypotheses, rather than that assertion.

lem-trf-polynomial-square-bar-naturality vs lem-trf-cotangent-resolution-coherence: the parent combines augmentation, canonical cotangent comparisons and all ring-square coherence; this task isolates only its indicated supporting argument and adds no replacement whole-coherence claim.

lem-trf-polynomial-square-bar-naturality vs lem-trf-cotangent-sheaf-model: this downstream sheaf-site formulation depends on the parent coherence theorem; it neither supplies the boundary criterion nor establishes its representable hypotheses or the explicit general h comparison construction. Citing it here would be circular.

lem-trf-polynomial-square-bar-naturality vs lem-trf-derived-colimit-bar: the existing node states Category bar complex and functorial derived colimits; this new task isolates the indicated polynomial-resolution supporting construction with its own hypotheses, rather than that assertion.

lem-trf-polynomial-square-bar-naturality vs lem-trf-simplicial-derived-colimit-computation: the existing node states Contractible representable evaluations compute derived colimits, with reindexing naturality; this new task isolates the indicated polynomial-resolution supporting construction with its own hypotheses, rather than that assertion.

lem-trf-polynomial-presentation-homology vs lem-trf-simplicial-derived-colimit-computation: the existing theorem assumes a small category and contractible representable evaluations; the new task proves these hypotheses for polynomial presentations, including the generator-fibre boundary-lifting assertion. Its comparison is a specialization after those substantive hypotheses have been proved.

lem-trf-polynomial-square-bar-naturality vs lem-sfb-standard-sheaf-cotangent-flat-functorial-model: the existing sheaf-flatness statement depends through lem-trf-affine-cotangent-comparison on this parent; the new task constructs the plain-ring u, theta and k, and proves their arbitrary-resolution bar identity. It neither claims sheaf flatness nor follows by specialization of an independently available statement.

## Unfinished work

The three deliberately unsplit tasks await other workers. No new Lean statements or proofs were requested. Required server dry run and push results are recorded by the delivery command.
