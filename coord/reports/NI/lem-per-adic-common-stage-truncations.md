# Stage-1 delivery: lem-per-adic-common-stage-truncations

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-adic-common-stage-truncations.json: retained statement and statement dependencies; replaced nine-step proof by a 2502-character five-step assembly.
- dag/nodes/sec-deligne-laumon-a1/lem-per-texact-system-triangle-coherence.json: statement, unsplit; no Mathlib match. Extracts the tower, cohomology and full-boundary argument of old steps 4–5.
- dag/nodes/sec-deligne-laumon-a1/lem-per-directed-pair-simultaneous-bounds.json: statement, unsplit; no Mathlib match. Extracts old step 9 as simultaneous realization of finitely many upper/lower bounds, with the heart consequence.
- citations.json: every item-step citation, with a verbatim statement quote.
- searches.jsonl: searches run by msearch.py; no invented searches. Extra finite-free searches were exploratory and do not claim a third delivered node.
- original-item.json: saved live input for interruption recovery; not a delivered DAG file.

## Attachments

None. I searched WeilConjectures by the blueprint id and by common-stage/truncation terminology; no project declaration there proves this assertion. The live attached Sheaf.Paper.PerAdicCommonStageTruncations declaration ends with sorry (line 415), so it is not an attachment. No Lean was written or compiled.

## WANTED

None: Bhatt–Scholze and BBD are available locally. The abstract new statements are agent extractions of the retained argument, rather than falsely attributed verbatim theorems of those sources.

## Repairs and scope

The released stage-1 repair record dated 2026-10-22 explicitly reopens the previously reviewed item and requires at least two new nodes and an assembly of at most 3000 characters. This delivery adds two independently usable statement-only nodes of comparable statement size (2225 and 1971 characters). Their proof and proof_deps are empty, proof_origin null, status unsplit; the complete old arguments are retained below for the workers who split those nodes. I did not copy either new node's proof into its statement.

The statement is unchanged; no STATEMENT-DISPUTED correction was needed. Existing metadata and the Lean record are retained. The supplied stage-1 repair order is the reason for changing a node whose old reviewed field says pass. No unit or chapter file is changed.

A newly available existing node, lem-pod-directed-pair-bounded-tstructure, states exactly the abstract t-structure and representative formula needed in old steps 6–8. The no-duplicate rule requires citing it instead of creating another copy. Its statement explicitly includes representative independence, canonical maps and distinguished truncation triangles; these are not being borrowed from its proof (it is unsplit). Accordingly old steps 6–8 are assigned to that existing task, while the two new tasks cover coherence and simultaneous heart realization. All nine old arguments remain verbatim below; nothing is dropped or blurred to shorten the assembly.

lem-pod-completed-scalar-extension-texact was also read. Its integral category cites def-weil-derived-complete-integral-detailed, whereas this item's category explicitly includes compatible etale-origin witnesses. I therefore do not substitute that node silently: step 1 retains the finite-free calculation and cites the completed scalar comparison and the exact constructible-transport theorem for this category.

## Not duplicates

lem-per-texact-system-triangle-coherence vs lem-pod-texact-truncation-comparison: the latter gives normalized single-truncation comparisons and their composition/natural-transformation laws. The new task additionally proves the full shifted boundary square, compatibility of the complete triangle and cutoff maps, and the explicit cohomology associator equation for an exact system. It retains old steps 4–5 as a separate argument.
lem-per-texact-system-triangle-coherence vs lem-zl-texact-cohomology-boundary-comparison: that node compares the long-exact-sequence cohomology boundary of an arbitrary triangle for one functor. This task identifies the entire standard truncation triangle and supplies system associator and cohomology equations.
lem-per-texact-system-triangle-coherence vs lem-pod-directed-pair-bounded-tstructure: that task constructs a t-structure on a directed quotient and gives the quotient arrow formula. The new task is a finite-system comparison theorem, without any pair category or descent conclusion.
lem-per-directed-pair-simultaneous-bounds vs lem-pod-directed-pair-bounded-tstructure: the existing statement does not assert simultaneous realization of specified isomorphisms and their inverse equations, nor that an intersection of the two half closures comes from a single stage heart. The new node assumes the finite-diagram realization interface and isolates that simultaneous-witness argument, for arbitrary finite bound lists.
lem-per-directed-pair-simultaneous-bounds vs prop-weil-pbc-common-stage-calculus: that node realizes finite diagrams and equations but says nothing about upper/lower classes or hearts. The new task additionally uses t-exactness to put all bounds on the same stage object, and concludes the heart identification.
lem-per-directed-pair-simultaneous-bounds vs lem-per-adic-common-stage-truncations: the new task is a generic finite diagram/heart argument with t-exactness and pair calculus assumed; it proves neither completed scalar t-exactness, normalized comparisons, nor the common-stage t-structure. It does not move the whole item into one node.

The whole-DAG and whole-blueprint searches included truncation, t-exact, scalar, finite free, heart, and common stage; candidates were opened and their statements read. The new nodes use BBD/Bhatt–Scholze references, not Stacks tags; there are no same-tag pairs needing a Stacks-specific duplicate comparison. Finite-field Weil-pair truncations have extra Frobenius data and are not the ordinary pair-category assertion here. lem-a1-texact-coefficient-stage-descent assumes the pair t-structure being constructed and is not used, avoiding a cycle.

## Mathlib search assessment

For each new node I ran LeanFinder with two different semantic phrasings, Loogle, grep through msearch.py and LeanSearch. All services returned answers. For coherence the hits were the individual TStructure.triangleLTGE/truncGEdeltaLT constructors and theorems about exact/homological functors, not the cross-category normalized triangle and cohomology tower assertions. I read Mathlib/CategoryTheory/Triangulated/TStructure/TruncLTGE.lean around lines 285–310, as well as the generic exact derived-functor interface. For simultaneous bounds the hits were TStructure.heart and isomorphism-closure properties or DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE, not finite-stage realization in a directed two-colimit. I read Mathlib/CategoryTheory/Triangulated/TStructure/Heart.lean around lines 43–54. The matching literal queries and returned hit names are recorded in the new node fields and searches.jsonl. Neither node is an exact match or one-line specialization of the hits. The item's old search record already covers the composite theorem; the additional exploratory finite-free query found no replacement for the item.

## Review by NI

I read the released repair and return entry, the item and its nine old steps, all statements cited in the new five-step assembly, the chapter and perverse unit, and the main-20261015 smooth-pullback node. I read Bhatt–Scholze PDF pp. 60–62, especially 6.8.11(3) and 6.8.14, and BBD PDF pp. 24–25 and 30–32 (printed pp. 23–24 and 29–31), especially 1.1.9/1.1.10 and 1.3.3. BS supports the coefficient-category setting; BBD supplies uniqueness of normalized truncations and the full triangle. Neither source supplies all literal raw-pair coherence equations; proof_origin remains agent. The main blueprint smooth-pullback file currently contains its statement rather than the old prose proof; the from.place records the inherited ordinary-cohomology allocation, not a claim that the current file prints this proof.

Step 1: lem-cbc-compactification-geometry-fibre-bound explicitly passes finite Noetherian affine covers, finite topological dimension and invertibility from Spec k to X. The field spectrum satisfies its hypotheses. lem-weil-finite-free-completed-scalar-comparison explicitly says S is finite free and that ordinary derived tensor is the completed scalar functor, already derived complete. lem-pc-kflat-resolution explicitly supplies a K-flat resolution for every sheaf complex, and lem-pur-derived-change-of-rings explicitly computes the tensor on it. I added the resolution-existence citation on final self-review rather than leaving its existence implicit. The finite direct-sum kernel/image/quotient calculation is written in the step itself, not assumed from a flatness definition. The constructible-transport statement is about the exact bounded-complete category with compatible etale witnesses that the item uses, and the integral-tstructure statement identifies its halves by ambient cohomology vanishing. I verified these are actual statements, not constructions hidden in proofs. No levelwise truncation or Tor-compatibility is invoked.

Step 2: prop-weil-localized-tstructure states exactly that both rational halves are isomorphism closures of integral images. prop-weil-pbc-scalar-extension states that its functor is the rationalization of integral completed extension and supplies exact shift-compatible associators. Thus the finite rational t-exactness hypothesis of the new coherence node follows. For the coherence node I checked the boundary equation types: both sides map T(tau>=r+1 K) to tau<=r(TK)[1]. T's source boundary is followed by its specified shift comparison and the shifted upper comparison. Its normalized cohomology lives in degree zero, with the [r] shift included. These are old steps 4–5 as a separate generic statement, not an assumption of the item as a whole.

Step 3: def-weil-finite-subextension-directed-set states nonemptiness, directedness via composita and finite extension of an included field. Its index is a set in the fixed larger universe. The literal finite-stage-pair definition gives exactly the Hom colimit and transport required by lem-pod-directed-pair-bounded-tstructure. I checked the latter statement, including its full conclusion about representative independence and triangles. The common-stage-cones definition identifies distinguished triangles with stage images; thm-weil-pbc-verdier-axioms supplies triangulatedness and exact j_E with exact scalar identifications. The finite stages are bounded by the localized theorem already used; step 2 gives t-exact transitions. This is a specialization of the existing generic node, not a second new duplicate.

Step 4: step 3's half description makes j_E t-exact, while the cited Verdier theorem makes it exact. The single-functor and exact-natural-transformation clauses in the new coherence statement therefore apply to j_E and j_LT_{L/E} isomorphic to j_E, with their specified shift data. The composed truncations and [r] shift yield the displayed degree-zero cohomology object. No cohomology sheaf is incorrectly substituted for an unshifted object of degree r.

Step 5: prop-weil-pbc-common-stage-calculus explicitly realizes every finite diagram of objects, maps, composites and equalities. The new simultaneous-bound statement uses that hypothesis to realize both isomorphisms and both inverse equations, so the lifts really are isomorphisms at the enlarged stage. Transition t-exactness then transfers upper and lower membership separately. For the new node's self-contained statement I checked the empty finite list, conflicting bounds, identical stages, and two witnesses initially at different stages. The heart conclusion uses H^0 on the resulting stage-heart object; it assumes no faithfulness or reflection. Applying it at bounds zero gives exactly the last clause of the item.

I checked delivery-errors B1–B10: new nodes are statement-only and self-contained, have actual definition dependencies, TeX is escaped once, sources are present, every recorded search actually ran, no leaf is falsely claimed, blueprint origins/via/same_as are filled, and no unfinished Lean theorem is attached. I checked C1–C8 against the cited statements: all non-elementary inputs are named, all ids are existing or new, and generic off-unit tools are declared only in split_report.tool_uses. The maintainer-owned tool_uses field is not enlarged. Cited texts were copied verbatim into citations.json after this reading. The D checks use the two strictly smaller arguments and the existing pair lemma; this is an assembly, not relabelling the entire item. E checks included X empty, E=L, a geometric point, non-flat integral cohomology, ramified L/E, and nonfaithful stage inclusions. Finite freeness is used for bounds even when cohomology is not flat. Identity and associator equations keep the specified scalar shift data. None of the new item steps exceeds 2000 characters; the total is below 3000.

## Remaining work

Stage 1 only: the two new statement-only tasks and the reused directed-pair task await their own splits/proofs. This is the explicit purpose of the human's re-split order; no Lean completion is claimed. No tool or launcher file was edited, and no other agent was started.

## Argument allocation and verbatim proof handoff

Old steps 1–3 stay in assembly steps 1–2 through the same completed finite-free and localization interfaces. Old steps 4–5 are the proof brief for lem-per-texact-system-triangle-coherence. Old steps 6–8 are assigned to existing lem-pod-directed-pair-bounded-tstructure, with old step 8's cohomology consequence assembled through the coherence node. Old step 9 is the proof brief for lem-per-directed-pair-simultaneous-bounds. This preserves the proof content while allowing the distinct outstanding arguments to be worked on separately.

### Original step 1

The spectrum of the field $k$ has a single point and a finite affine cover by a Noetherian ring. Apply [lem-cbc-compactification-geometry-fibre-bound] to $X\to\operatorname{Spec}k$: $X$ is Noetherian and finite-dimensional, and $\ell$ remains a unit. Thus the integral and localized bounded t-structures [prop-weil-pbc-integral-tstructure, prop-weil-localized-tstructure] apply at every finite coefficient field. Write $Q_E$ for localization and $C_{L/E}$ for integral change of completed coefficient rings. The construction of [prop-weil-pbc-scalar-extension] gives $T_{L/E}Q_E\cong Q_LC_{L/E}$; these are raw rationalizations throughout.

Cited interfaces: lem-cbc-compactification-geometry-fibre-bound, prop-weil-pbc-integral-tstructure, prop-weil-localized-tstructure, prop-weil-pbc-scalar-extension.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Propositions 6.8.11(3), 6.8.14(2); applicability to the completed finite-stage categories.

### Original step 2

Put $R=B_{E,X}$ and $S=B_{L,X}$. By [lem-weil-finite-free-completed-scalar-comparison], $S$ is finite free as an $R$-module, and $C_{L/E}K=K\otimes_R^LS$ is already derived complete. Choose an $R$-basis of $S$, of size $d=[L:E]$, only for this calculation. For a K-flat resolution $P\to K$, restriction of $P\otimes_RS$ is the complex $P^{\oplus d}$, with componentwise differential. Kernels, images and quotients of this finite direct sum are the corresponding direct sums; hence $\mathcal H^i(P\otimes_RS)$, after restriction, is $\mathcal H^i(K)^{\oplus d}$. Restriction forgets scalar action and detects zero sheaves. Consequently $C_{L/E}$ preserves both ambient cohomological bounds. It preserves the constructible subcategories with their compatible etale-origin witnesses by [lem-weil-pbc-finite-free-constructible-scalar-transport]. By [prop-weil-pbc-integral-tstructure] it therefore preserves both integral halves. No levelwise truncation or Tor-compatibility assertion is used.

Cited interfaces: lem-weil-finite-free-completed-scalar-comparison, lem-pur-derived-change-of-rings, lem-weil-pbc-finite-free-constructible-scalar-transport, prop-weil-pbc-integral-tstructure.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.8.11(3); finite-free change of completed coefficient rings and the cohomological bounds.

### Original step 3

Every object of a rational half is isomorphic to $Q_EK$ for an integral object $K$ in that half [prop-weil-localized-tstructure]. Apply step 2 and $T_{L/E}Q_E\cong Q_LC_{L/E}$ [prop-weil-pbc-scalar-extension]. Its image lies in the same rational half; shifts give this for every cutoff. This proves t-exactness, rather than merely exactness as a triangulated functor. Apply [lem-pod-texact-truncation-comparison] to obtain $c^-_{L/E,r}:T_{L/E}\tau_E^{\le r}\cong\tau_L^{\le r}T_{L/E}$ and $c^+_{L/E,r}:T_{L/E}\tau_E^{\ge r}\cong\tau_L^{\ge r}T_{L/E}$, characterized respectively by $\iota c^-=T(\iota)$ and $c^+T(\pi)=\pi$. This also gives their naturality in $K$.

Cited interfaces: prop-weil-localized-tstructure, prop-weil-pbc-scalar-extension, lem-pod-texact-truncation-comparison.

Source: literature/bbd-faisceaux-pervers_Asterisque-100-1982.pdf; Proposition 1.3.3(i),(ii), pp. 29–30; normalized comparison for a t-exact exact functor.

### Original step 4

For $E\subset L\subset M$, let $a:T_{M/L}T_{L/E}\cong T_{M/E}$ be the specified associator. The natural-transformation and composition clauses of [lem-pod-texact-truncation-comparison] give, for either truncation $\tau$,
$$c_{M/E,K}\,a_{\tau K}=\tau(a_K)\,c_{M/L,T_{L/E}K}\,T_{M/L}(c_{L/E,K}).$$
The identity comparison is the identity since $T_{E/E}=\operatorname{id}$. These equations use exactly the associator of [prop-weil-pbc-scalar-extension]. Define the cohomology comparison by composing the upper and lower comparisons for $(\tau^{\ge r}\tau^{\le r}K)[r]$, followed by the iterated scalar shift comparison. This is the degree-zero cohomology object $\mathcal H^rK$ (the ambient sheaf when an integral representative is used) [def-weil-derived-cohomology-sheaves, prop-weil-localized-tstructure]. Substitution of the displayed equations and the associator/shift equations gives the identical identity and composition equations for $\mathcal H^r$.

Cited interfaces: lem-pod-texact-truncation-comparison, prop-weil-pbc-scalar-extension, def-weil-derived-cohomology-sheaves, prop-weil-localized-tstructure.

Source: literature/bbd-faisceaux-pervers_Asterisque-100-1982.pdf; Proposition 1.3.3 and definition 1.3.16; uniqueness and composition of normalized comparisons.

### Original step 5

The comparisons identify the complete truncation triangles, including the third arrow. Indeed, apply $T_{L/E}$ to the finite-stage triangle at cutoff $r$, using its specified shift comparison [prop-weil-pbc-scalar-extension]. Its first term has bound $\le r$ and its third term bound $\ge r+1$. The comparison equations in step 3 commute with the first two arrows to the standard truncation triangle of $T_{L/E}K$. For the first term $A$ of the source triangle and third term $B'$ of the target, $A[1]$ has bound $\le r-1$, so $\operatorname{Hom}(A[1],B')=0$ by [def-weil-t-structure]. Clause (2) of [lem-weil-pbc-triangle-morphism-extension] now says that these prescribed first and third components, with middle component the identity, form a morphism of triangles: the boundary square commutes as well. The same uniqueness applies to cutoff-map diagrams; their finite-stage equations follow from the characterizing truncation maps, and remain valid under scalar extension.

Cited interfaces: prop-weil-pbc-scalar-extension, prop-weil-localized-tstructure, def-weil-t-structure, lem-weil-pbc-triangle-morphism-extension.

Source: literature/bbd-faisceaux-pervers_Asterisque-100-1982.pdf; Proposition 1.3.3(ii), pp. 29–30; Proposition 1.1.9 and Corollary 1.1.10(ii), pp. 23–24.

### Original step 6

In the pair category [def-weil-pbc-finite-stage-pair-category], set the halves at cutoff $r$ to be the isomorphism closures of $(E,K)$ with $K\in D_E^{\le r}$ or $D_E^{\ge r}$, respectively. These classes have the required shift inclusions by their finite-stage counterparts and the pair shift [prop-weil-pbc-common-stage-calculus]. For orthogonality choose presentations of an upper object and a lower object with cutoffs $r$ and $r+1$. After conjugating by their chosen isomorphisms, any map is $[M,u]$ between their scalar extensions. Step 3 places its endpoints in the corresponding halves at $M$, so $u=0$ by finite-stage orthogonality [def-weil-t-structure, prop-weil-localized-tstructure]. Thus the original map is zero. Each $(E,K)$ has the image of its finite-stage truncation triangle, distinguished because $j_E$ is exact [thm-weil-pbc-verdier-axioms]. This supplies the triangle axiom. The two finite-stage bounds of $K$ give two bounds of $(E,K)$, proving boundedness. Thus these halves form the asserted bounded t-structure.

Cited interfaces: def-weil-pbc-finite-stage-pair-category, prop-weil-pbc-common-stage-calculus, def-weil-t-structure, prop-weil-localized-tstructure, thm-weil-pbc-verdier-axioms.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Propositions 6.8.11(3) and 6.8.14(1),(2); explicit common-stage verification of t-structure axioms.

### Original step 7

Here is the actual descent formula; it does not apply an exact-functor descent assertion to truncation, which is generally not triangulated-exact. For either truncation put $\tau(E,K)=(E,\tau_EK)$. For $f=[M,u]:(E,K)\to(F,L)$ define
$$\tau(f)=[M,c_{M/F,L}^{-1}\,\tau_M(u)\,c_{M/E,K}].$$
If $M\subset N$, the associator equation of step 4 and naturality of $c_{N/M}$ show that transporting the displayed representative to $N$ gives exactly
$$c_{N/F,L}^{-1}\,\tau_N(a_{N,M,F,L}\,T_{N/M}(u)\,a_{N,M,E,K}^{-1})\,c_{N/E,K}.$$
The expression inside $\tau_N$ is $u_N$ by the pair-category definition. Thus two equivalent representatives give equivalent images. For composition, put both arrows at one stage [prop-weil-pbc-common-stage-calculus]; the adjacent factors $c_{M/F,L}$ and $c_{M/F,L}^{-1}$ cancel, and $\tau_M(vu)=\tau_M(v)\tau_M(u)$. The identity formula follows from $c_{E/E}=1$. These calculations prove that both truncations are functors with the stated arrow formulas.

Cited interfaces: def-weil-pbc-finite-stage-pair-category, prop-weil-pbc-common-stage-calculus.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.8.14; explicit conjugation and refinement calculation in the pair category.

### Original step 8

Represent the upper counit on $(E,K)$ by $[E,\iota_{E,K}]$ and the lower unit by $[E,\pi_{E,K}]$. Their naturality for $[M,u]$ follows by substituting step 7 and the two characterizing equations of step 3. All equations between truncation maps are checked at a common finite stage using [prop-weil-pbc-common-stage-calculus], where they are the ordinary finite-stage equations [prop-weil-localized-tstructure, def-weil-t-structure]. Step 5 handles the shifted third arrow of the distinguished truncation triangles, and [thm-weil-pbc-verdier-axioms] sends each such finite-stage triangle to a distinguished pair-category triangle. These are truncation triangles for the halves proved in step 6. Their uniqueness follows from [lem-weil-pbc-triangle-morphism-extension](2), since the same upper/lower orthogonality gives its vanishing hypothesis in the pair category. Consequently the constructed functors are the canonical truncations of that t-structure, including all their canonical maps. Applying their composition and the pair shift gives naturally $\mathcal H^r(E,K)\cong(E,\mathcal H_E^rK)$.

Cited interfaces: prop-weil-pbc-common-stage-calculus, prop-weil-localized-tstructure, def-weil-t-structure, thm-weil-pbc-verdier-axioms, lem-weil-pbc-triangle-morphism-extension.

Source: literature/bbd-faisceaux-pervers_Asterisque-100-1982.pdf; Proposition 1.3.3(i),(ii), pp. 29–30; common-stage descent of the units, counits and full triangles.

### Original step 9

It remains to identify the heart; the witnesses for its two halves need not initially be at the same stage. Let $Z=(E,K)$ lie in both halves. Choose isomorphisms from $Z$ to a pair $(F,A)$ in the upper half and to a pair $(G,B)$ in the lower half. Include their inverses and both inverse equations in one finite diagram. By [prop-weil-pbc-common-stage-calculus] there is a finite $N\supset E,F,G$ where these are actual isomorphisms, so $T_{N/E}K\cong T_{N/F}A$ and $T_{N/E}K\cong T_{N/G}B$. Step 3 places the right-hand sides in the upper and lower finite-stage halves respectively. Hence $T_{N/E}K$ belongs to the finite-stage heart. Its two degree-zero truncation maps are isomorphisms, giving $T_{N/E}K\cong\mathcal H_N^0(T_{N/E}K)$ [def-weil-t-structure, prop-weil-localized-tstructure]. The canonical identification $j_NT_{N/E}\cong j_E$ [thm-weil-pbc-verdier-axioms] now proves the required isomorphism for $Z$ after this one finite enlargement. Conversely every finite-stage heart object belongs to both pair halves. Therefore the pair heart is exactly the isomorphism closure of finite-stage hearts. No reflection of bounds by scalar extension or faithfulness of $j_E$ was assumed.

Cited interfaces: prop-weil-pbc-common-stage-calculus, def-weil-t-structure, prop-weil-localized-tstructure, thm-weil-pbc-verdier-axioms.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Propositions 6.8.11(3), 6.8.14(1),(2); simultaneous realization of the two heart witnesses.

