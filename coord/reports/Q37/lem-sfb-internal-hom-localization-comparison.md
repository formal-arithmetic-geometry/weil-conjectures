# Worker report — Q37

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-internal-hom-localization-comparison.json`: existing statement node re-split; statement and Lean record unchanged; four assembly steps, 2240 characters in total.
- `dag/nodes/sec-six-functors-basics/lem-sfb-derived-scalar-localization-reflection.json`: new statement, unsplit; no Mathlib match for the ringed-site derived reflection with normalized maps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-kinjective-hom-scalar-telescope.json`: new statement, unsplit; no Mathlib match for the resolution-induced versus scalar tower with every colimit leg.
- `citations.json`: one exact statement quotation for every citation in every assembly step.

Both new nodes contain statements only: empty proof and proof_deps, null proof_origin. Neither states a clause of the parent: reflection has no internal Hom or continuity, while the Hom-telescope statement has no change of rings, boundedness, continuity, or evaluation-transpose map. They are independent tasks, and neither depends on the other or on the parent. The old elementary truncation and the actual use of continuity and evaluation normalization remain the parent's argument.

## Attachments

None. I searched `lean/WeilConjectures/` by the blueprint tag and by internal-Hom/localization notions. The attached theorem `CategoryTheory.internalHom_localization_comparison` is in `lean/Sheaf/Algebra/Homology/InternalHomLocalizationComparison.lean:158`; its final body is `sorry`. It cannot supply ATTACH. Its definitions fix precisely the non-linear functorial resolution and complex-level continuity comparison under discussion. No Lean was changed or compiled.

## WANTED

None. The Bhatt–Scholze PDF and the relevant Stacks source files are present.

## Return repaired and comparison with current state

The sandbox initially contained only dispatcher brief files, no node, report, or searches. I copied the live reviewed node and retained its exact seven-step proof in this report and in retained-proof.json. The current live node includes the maintainer's correction of the non-linear K-injective resolution issue in old step 5, as well as the stage-2 statement attachment; both were read. The copy therefore starts from the repaired returned head available on current main, rather than from an obsolete pre-correction proof. No statement, Lean record, import flag or creation record was changed.

The return requires spreading the 5691-character argument over independent statement-only nodes while keeping the parent below 3000 characters. Old steps 2 and 3 are now the reflection task, and the non-elementary part of old step 5 is the scalar-Hom telescope task. The four assembly steps total 2240 characters; no individual assembly step exceeds 2000. The entire old proof is reproduced below, not shortened or discarded. The main mathematical correction to retain is that I(s) need not be literally scalar multiplication. The new telescope task explicitly permits a non-R-linear resolution functor and requires a derived isomorphism compatible with every leg, not just an abstract isomorphism of the endpoints.

## Proof coverage and worker handoff

- Old step 1 stays as assembly step 1: good quotient truncation produces a common termwise lower bound.
- Old step 2 belongs to the reflection task: exact E and restriction give termwise derived functors, comparison with the K-flat derived tensor formula, and the normalized unit.
- Old step 3 belongs to the reflection task: local balancing proves multiplication is invertible, then the triangle identities give the inverse formula for the unit-precomposition bijection and UF(eta)=eta_UF.
- Old step 4 stays as assembly step 2, using the existing all-complex telescope theorem with coefficient ring Z[T], T mapped to s. Exact filtered colimits preserve quasi-isomorphisms by the kernel/image formula, without boundedness.
- Old step 5 through the isomorphism of two colimits belongs to the Hom-telescope task: cancel Q(i) to compare I(s) with scalar multiplication, use K-injectivity to obtain a homotopy, postcompose to the Hom complex, and use the cone of 1 minus shift. The explicit cone isomorphism, cokernel quasi-isomorphism, contractible kernel and all-leg compatibility must all be supplied by that worker. These are preserved verbatim below. The remaining application of the parent's assumed continuity to (P,s) is assembly step 3.
- Old step 6 stays as assembly step 4: transpose extended evaluation to obtain the unit equation, then apply the reflection task's uniqueness into an object isomorphic to UN. This is equality of actual derived arrows, not an inference that individual telescope legs determine arbitrary derived maps.
- Old step 7 stays as assembly step 4: use the existing scalar-Hom node's conservativity and the canonical evaluation construction to finish invertibility and naturality.

The existing lemma `lem-kun-complex-colimit-hocolim` is useful to the future telescope worker: it already states that cone(1-shift) maps quasi-isomorphically to the termwise colimit, with the canonical projection. It does not compare the two resolution-induced and scalar towers. `lem-sc-kinjective-quasi-iso-comparison` gives Hom_K to Hom_D bijective into a K-injective object, and `lem-pur-kinjective-cone-contractible` gives contractibility of cone(identity). These previously cited facts remain available to that worker; they were not replaced by a claim of strict resolution linearity.

## Searches

Before naming either node I searched all `dag/nodes/` by localization/counit/reflectivity and Hom/homotopy/telescope keywords, read the existing normalized scalar-Hom adjunction, ordinary and derived coefficient adjunction, scalar-localization exactness, complex-colimit telescope, K-injective comparison, and cone-identity statements, and searched the whole imported blueprint with `blueprint_refs.py search` for telescope, counit, homotopic, scalar localization, localization counit, and scalar tower. The ancestor command returns None: this is an agent-created chain with no imported blueprint ancestor. The new from.node fields preserve that null ancestor, and via starts with the parent followed by its existing via chain; from.place records exactly the old proof argument served. same_as is empty.

Each new node records six actual msearch.py queries: LeanSearch, Loogle, two LeanFinder phrasings, and two greps. All completed successfully; searches.jsonl contains their original results. Reflection searches found ordinary ModuleCat change-of-rings counit formulas, sheafification adjunctions, the generic localization-of-adjunction construction and derived exact functor factorization. I read the presheaf change-of-rings source: these do not establish invertibility of multiplication after sheaf localization and its derived realization. Telescope searches found ordinary injective-resolution functors, sheaf colimit existence, the homotopy invariance of Q and the individual K-injective and mapping-cone lemmas. I read `DerivedCategory/KInjective.lean:41` and `HomotopyCategory/Pretriangulated.lean:93,103,110`: none states the entire two-tower comparison. Neither new node is a one-line specialization of a returned declaration. The existing parent's searches were retained unchanged; its statement has not changed.

## Review by Q37

I read Bhatt–Scholze Lemma 6.8.12, Proposition 6.8.14(2), and Remark 6.8.15 on printed pages 61–62. They motivate localization of constructible coefficients but do not state this conditional internal-sheaf theorem. The parent remains honestly agent-authored, and I have not replaced its displayed sequential internal-Hom assumption by the paper's global Hom/direct-sum lemma. I read Stacks sites-modules.tex, lemma-flatness-sheafification (03ET) and lemma-limits-colimits (03DB); sites-cohomology.tex, lemma-adjoint (07A6) and section-internal-hom (08J7), including its Hom-complex construction; and derived.tex, lemma-K-injective (070I). The reflection and scalar-telescope statements are agent extractions of the already reviewed proof, not claimed verbatim theorems in those sources. Reflection's recorded source locates its localization-flatness input; derived adjunction and its normalization are supplied by the existing coefficient-adjunction statement. Telescope's recorded source locates the K-injective detection of homotopy; the cokernel/cone argument remains the separate work of the new task. No SGA route is used.

For assembly step 1 I checked the statement of def-weil-abstract-derived-category: its kernel/image cohomology and quasi-isomorphism definitions are exactly what the explicit quotient truncation uses. At degree a the kernel of the induced differential from coker(d^(a-1)) is H^a(M); below a both cohomologies vanish by the hypothesis on L. This is an elementary computation rather than a new lemma.

For step 2 I read the new reflection statement, including exactness of E and U0, comparison on arbitrary complexes, the normalized unit and the Hom-bijection. I also opened lem-weil-pbc-scalar-localization-complex-colimit: it explicitly allows every complex and gives the nth leg eta followed by the inverse nth scalar power. Its coefficient ring can be Z[T] acting via the specified global section. Exactness and unit normalization required there are in the reflection statement. The elementary kernel/image argument justifies preservation of quasi-isomorphisms in the chosen complex models.

For step 3 I read the new telescope statement: it introduces both towers using exactly the same fixed functorial K-injective resolution as def-pur-derived-internal-hom and asserts compatibility at every leg. The definition node explicitly defines internal Hom by Hom(A,I(P)), is functorial, and inverts quasi-isomorphisms. Thus the only boundedness used is that of the input tower (P,s), proved in step 1. The Hom complex itself can be unbounded. Applying precisely the parent's continuity assumption and preserving the zeroth leg gives beta eta = H(K,eta_L). No R-linearity of I is assumed, and a choice of telescope isomorphism is permitted: the next step identifies the resulting beta by unit uniqueness.

For step 4 I reopened lem-sfb-dc-hom-scalar-adjunction: it states the evaluation-normalized isomorphism U H_S(FK,N) = H_R(K,UN), natural in both inputs, and explicitly states conservativity of U. Transposing alpha U chi after eta gives the original evaluation followed by eta_L, as in the old proof. The reflection statement's bijection applies with A=H_R(K,L), N=H_S(FK,FL); transport along alpha permits that precise target. It therefore identifies the actual map with beta. Two isomorphisms alpha and beta imply U chi invertible; conservativity gives chi invertible. The final naturality follows from the actual functorial evaluation/transpose construction, without requiring a functorial choice of homotopy for I(s).

Both new statements introduce the site, coefficient sheaf, scalar, complexes, derived categories and all their maps. Each used notion has a definition or existing construction dependency. Reflection has no continuity or internal-Hom conclusion. Telescope has no localized coefficient ring or comparison chi, and demands no lower bound. I checked s=1 (both towers have identity transition), s=0 and nilpotent s (the localized category is zero and the scalar colimit is zero; the other telescope must be acyclic, not necessarily literally zero), and zero complexes. On a one-object site with R=Z and s=p, reflection is the ordinary localization counit and telescope compares the two chain models before inverting p. The empty site gives only zero objects and satisfies both statements. Nothing assumes enough points, perfection, constructibility, or completeness. These checks preserve all hypotheses of the original parent.

I checked delivery-errors B–E against the written files: the new statements carry no proof sketches, have complete objects and definition citations, actual recorded searches with a second phrasing, and filled blueprint references; no formula relies on a Stacks tag for its meaning. Existing same-tag candidates are distinguished individually below. Every non-elementary assembly fact is a cited statement and has a verbatim quotation in citations.json. The new nodes have no parent dependency, hence introduce no cycle. The parent is an assembly of two different intermediate arguments with its original continuity and canonical-map reasoning still present, not a relabelled conclusion. No statement dispute was found and the parent statement was preserved exactly.

## Not duplicates

lem-sfb-derived-scalar-localization-reflection vs lem-pc-sites-modules-sheafification-flat: existing statement only transports flatness through sheafification; the new statement proves the derived localization counit and unit-precomposition bijection.

lem-sfb-derived-scalar-localization-reflection vs lem-pc-sites-modules-functorial-flat-cover: existing statement constructs a functorial flat cover, not the counit of scalar localization.

lem-sfb-derived-scalar-localization-reflection vs lem-sfb-constant-module-flat: existing statement proves flatness of constant module realizations; the new statement concerns a section localization of an arbitrary ring sheaf and derived reflection.

lem-sfb-derived-scalar-localization-reflection vs lem-weil-pbc-free-sheaf-flat: existing statement proves flatness of representable free sheaves; the new statement identifies a localization counit and its universal mapping property.

lem-sfb-derived-scalar-localization-reflection vs lem-weil-pbc-scalar-localization-sheaf-exact: existing statement supplies exactness of ordinary E only; the new task additionally identifies its derived realization, proves its counit invertible and gives the normalized unit bijection.

lem-sfb-kinjective-hom-scalar-telescope vs lem-sbc-unbounded-exact-adjunction-square: existing statement compares inverse-system evaluation and derived site adjunctions; it does not compare two direct scalar telescopes on one internal Hom complex.

lem-sfb-kinjective-hom-scalar-telescope vs lem-sbc-ambient-operations-scalar-linearity: existing statement gives derived scalar-linearity of scheme pullback/pushforward; it says nothing about the non-linear chosen resolution functor or complex-level colimit legs.

lem-sfb-kinjective-hom-scalar-telescope vs lem-trf-proetale-unit-leray-chain-formula: existing statement computes the global-sections image of a derived site unit and Leray map; the new statement is a comparison of internal-Hom scalar telescopes.

lem-sfb-kinjective-hom-scalar-telescope vs lem-sc-p1-rhom-injective-cocycle-bijective: existing statement detects bijectivity of a map on a fixed cohomology group through injective cocycles; the new statement compares unbounded sheaf Hom-complex colimits.

lem-sfb-kinjective-hom-scalar-telescope vs lem-sc-p1-rhom-hom-derived-roof-shift-injective-cocycle: existing statement concerns the shifted roof formula on an individual injective cocycle; it has no scalar telescopes.

lem-sfb-kinjective-hom-scalar-telescope vs lem-sc-p1-rhom-hom-derived-roof: existing statement constructs the cohomology-to-derived-Hom roof isomorphism for Hom(M,-); the new statement compares scalar transitions before and after K-injective resolution.

lem-sfb-kinjective-hom-scalar-telescope vs lem-sc-p1-rhom-natural-cocycle-map: existing statement constructs a cohomology-to-derived-Hom map natural in bounded-below objects; the new statement concerns colimits of unbounded internal sheaf Hom complexes.

lem-sfb-kinjective-hom-scalar-telescope vs lem-sc-p1-rhom-hom-derived-roof-shift: existing statement proves compatibility of the roof isomorphism with shifting the input; no scalar or sequential colimit appears.

lem-sfb-kinjective-hom-scalar-telescope vs lem-weil-pbc-flat-restriction-derived-mate: existing statement identifies a normalized derived mate under flat site restriction; it does not identify resolution-induced scalar endomorphisms or their telescopes.

lem-sfb-kinjective-hom-scalar-telescope vs lem-weil-pbc-derived-exchange-module-termwise: existing statement represents an etale base-change mate on K-injective complexes; the new statement has no cartesian square or base-change map.

lem-sfb-kinjective-hom-scalar-telescope vs lem-weil-pbc-sequential-tower-evaluation-full: existing statement lifts compatible derived maps of inverse systems, without uniqueness; the new statement gives a specified all-leg comparison of termwise direct colimits on internal Hom.

lem-sfb-kinjective-hom-scalar-telescope vs lem-weil-pbc-kinjective-hom-derived: existing statement is Hom_K to Hom_D bijective into a K-injective target; it supplies an input to, but not the Hom-complex/telescope conclusion of, the new task.

lem-sfb-kinjective-hom-scalar-telescope vs lem-weil-pbc-free-sheaf-derived-sections: existing statement identifies derived Hom from a free constant sheaf with global cohomology; it has no resolution-induced scalar tower comparison.

lem-sfb-kinjective-hom-scalar-telescope vs lem-weil-pbc-derived-exchange-unbounded-transport: existing statement extends a bounded etale exchange representative equation to unbounded K-injective representatives; it has no scalar telescopes.

lem-sfb-kinjective-hom-scalar-telescope vs lem-weil-pbc-derived-exchange-bounded-comparison: existing statement is the bounded source case of a normalized etale exchange equation; the new statement compares scalar Hom telescopes without a boundedness hypothesis.

lem-sfb-kinjective-hom-scalar-telescope vs lem-sf-exact-localization-derived-triangle: existing statement constructs a derived localization triangle from a short exact sequence of functors; it does not compare scalar towers on a Hom complex.

lem-sfb-kinjective-hom-scalar-telescope vs lem-cbc-kinjective-derived-mapping-complex: existing statement compares enhanced global mapping complexes in a functor category; the new statement concerns ordinary internal sheaf Hom and termwise sequential colimits.

lem-sfb-kinjective-hom-scalar-telescope vs lem-sp-exact-pullback-derived-adjunction: existing statement constructs a derived pullback adjunction with representative transpose normalization; it says nothing about non-linear resolution scalar transitions or their colimits.

lem-sfb-kinjective-hom-scalar-telescope vs lem-sp-levelwise-kinjective-tower-image: existing statement computes a derived functor on an inverse tower whose evaluations are K-injective; it does not compare I(s) with scalar multiplication in a direct telescope.

lem-sfb-kinjective-hom-scalar-telescope vs lem-pur-derived-injective-boundary: existing statement constructs connecting maps for exact rows on injective objects and identifies snake maps; it has no scalar-telescope conclusion.

lem-sfb-kinjective-hom-scalar-telescope vs lem-pur-support-pair-chain-coherence: existing statement transports chain homotopies through support-kernel diagrams; it does not compare internal-Hom scalar colimits.

lem-sfb-kinjective-hom-scalar-telescope vs lem-weil-pbc-kinjective-pullback-abutment: existing statement compares the cohomology of an inverse-image unit chain map to its Leray description; it has no direct telescope.

lem-sfb-kinjective-hom-scalar-telescope vs lem-weil-pbc-kinjective-unit-leray: existing statement identifies a global-sections unit and Leray composition on K-injective complexes; it does not identify the two Hom scalar colimits.

lem-sfb-derived-scalar-localization-reflection vs lem-weil-pbc-integral-localization-counit: existing statement concerns ordinary integral-to-rational modules on schemes; the new task is unbounded derived reflection for a section of any commutative ring sheaf, with normalized unit and counit.

lem-sfb-derived-scalar-localization-reflection vs lem-pur-sheaf-ring-derived-coefficient-adjunction: the existing adjunction allows any coefficient map and does not assert an invertible counit; the new localization-specific multiplication assertion is additional work.

lem-sfb-kinjective-hom-scalar-telescope vs lem-kun-complex-colimit-hocolim: the existing statement identifies the cone of 1-shift for a single sequence with its colimit; the new task compares the two different endomorphisms arising from a non-linear K-injective resolution.

lem-sfb-kinjective-hom-scalar-telescope vs lem-sc-kinjective-quasi-iso-comparison: the existing Mathlib leaf detects equality up to homotopy; the Hom complex, scalar action and all-leg colimit comparison are additional work.

lem-sfb-derived-scalar-localization-reflection vs lem-sfb-internal-hom-localization-comparison: the new lemma contains no internal Hom or continuity hypothesis and does not assert the parent's comparison; it carries only old steps 2–3.

lem-sfb-kinjective-hom-scalar-telescope vs lem-sfb-internal-hom-localization-comparison: the new lemma contains no localization of coefficients, continuity hypothesis or evaluation-transpose conclusion; it carries only the resolution/telescope portion of old step 5.

## Original argument retained verbatim

The following is the full current reviewed proof, including the maintainer's correction, to preserve every argument for the newly queued workers. These paragraphs are handoff material, not proof fields of the new unsplit nodes.

### Original step 1

Choose $a$ with $H^i(L)=0$ for $i<a$ and a complex $M$ representing $L$. Replace $M$ by $P$: put $P^i=0$ for $i<a$, $P^a=\operatorname{coker}(d_M^{a-1})$, and $P^i=M^i$ for $i>a$, with the induced differential. The quotient map $M\to P$ induces the identity on cohomology in degrees at least $a$ and maps zero to zero below $a$; it is a quasi-isomorphism. Thus the constant sequence $P\xrightarrow{s}P\xrightarrow{s}\cdots$ has one termwise lower bound, as required by the continuity hypothesis.

Cited nodes: def-weil-abstract-derived-category.

### Original step 2

Write $E(M)=S\otimes_R M$ and let $U_0$ be restriction of scalars. Scalar localization is exact by the cited exactness theorem; $U_0$ is exact by the cited coefficient adjunction. Applying them termwise gives $F:D(R)\to D(S)$ and $U:D(S)\to D(R)$. Identify $F$ with $S\otimes_R^{\mathbf L}-$: the K-flat formula for derived change of rings and exactness identify both on a resolution $Q\to M$, since $E(Q)\to E(M)$ is a quasi-isomorphism. The normalized derived coefficient adjunction gives $F\dashv U$, with unit $\eta_A:A\to UFA$ induced by $x\mapsto1\otimes x$.

Cited nodes: lem-weil-pbc-scalar-localization-sheaf-exact, lem-pur-sheaf-ring-coefficient-ordinary-adjunction, lem-pur-derived-change-of-rings, lem-pur-sheaf-ring-derived-coefficient-adjunction.

### Original step 3

For any complex $N$ of $S$-modules, multiplication $EU_0N\to N$, $b\otimes x\mapsto bx$, is inverse to $x\mapsto1\otimes x$: locally $s^{-n}\otimes x=1\otimes s^{-n}x$, by multiplying by the invertible $s^n$ and balancing. These equalities sheafify and commute with differentials. The normalized derived counit $\varepsilon_N:FUN\to N$ is therefore an isomorphism. Consequently precomposition with $\eta_A$ bijects maps $UFA\to UN$ with maps $A\to UN$: its inverse sends $h$ to $U\varepsilon_N\circ UF(h)$. To check uniqueness directly, $UF\eta_A=\eta_{UFA}$ since both are inverse to $U\varepsilon_{FA}$; naturality of $\eta$ and $U\varepsilon_N\circ\eta_{UN}=1$ give $q=U\varepsilon_N\circ UF(q\circ\eta_A)$ for every $q:UFA\to UN$.

Cited nodes: lem-pur-sheaf-ring-derived-coefficient-adjunction, def-weil-pbc-ringed-section-localization.

### Original step 4

Apply the complex-colimit theorem with coefficient ring $\mathbf Z[T]$, $t=T$, acting through the global section $s$. For every complex $B$, without a lower-bound assumption, it identifies the termwise colimit of $B\xrightarrow{s}B\to\cdots$ with $U_0E(B)$; its $n$th leg represents $U(s^{-n})\eta_{QB}$. Exactness of filtered colimits implies that they preserve quasi-isomorphisms (cohomology is kernel modulo image), so the same identifications hold for the functorial representatives stipulated in the statement. In particular they apply both to $P$ and to a representative of $H_R(K,L)$, even when that internal Hom is unbounded below.

Cited nodes: lem-weil-pbc-scalar-localization-complex-colimit, def-weil-abstract-derived-category.

### Original step 5

Represent $K$ by $\mathcal L$ and put $X=\mathcal Hom^\bullet(\mathcal L,I(P))$, the Hom-complex defining $H_R(K,L)$ with the fixed functorial K-injective resolution $i:P\to I(P)$. Applying $H_R(K,-)$ to the scalar tower on $P$ gives the tower $X\xrightarrow{t_1}X\to\cdots$ with $t_1=\mathcal Hom^\bullet(\mathcal L,I(s))$; the scalar tower on $X$ has $t_2=s$, and postcomposition by $s$ is multiplication by $s$ on every component, $s\varphi=s\circ\varphi$. The maps $I(s)$ and $s_{I(P)}$ satisfy $Q(I(s))Q(i)=Q(i)Q(s_P)=Q(s_{I(P)})Q(i)$ with $Q(i)$ invertible, so they agree in $D(R)$ and, $I(P)$ being K-injective, are homotopic by the cited bijection $\operatorname{Hom}_K\to\operatorname{Hom}_D$; postcomposing a homotopy $h$ gives $t_1-t_2=dh'+h'd$ on $X$. Each termwise sequential colimit is the cokernel of the termwise monomorphism $f_k=1-\sigma_{t_k}:\bigoplus_nX\to\bigoplus_nX$ ($\iota_n\mapsto\iota_n-\iota_{n+1}t_k$), with the $n$th leg induced by $\iota_n$. Since $f_1-f_2=dH+Hd$ for $H=-\sigma_{h'}$, the map $(x,y)\mapsto(x,y+Hx)$ is an isomorphism of mapping cones $\operatorname{cone}(f_1)\cong\operatorname{cone}(f_2)$ which is the identity on the second summand; and $(x,y)\mapsto[y]$, $\operatorname{cone}(f_k)\to\operatorname{coker}f_k$, is a quasi-isomorphism because its kernel is isomorphic to $\operatorname{cone}(1_{\bigoplus X})$, which is contractible. Hence the colimits of the two towers are isomorphic in $D(R)$ compatibly with every leg. Apply precisely the assumed sequential-continuity comparison to the bounded-below input tower $(P,s)$ of step 1, and step 4 to the tower $(X,s)$ and to $(P,s)$. This gives an isomorphism $\beta:UFH_R(K,L)\xrightarrow{\sim}H_R(K,UFL)$. Its composite with $\eta_{H_R(K,L)}$ is $H_R(K,\eta_L)$, because the continuity comparison is induced by evaluation, the leg-compatible isomorphism above preserves the zeroth leg, and the zeroth colimit leg is the unit. No lower bound on $H_R(K,L)$ has been used.

Cited nodes: def-pur-derived-internal-hom, def-weil-pbc-category-colimit, def-pur-kinjective-complex, lem-sc-kinjective-quasi-iso-comparison, lem-pur-kinjective-cone-contractible.

### Original step 6

Let $\chi:FH_R(K,L)\to H_S(FK,FL)$ be the canonical evaluation-transpose map in the statement, and let $\alpha:UH_S(FK,FL)\xrightarrow{\sim}H_R(K,UFL)$ be the cited evaluation-normalized scalar-Hom isomorphism. Their normalization gives $(\alpha\circ U\chi)\circ\eta_{H_R(K,L)}=H_R(K,\eta_L)$: transposing either side gives evaluation $K\otimes_R^{\mathbf L}H_R(K,L)\to L$ followed by $\eta_L$, since $\chi$ is the transpose of extended evaluation and $\alpha$ uses the scalar unit on $K$. The target is isomorphic via $\alpha$ to $UN$ for $N=H_S(FK,FL)$. The uniqueness proved in step 3 therefore gives $\alpha\circ U\chi=\beta$. This establishes equality of the actual derived maps, not just their values on the individual telescope legs.

Cited nodes: lem-sfb-dc-hom-scalar-adjunction, lem-pur-sheaf-ring-derived-coefficient-adjunction.

### Original step 7

Since $\alpha$ and $\beta$ are isomorphisms, so is $U\chi$. The conservativity assertion of the scalar-Hom adjunction node implies that $\chi$ is an isomorphism in $D(S)$. Step 6 also identifies its restriction with the asserted sequential-continuity isomorphism. Naturality in $L$ and contravariant naturality in $K$ (among objects satisfying the displayed continuity assumption) follow from the functorial evaluation map defining $\chi$ and the natural isomorphism $\alpha$; the representative and colimit choices do not alter this canonical map.

Cited nodes: lem-sfb-dc-hom-scalar-adjunction.

## Unfinished work

No part of the requested stage-1 repair remains unwritten. The proofs of the two new statements are deliberately queued as independent unsplit work. Required server dry-run and push results follow in the delivery tool output.
