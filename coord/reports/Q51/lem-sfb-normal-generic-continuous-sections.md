# Repair report: lem-sfb-normal-generic-continuous-sections

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-normal-generic-continuous-sections.json`: statement unchanged; five assembly steps, 1972 characters in total.
- `dag/nodes/sec-six-functors-basics/lem-sfb-normal-generic-chart-clopens.json`: statement, unsplit, no Mathlib match; normal affine chart geometry and generic idempotent/clopen lifting (old steps 1–2, 2132 characters of argument).
- `dag/nodes/sec-six-functors-basics/lem-sfb-normal-generic-component-comparison.json`: statement, unsplit, no Mathlib match; basis gluing and affine generic component comparison (old steps 3–4, 1637 characters).
- `dag/nodes/sec-six-functors-basics/lem-sfb-ultrametric-component-map-extension.json`: statement, unsplit, no Mathlib match; ultrametric separation, component factorization and the explicit inverse ring map (old steps 5–6, 1515 characters).
- `report.md` and `citations.json` contain the review, original arguments and six exact parent-step citation quotations. The `search-*.txt` files retain the actual search outputs and `searches.jsonl` retains the command's log; these are sandbox evidence, not extra DAG files.

## Attachments

None. Searches by the item tag, normal_generic_continuous, generic/clopen/component concepts in `lean/WeilConjectures/` found no declaration giving the item. The matching `AlgebraicGeometry.ProEtale.normal_generic_continuous_sections` in `lean/Sheaf/AlgebraicGeometry/NormalGenericContinuousSections.lean:81` ends with `sorry`. It is a signature to respect, not a completed proof. The existing upstream `Algebra.WeaklyEtale.isIntegrallyClosedIn_tensorProduct` at `WeilConjectures/RingTheory/ProEtale/WeakDimension.lean:563` supplies the algebraic ingredient already represented by lem-weil-pbc-weak-etale-integral-closure, not the whole chart lemma. Existing component lift declarations and the spectral clopen criterion also give only ingredients of the new nodes.

## Wanted sources

None. All sources used here are already present under literature/.

## What was wrong and what the repair changes

The return requires distribution of the 6662-character proof, not abbreviation. The supplied sandbox contained only dispatcher marker files, with no retained node, report or search log. I therefore copied the current shared-repository item, whose eight proof steps match all the return's step lengths exactly. I made no git command in the shared repository and no Lean, compiler or Lake call. The delivery tools handle comparison with current server main and the returned head in their own worktree.

The three new nodes carry self-contained statements, source places, blueprint references, logged searches, empty proof/proof_deps, null proof_origin and status unsplit. Their arguments are assigned in pairs of adjacent original steps and retained verbatim below; none is blurred into a claim that it is standard. Parent steps 1, 2 and 3 explicitly use their statements. Original step 7 stays as the naturality calculation in parent step 4, and original step 8 stays as the coefficient realization in parent step 5. The three extracted arguments have comparable sizes; no single new node states the original continuous-section theorem.

The parent's statement, all its hypotheses, both naturalities, empty objects, and the lack of completeness/local compactness assumptions are unchanged. Its original citations, historical searches and maintainer fields are preserved in the copied input; obsolete direct proof dependencies are replaced by the three new interfaces. The source route stays the normal generic/idempotent/component route; no SGA source is used.

## What could not be finished

No repair point remains mathematically open at the level of this split. The new statements are intentionally delivered without proofs so three workers can work independently. This is a stage-1 repair, not a claim of a completed Lean proof.

## Review by Q51

I read the current item, its actual Lean signature and sorry, the chapter record, the sk-thm-sf-ctf-stability unit and the main-20261015 direct-images blueprint node. The inherited blueprint chain ends at a null ancestor, and blueprint_refs ancestor confirms None. I retained that ancestor, prepended this item to each new node's via list, and supplied exact places referring to the returned argument and the same normal-monodromy application. This does not silently invent a new blueprint identity or alter the unit route. Searches of the full imported blueprint for generic clopen, normal generic, clopen, connected components, continuous functions, ultrametric and weakly etale found tools and coefficient definitions, not an existing node stating any of these three interfaces. A whole-DAG statement/title scan plus tag searches and the Lean concept searches gave the same conclusion. The nearby def-zl-generic-component-data is relative profinite site/scalar data, not generic-fibre restriction.

For the chart node I read Stacks more-algebra.tex, Tag 092W, lemma-normality-goes-up (statement and proof), and algebra.tex, Tag 00EE, lemma-disjoint-decomposition (statement and proof). Tag 092W assumes a normal domain, not merely an integral ring: the chart statement explicitly requires stalkwise normality, and the retained argument obtains normal R by lem-weil-pbc-affine-open-stalk-localization and lem-weil-pbc-normal-domain-of-local-normal. I opened both statements: they give precisely the localization/stalk identifications and the maximal-local criterion. I opened sk-lem-pe-weakly-etale-stability and def-weil-pbc-proetale-site: they justify restricting to W over V and identify weakly etale with flat plus flat diagonal. I opened def-weil-pbc-ind-etale-algebra: its ring-level equivalence really supplies flatness of B over R. I opened lem-weil-pbc-fibre-product-affine-spectra: its tensor product and projection formula are the ones used here. The localization identification is given by mutually inverse b tensor a/s and ab/s maps in the preserved text; it is not an unsupported localization comparison. I opened lem-trf-flat-module-torsionfree-domain, lem-weil-pbc-weak-etale-integral-closure and lem-weil-pbc-spec-clopen-idempotent: these state the injective multiplication, integral closure in B tensor k, and UNIQUE idempotent/clopen correspondence needed in the old step 2. The idempotent equation in B is justified by injectivity after integral closure, not by confusing a lift with an idempotent. These old proof ingredients belong to the future chart worker's argument and are preserved below, not concealed as dependencies of its statement-only node.

For the component comparison node I read Stacks topology.tex, Tag 0906, lemma-spectral-pi0, and the complete statement of lem-sfb-spectral-clopen-component-homeomorphism. Tag 0906 alone says components are profinite; it does not prove the comparison criterion. That criterion remains the existing node, to be used by the future worker after global clopen gluing. I also opened lem-weil-pbc-affine-morphism-permanence (base change and affine-source conclusion), lem-weil-pbc-affine-scheme-qcqs, and lem-weil-pbc-qcqs-scheme-spectral; their statements give each geometric prerequisite. The new node assumes a genuine open BASIS, not just an open cover; uniqueness can therefore be checked on smaller basis opens in every intersection. Its conclusion includes j and i affine, U_eta affine and both spectral, so the parent does not smuggle these facts into an otherwise elementary application. Integral X makes every nonempty affine open contain eta, proving the original affine-generic-inclusion argument. I did not assume X quasi-separated or intersections of affines affine. Normality is unnecessary in this conditional node; the input clopen bijections are explicit hypotheses, supplied by parent step 1.

For the ultrametric extension node I read Bhatt–Scholze Lemma 4.2.12, including the last paragraph on continuous functions factoring through components; the general topological formulation and the extension inverse are explicitly labelled agent deductions. I checked Mathlib Topology/Connected/TotallyDisconnected.lean:255–278, AlgebraicGeometry/Sites/ConstantSheaf.lean:88–98, and Topology/MetricSpace/Ultra/TotallySeparated.lean:25–32 after the recorded searches found them. These give the continuous lift and ultrametric total disconnectedness, but neither states the new precomposition ring isomorphism and its prescribed inverse. LocallyConstant.congrLeftRingEquiv concerns locally constant functions, which cannot replace all continuous maps into a norm-topological field. The old text explicitly proves clopen-ball separation, continuous factorization using the quotient topology, both inverse equations, preservation of ring operations, and the empty-space case. I kept that entire argument below. Completeness, compactness of the coefficient field and compactness of Y,Z play no role.

Parent step 1 uses exactly the chart node's basis and clopen-bijection conclusion. Every normal/integral/locally Noetherian/pro-etale hypothesis is already in the item; no property of U other than its being a pro-etale object is needed at this stage. Parent step 2 uses exactly the component node's conditional conclusion. Its input basis and bijections are those of step 1, and its affineness hypothesis is the parent's IsAffine U, so the homeomorphism has the required normalization for the actual projection. Parent step 3 uses exactly the topological extension node, with Y=|U_eta|, Z=|U|, i the projection and h from step 2. The field norm in the item gives the multiplicative ultrametric required there. It obtains both bijectivity of actual restriction and total disconnectedness for the coefficient realization. Parent step 4 uses only these preceding bijections and the defining pullback projection equations: both displayed composition equalities and both uniqueness arguments are written out. I marked only this composition/uniqueness calculation elementary. Parent step 5 uses the entire first sentence of lem-weil-pbc-condensed-field-continuous-realization, read directly in its node. It requires a totally disconnected normed field and any scheme; step 3 gives the extra topology hypothesis. I read Hemo–Richarz–Scholbach Example 3.1, p. 6, including its identification of pulled-back coefficients with U ↦ Maps_cont(U,A), and opened sk-def-sfb-pulled-back-coefficients and def-sfb-continuous-map-condensed-ring to check exactly which ring is being pulled back. The citations file quotes literal parts of these three statements and all three new statements. No step uses a fact present only inside the proof of a cited node.

I tested the new statements on U empty (B=D=0 and singleton function rings), X=Spec k (identity generic projection), disconnected affine objects (distinct clopen components remain distinct), the empty basis only on empty U, and trivially valued and incomplete normed fields. In the component lemma a proper open cover without refinements would not justify the overlap check; its explicit basis hypothesis repairs that possible ambiguity. In the extension lemma singleton spaces give evaluation and a disconnected Y over a singleton Z fails the homeomorphism hypothesis as required. In the chart argument nonnormal integral rings cannot be substituted in 092W. There is no strengthening of the parent or dropped case. All new nodes are statement-only; every notion is either introduced inline or cited through its statement dependencies, no doubled TeX escaping was added, and all searches recorded are the actual logged command queries, including a second semantic phrasing for every new node. The parent has 1972 proof characters and no step over 2000, so the long-step return is repaired by distribution rather than compression. Each new node receives a non-elementary argument of 1515–2132 original characters. B1–B10, C1–C8, D1–D5 and E1–E7 were checked against the explicit source and statement comparisons just described. The corrected issue is the workload split; no statement dispute or source error was found.

## Not duplicates

lem-sfb-normal-generic-chart-clopens vs lem-sc-clopen-rank-stratum-module-projector: the existing statement constructs projectors on module sheaves for rank strata; the new statement concerns normal affine chart rings and generic clopen lifting, with no modules or rank stratification.

lem-sfb-normal-generic-chart-clopens vs lem-sc-clopen-rank-stratum-derived-projector: the existing statement splits a derived object by a rank projector; the new statement is an affine chart and generic-idempotent assertion with no derived category.

lem-sfb-normal-generic-chart-clopens vs lem-sc-clopen-rank-strata-homology-lift: the existing statement lifts a homology morphism for rank strata; the new statement compares a normal-base chart and its generic fibre, not homology.

lem-sfb-normal-generic-chart-clopens vs lem-weil-pbc-spec-clopen-idempotent: the existing statement is the clopen/idempotent correspondence for a single ring; it gives no normal chart basis or comparison of B and B tensor k. It is an ingredient of the preserved chart argument, not the new conclusion.

lem-sfb-normal-generic-chart-clopens vs lem-weil-pbc-base-change-nilpotent-thickening-idempotents: the existing statement compares a nilpotent closed thickening with its base; generic localization is not a nilpotent quotient, and the new node assumes normality and weak etaleness instead.

lem-sfb-normal-generic-chart-clopens vs lem-weil-pbc-scheme-clopen-idempotent: the existing statement identifies global idempotents and clopens and their pullbacks; it does not show that a generic pullback has bijective idempotents or construct the normal weakly etale chart basis.

lem-sfb-normal-generic-chart-clopens vs lem-weil-pbc-integral-closure-finite-fibre-choose-g: the existing statement chooses a principal open from finite-type integral-closure fibre data; the new node neither assumes that finite-type product setup nor chooses a principal open.

lem-sfb-normal-generic-chart-clopens vs lem-weil-pbc-formal-fibre-transition-idempotents: the existing statement lifts idempotents across successive infinitesimal fibre thickenings; the new statement lifts them across a generic localization of a weakly etale chart.

lem-sfb-normal-generic-chart-clopens vs lem-weil-pbc-integral-closure-finite-fibre-image-clopen: the existing statement describes the image of one chosen finite fibre factor in an integral closure; the new node compares all clopens of a chart with all clopens of its generic fibre.

lem-sfb-normal-generic-chart-clopens vs lem-weil-pbc-integral-closure-finite-fibre-part-localization: the existing statement produces a lifted finite-fibre idempotent and a principal localization for a finite-type algebra; the new node has no finite-fibre product hypothesis and concerns arbitrary weakly etale charts over a normal scheme.

lem-sfb-normal-generic-chart-clopens vs lem-weil-pbc-weak-etale-integral-closure: the existing statement gives integral closedness of B in B tensor k over a normal domain; the new statement includes geometric chart-basis construction, stalk and fraction-field identification, injective localization, and generic idempotent/clopen bijections. The preserved argument uses the existing theorem without recreating it.

lem-sfb-normal-generic-component-comparison vs lem-pe-spectral-components-profinite: the existing statement says one spectral component quotient is profinite; the new node glues LOCAL clopen bijections for an affine generic fibre and compares its component quotient with that of U.

lem-sfb-normal-generic-component-comparison vs lem-sfb-spectral-clopen-component-homeomorphism: the existing criterion requires GLOBAL bijectivity on clopens for a map of spectral spaces. The new conditional scheme lemma starts with clopen bijections only on an open BASIS and proves the global bijection, affine generic geometry and hence the criterion prerequisites. It is not a specialization without the old gluing and affine arguments.

lem-sfb-normal-generic-component-comparison vs lem-weil-pbc-profinite-component-ring-pullback: the existing statement constructs a new w-local ring from a profinite change of components. The new node analyzes the given generic fibre of an arbitrary affine X-scheme under local clopen hypotheses; no w-local base ring or constructed profinite change is present.

lem-sfb-normal-generic-chart-clopens vs lem-sfb-normal-generic-continuous-sections: the parent asserts continuous coefficient-section bijections and naturalities; the new node stops at geometric charts, injective generic localization and clopen lifting, with no coefficient field.

lem-sfb-normal-generic-component-comparison vs lem-sfb-normal-generic-continuous-sections: the parent proves continuous-section extension; this node is a conditional local-clopen-to-component comparison independent of coefficient fields and assumes the local clopen input rather than proving normal generic restriction.

lem-sfb-ultrametric-component-map-extension vs lem-sfb-normal-generic-continuous-sections: the new lemma is purely topological with an assumed component homeomorphism, and proves no normal-generic geometric comparison or condensed coefficient identification.

lem-sfb-ultrametric-component-map-extension vs lem-sfb-totally-disconnected-coefficient-realization: the existing statement identifies condensed ring coefficients with continuous function sheaves; it does not compare continuous functions along a map inducing a homeomorphism on connected components.

## Original arguments retained for the new workers

The following is the complete original proof text, copied verbatim in its original order. It is handoff material in this report; the three new DAG nodes remain statement-only. Old steps 1–2 belong to lem-sfb-normal-generic-chart-clopens, steps 3–4 to lem-sfb-normal-generic-component-comparison, and steps 5–6 to lem-sfb-ultrametric-component-map-extension. Steps 7–8 remain in the parent as its steps 4–5.

### Original step 1

First record the chart geometry, without assuming $X$ affine or quasi-separated. If $V=\operatorname{Spec}R\subset X$ is nonempty affine, $R$ is a domain by [def-pc-integral-scheme]. By [lem-weil-pbc-affine-open-stalk-localization], its prime localizations are the corresponding local rings of $X$, hence are normal by hypothesis. Apply [lem-weil-pbc-normal-domain-of-local-normal] to see that $R$ is integrally closed in its fraction field. The generic point corresponds to $(0)$, so the same stalk-localization statement identifies this fraction field with $k$. Cover $U$ by affine opens $W=\operatorname{Spec}B$ mapping into such $V$. These form an open basis: shrink around the image point in $X$, then take an affine neighbourhood in its inverse image. By [sk-lem-pe-weakly-etale-stability] and the site definition, $W\to V$ is weakly etale. It therefore gives a weakly etale ring map $R\to B$ in [def-weil-pbc-ind-etale-algebra]; in particular $B$ is flat over $R$. Finally [lem-weil-pbc-fibre-product-affine-spectra] identifies $W_\eta$ with $\operatorname{Spec}(B\otimes_Rk)$ and its projection with the structural ring map.

Cited statement ids: def-pc-integral-scheme, lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-normal-domain-of-local-normal, sk-lem-pe-weakly-etale-stability, def-weil-pbc-proetale-site, def-weil-pbc-ind-etale-algebra, lem-weil-pbc-fibre-product-affine-spectra.

### Original step 2

On each chart from step 1 put $D=B\otimes_Rk$. This is the localization of $B$ at the images of $R\setminus\{0\}$: the maps sending $b\otimes(a/s)$ to $ab/s$ and $b/s$ to $b\otimes(1/s)$ are inverse by the tensor and localization relations. By [lem-trf-flat-module-torsionfree-domain], a nonzero $s\in R$ acts injectively on $B$. The localization zero criterion then makes $B\to D$ injective. The hypotheses of [lem-weil-pbc-weak-etale-integral-closure] are now exactly satisfied. Every idempotent $e\in D$ is integral over $B$, since it solves the monic equation $T^2-T=0$; it consequently belongs to $B$, where injectivity gives the same idempotent equation and uniqueness of the lift. The correspondence of [lem-weil-pbc-spec-clopen-idempotent] now proves that inverse image gives a bijection $\operatorname{Clop}(W)\to\operatorname{Clop}(W_\eta)$: $D(b)$ pulls back to $D(b\otimes1)$ by the definition of inverse image of a prime. This includes $B=0$, since then $D=0$ and both spectra are empty.

Cited statement ids: lem-trf-flat-module-torsionfree-domain, lem-weil-pbc-weak-etale-integral-closure, lem-weil-pbc-spec-clopen-idempotent.

### Original step 3

We globalize the clopen bijections, using only their uniqueness on the chart basis of step 1. Given a clopen $H\subset U_\eta$, extend $H\cap W_\eta$ uniquely to a clopen $H_W\subset W$ on every such chart. For two charts $W,W\prime$, cover their intersection by smaller chart-basis opens $Z$. The restrictions $H_W\cap Z$ and $H_{W\prime}\cap Z$ have the same generic inverse image $H\cap Z_\eta$, so step 2 on $Z$ makes them equal. Thus the $H_W$ agree on overlaps. Their union $\widetilde H\subset U$ is open, and its complement is open because on each $W$ it is $W\setminus H_W$. Its generic inverse image is $H$. Uniqueness holds by restricting any other extension to every $W$ and applying step 2. Hence inverse image along $i:U_\eta\to U$ is bijective on clopen subsets. This proof does not assume that intersections of affine opens of $X$ or $U$ are affine, or that the individual components of $U$ are open.

Cited statement ids: none (elementary argument from previous steps).

### Original step 4

The morphism $j:\operatorname{Spec}k\to X$ is affine: the inverse image of every nonempty affine open of the integral $X$ is all of $\operatorname{Spec}k$, and that of the empty open is empty. By [lem-weil-pbc-affine-morphism-permanence], $i:U_\eta\to U$ is affine and $U_\eta$ is affine. Both $U$ and $U_\eta$ are therefore qcqs by [lem-weil-pbc-affine-scheme-qcqs], and spectral by [lem-weil-pbc-qcqs-scheme-spectral]. Apply [lem-sfb-spectral-clopen-component-homeomorphism] to their continuous map $i$ and the bijection proved in step 3. It yields a homeomorphism $h=\pi_0(i):P_\eta\xrightarrow{\sim}P$, where $P_\eta=\pi_0(U_\eta)$, $P=\pi_0(U)$, normalized by $h q_\eta=q i$. This remains valid for the empty object.

Cited statement ids: lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-scheme-spectral, lem-sfb-spectral-clopen-component-homeomorphism.

### Original step 5

The field $A$ is totally disconnected. Indeed an ultrametric ball $B(a,r)$ is open and closed: if $y$ lies outside it, the ball $B(y,r)$ is disjoint from it by the strong triangle inequality. For distinct $a,b$, choose $0<r\leq |a-b|$; this clopen ball separates them. A connected subset cannot meet both a clopen set and its complement, so has at most one point. Any continuous $f:|U_\eta|\to A$ is therefore constant on every connected component: its image on that component is connected, as a separation of the image would pull back to a separation of the component. Thus $f=\bar f q_\eta$ for a unique function $\bar f:P_\eta\to A$. The quotient topology makes $\bar f$ continuous, since $q_\eta^{-1}(\bar f^{-1}(O))=f^{-1}(O)$ is open for every open $O\subset A$. The same factorization holds for continuous functions on $U$.

Cited statement ids: none (elementary argument from previous steps).

### Original step 6

Define the extension of $f$ to be $E_U(f)=\bar f h^{-1}q$. It is continuous and $E_U(f)i=\bar f h^{-1}h q_\eta=f$. Conversely, if $g:|U|\to A$ is continuous, write $g=\bar g q$ as in step 5. Its restriction factors as $\bar g h q_\eta$, so applying the displayed formula returns $\bar g h h^{-1}q=g$. This proves bijectivity of the actual restriction map. Restriction preserves $0,1,+$ and multiplication pointwise; its inverse does too, since restriction is injective and the restrictions of $E_U(f+f\prime)$ and $E_U(f)+E_U(f\prime)$ are equal, and likewise for products and constants. For $U=\varnothing$, both function rings have one element and the same formula is the unique map.

Cited statement ids: none (elementary argument from previous steps).

### Original step 7

Let $v:V\to U$ be any $X$-morphism of affine pro-etale objects and $v_\eta:V_\eta\to U_\eta$ its base change. The projection equations give $iv_\eta=vi_V$. Thus $(g\circ v)\circ i_V=(g\circ i)\circ v_\eta$ for every continuous $g$ on $U$. This proves the restriction square commutes. In particular $E_U(f)\circ v$ and $E_V(f\circ v_\eta)$ have identical generic restrictions, so injectivity for $V$ proves they agree. For a continuous field homomorphism $a:A\to A\prime$, composition is continuous and $a\circ(g\circ i)=(a\circ g)\circ i$. This proves coefficient naturality of restriction. When both coefficient fields satisfy the statement, $a\circ E_U^A(f)$ and $E_U^{A\prime}(a\circ f)$ have the same generic restriction and hence agree by uniqueness for $A\prime$.

Cited statement ids: none (elementary argument from previous steps).

### Original step 8

Finally use the canonical realization [lem-weil-pbc-condensed-field-continuous-realization] with the totally disconnected normed field $A$ established in step 5. It identifies the ring sheaf $R_{A,T}$ from [sk-def-sfb-pulled-back-coefficients] with continuous functions on $T$ in precisely the topology supplied by [def-sfb-continuous-map-condensed-ring]. Thus the ring bijections above concern the requested continuous coefficients and the actual restriction maps. All arguments used the norm topology itself; no completion, compactness of the coefficient field, or passage to discrete coefficients occurred.

Cited statement ids: lem-weil-pbc-condensed-field-continuous-realization, sk-def-sfb-pulled-back-coefficients, def-sfb-continuous-map-condensed-ring.

