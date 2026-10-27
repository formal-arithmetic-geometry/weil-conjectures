## Worker report

This repairs the batch5 return of 2026-10-22 for Q109/lem-trf-log-fan-chart-blowup. The named sandbox initially contained only the four brief markers, with no delivered JSON, report or search log. I copied the current read-only repository node, which has exactly the ten proof steps and 10015 text characters identified in the return. No git commands were run in the shared repository. No Lean was written or compiled. Existing metadata, the statement, and the Lean record are retained; the delivery tool rebases the stage-1 fields onto the current server base.

Files written (all under this item's sandbox):

- dag/nodes/sec-trace-formula/lem-trf-log-fan-chart-blowup.json: repaired statement node, split; unchanged statement, five short assembly steps.
- dag/nodes/sec-trace-formula/lem-trf-monoid-chart-characteristic-fan.json: statement, unsplit, no Mathlib match; proof and proof_deps empty.
- dag/nodes/sec-trace-formula/lem-trf-fan-chart-local-monoid-lift.json: statement, unsplit, no Mathlib match; proof and proof_deps empty.
- dag/nodes/sec-trace-formula/lem-trf-fan-center-local-blowup-charts.json: statement, unsplit, no Mathlib match; proof and proof_deps empty.
- dag/nodes/sec-trace-formula/lem-trf-saturated-fan-blowup-lift.json: statement, unsplit, no Mathlib match; proof and proof_deps empty.
- dag/nodes/sec-trace-formula/lem-trf-strict-log-blowup-cartesian.json: statement, unsplit, no Mathlib match; proof and proof_deps empty.
- report.md and citations.json: signed self-review and verbatim statement quotes for every parent citation.
- returned-proof.json: read-only baseline of the ten returned steps; their full texts are also reproduced below for delivery readers.
- searches.jsonl, search-plan.json, and the five *-search-results.txt files: actual msearch requests and complete printed results retained for retries. repair.py and write_report.py are sandbox-only generation scripts.

Attachments: none. Searching lean/WeilConjectures for the blueprint tag, fan-chart names and logarithmic monoidal notions found no project declaration supplying these statements. lean/Sheaf/AlgebraicGeometry/LogFanChartBlowup.lean:308 states the parent, but its proof at line 354 is sorry, so it is not an attachment.

WANTED: none newly required. The ILO volume is present and was read. Kato (1988), section 1, is already listed as wanted in the supporting associated-log node's source; this repair does not claim to have read that absent reference or import a new route from it.

What was wrong: the parent carried five independent log-geometric arguments inline, including steps marked elementary despite needing substantial work. The return requires at least three independent jobs and an assembly of at most 3000 characters. This repair creates five jobs, all statement-only, and a 2272-character parent assembly. It preserves the complete earlier argument in this report and gives its precise location in the new work. The statement is not disputed or changed. The old citation to VI 1.6 is not used to assume log regularity: that paragraph concerns log regular schemes, whereas freeness for the local lift here comes from the existing general fs-face-sharpening lemma.

What remains: the five new statements await their own stage-1 splits. That is the requested delivery, not a claim that their proofs or Lean are complete.

## Repair of the return

The return has one repeated request, rather than separate mathematical numbered objections. It is addressed as follows:

1. Work is distributed among five genuinely different arguments, not moved to a single replacement theorem. Their inherited argument sizes are 1274, 2923, 1971, 1304 and 1246 characters, respectively. They address fixed charts, local lifting, affine blowup comparisons, the universal property on monoidal spaces, and a single strict log Cartesian square. None contains the entire tower assertion, finite covering assertion, and composition assertion of the parent.
2. Each new node is unsplit with an empty proof, empty proof_deps, null proof_origin, its own self-contained statement and ILO source, exact blueprint ancestry, and five actual searches (two semantic phrasings, Loogle, grep and LeanSearch). The strict-base-change job also has a second targeted grep.
3. The parent keeps the exact statement. Its assembly is 2272 characters, below 3000, and no step exceeds 2000. The finite-cover selection and ordered induction are written out; the five substantial subarguments are delegated by citations whose statements say exactly what is used.
4. Every part of the old argument is retained below, including the stalk quotient, Zariski spreading of basis lifts and equations, chart-isomorphism verification, inverse-image equality of ideals, ring tensor-product charts, generator selection, uniqueness of fractions and saturated roots, overlap localizations, ordered induction, identity on base log sections, and fs rather than ordinary Cartesian comparison.

## Not duplicates

Searches were made over all dag/nodes statements and source places for fan chart, characteristic monoid, saturated log blowup, 3.3.12, 3.3.13, 3.1.19 and 3.3.11; the entire imported blueprint was searched with tools/blueprint_refs.py for fan chart, log blowup, monoid chart, sharp monoidal, saturated log, monoidal, saturation and characteristic monoid. No blueprint node states any of the five jobs. Names were checked to be unused. The closest existing statements were opened and read:

lem-trf-monoid-chart-characteristic-fan vs lem-trf-associated-log-universal-stalks: the existing result gives the associated etale log structure, its universal property and stalk pushout; the new result constructs the sharp fan map, proves the global chart is Zariski, and identifies its characteristic sheaf with a fan.

lem-trf-monoid-chart-characteristic-fan vs lem-trf-fs-face-sharpening: the existing result is an algebraic theorem on one monoid and one face, not a statement about log charts and monoidal-space morphisms.

lem-trf-fan-chart-local-monoid-lift vs lem-trf-strict-fan-chart-local-comparison: the existing result compares two already supplied fan charts under a strict morphism; it does not lift a characteristic chart to the log structure. It also depends on this parent and cannot replace an input here.

lem-trf-fan-chart-local-monoid-lift vs lem-trf-fs-chart-free-factorization: the existing statement factors an injective map of fs monoids with torsion-free cokernel; it does not split the units/characteristic extension in a sheaf or spread it to a Zariski chart.

lem-trf-fan-center-local-blowup-charts vs lem-trf-coherent-log-ideal-chart-construction: the existing theorem starts with a coherent log ideal and constructs its log blowup; the new theorem identifies the center from a fan chart and identifies the local fan maps and their canonical characteristic comparisons.

lem-trf-fan-center-local-blowup-charts vs lem-trf-log-regular-toric-refinement: the existing theorem assumes log regularity and proves that property for an affine monoid refinement; it does not compare characteristic fan morphisms and would add an unavailable hypothesis.

lem-trf-saturated-fan-blowup-lift vs lem-trf-affine-fan-hom-universal: the existing statement represents maps to a fixed affine sharp monoid spectrum by global monoid homomorphisms; it does not give the saturated blowup lifting property or compare its glued charts.

lem-trf-saturated-fan-blowup-lift vs lem-trf-sharpening-fan-bijection: the existing statement concerns ideals and towers on monoschemes, plus desingularization rules. The new one concerns arbitrary sharp saturated integral monoidal source spaces, including log characteristic spaces, with no monoscheme hypothesis.

lem-trf-strict-log-blowup-cartesian vs def-per-strict-log-morphism: the existing node defines strictness and its stalk criterion, not the Cartesian square for saturated logarithmic blowups.

lem-trf-strict-log-blowup-cartesian vs lem-sfb-log-smooth-composition-strict-base-change: the existing result concerns log smoothness and log etaleness, not the saturated blowup fiber-product universal property.

lem-trf-strict-log-blowup-cartesian vs lem-trf-functorial-log-blowup-etale-descent: the existing result descends an already functorial tower rule from charted objects; it does not establish the single-step comparison needed as input.

lem-trf-monoid-chart-characteristic-fan vs lem-trf-log-fan-chart-blowup: the child states only its independent local or single-stage subargument; the parent assembles chart existence, the finite cover, arbitrary ordered towers, and their compatibilities.

lem-trf-fan-chart-local-monoid-lift vs lem-trf-log-fan-chart-blowup: the child states only its independent local or single-stage subargument; the parent assembles chart existence, the finite cover, arbitrary ordered towers, and their compatibilities.

lem-trf-fan-center-local-blowup-charts vs lem-trf-log-fan-chart-blowup: the child states only its independent local or single-stage subargument; the parent assembles chart existence, the finite cover, arbitrary ordered towers, and their compatibilities.

lem-trf-saturated-fan-blowup-lift vs lem-trf-log-fan-chart-blowup: the child states only its independent local or single-stage subargument; the parent assembles chart existence, the finite cover, arbitrary ordered towers, and their compatibilities.

lem-trf-strict-log-blowup-cartesian vs lem-trf-log-fan-chart-blowup: the child states only its independent local or single-stage subargument; the parent assembles chart existence, the finite cover, arbitrary ordered towers, and their compatibilities.

## Review by Q109

I read the chapter and sk-i-curve-zero unit records, GOAL.md, the three blueprint levels in SETUP.md, the stage-1 contract and delivery-errors B through E. The current unit uses the contracting-correspondence proof. This node is the retained historical monoidal-resolution input below lem-trf-local-term-locality, as its existing ancestry says; the repair does not alter that unit or invent a new route. I read the current main-20261015 locality statement/proof as well as the ILO volume. ILO VIII printed pp.98--102 (3.1.1--3.1.25), pp.106--109 (3.3.2--3.3.13) and the finite-cover passage on pp.109--110 give the route. VIII 3.3.13(ii) expressly warns that a fan chart need not have a global monoscheme lift; the local lifting statement respects that warning. VIII 3.3.9 and 3.3.11 supply the saturated rather than ordinary comparison. VI 1.1, printed p.69, supplies the locally Noetherian and etale-site conventions. VI 1.6 is not applied outside its log-regular hypotheses.

For the new fixed-chart statement I checked the point map Q minus the unit face, the open preimages D(q), and the face-localization quotient against 3.1.2--3.1.10 and 3.3.12. It assumes an actual global fs monoid chart, so it is a proper intermediate input to local chart existence rather than a relabelled covering clause. For the local-lift statement I checked F_z is the affine generalization neighborhood (3.1.4(iii), 3.1.10(ii)); the finite-basis splitting and finite spreading argument uses the sharp fs stalk, not log regularity. The final chart verification uses the associated-log universal property and identity on units as in the old steps. For the center/comparison statement I checked the center is the inverse image in N of the generated characteristic ideal, not a ring ideal, and that both models use the same saturated fraction monoids (3.1.19--3.1.25 and 3.3.7--3.3.13). The statement includes local Noetherian preservation and Zariski charts so induction has the hypotheses it needs. For the universal fan-lift statement I checked the source is sharp, saturated and integral; these are exactly what ensure cancellation, a unique image of every fraction, and existence of the saturated extension. It applies to a characteristic space, which need not itself be a fan. For the strict-change statement I checked Zariski log pullback, the unit quotients, the characteristic-ideal inverse image, and the universal property in the fs category (3.3.8--3.3.11), including the strictness of the comparison. On a shared monoid chart the pullback is given by the same monoid and the base-changed ring chart, proving that strictness. For the extra characteristic-ideal formulation, finitely many local generators of K lift locally to N; in an fs chart each lift is a chart element times a unit after shrinking, hence its inverse image is a coherent log ideal. This supplies that formulation without assuming a ring ideal is nonzero.

I opened every statement cited by the revised parent. Step 1 uses the fs definition only for strict etale chart neighborhoods, the new fixed-chart statement for the characteristic fan, the affine qcqs statement only for source quasi-compactness, and the etale-open statement for images of opens. I checked Stacks 00E8, algebra.tex label lemma-quasi-compact, and 03WT, morphisms.tex label lemma-etale-open. A finite subcover is then the definition of quasi-compactness. The locally Noetherian and characteristic torsion hypotheses of the parent's conditional clause have not been dropped, even though the fs chart argument already supplies torsion-freeness of its sharp stalks.

Step 2 uses the local-lift statement for exactly the Zariski neighborhoods and monoid lifts it asserts, and the local-blowup statement for both coherence of the prescribed center and the displayed ring and characteristic charts. It does not use an existence theorem as though it supplied an unrecorded comparison. Step 3 uses invertibility from the definition of saturated log blowup and the new fan universal-property statement for uniqueness on overlaps. The sheaf isomorphisms and their geometric normalization were obtained in Step 2, so the gluing does not assert an additional comparison without a citation. Step 4 is elementary induction using the one-stage outputs already established: zero is the original datum; the successor applies that construction at the next ordered center; local Noetherian fs and Zariski properties are explicit in the local-charts statement. Definition-level uniqueness and the cited fan-lift uniqueness identify concatenations without forgetting the identity log map. Step 5 uses the strict-change statement for the characteristic isomorphism, equality of pulled-back centers, strict comparison, and fs Cartesian property. The fan-lift uniqueness supplies the compatibility of the chart maps. Iterating it gives strict comparisons at every stage, with the initial comparison equal to g on sections, not merely on underlying schemes. citations.json quotes the complete actual statements so each of these clauses is available verbatim.

Small cases were checked for each job. For Q a group the fixed-chart fan is the point and the characteristic is zero; for Q=0 the structure is trivial. At a generic fan point P=0, the local-lift basis is empty and the construction gives the trivial chart. For the center/comparison job, a unit ideal gives an identity blowup since P is already saturated; a principal ideal needs only one chart. For the two-generator ideal of N^2, the charts add e_2-e_1 or e_1-e_2 and the overlap inverts that difference, as the fan lifting statement requires. When the associated ring monomials vanish, the logarithmic center is still legitimate: no nonzero ring-ideal or log-regularity hypothesis is imposed. Empty scheme charts and empty T have unique maps and no stalk checks. Strict identity maps and composites give identity and composed Cartesian comparisons. The empty covering and zero-length tower are handled explicitly by the parent; no positive-rank or nonempty-scheme hypothesis has been introduced.

The B1--B7 checks are substantive here: every new node has no proof or sketch in its statement, introduces all its objects, defines or cites its notions, uses single TeX escaping, and cites precise ILO places. There are no new Stacks-source nodes or Mathlib leaves, so neither an invented tag nor an unverified declaration/line is recorded. Existing generic statements were reused rather than reproduced. All five jobs were searched with the required msearch command; the first and second phrasings both returned ordinary algebraic geometry, group/localization facts or unrelated logarithms, never logarithmic monoidal geometry. Loogle and the targeted source greps found no corresponding log objects. The broad strict/log grep had irrelevant analytic-log and restriction hits; the additional AlgebraicGeometry-only grep had zero hits. No service failure was called a negative match. Recorded queries and verdicts are taken from the actual log, and full printed hits are retained. There are no new off-route theorem citations, and the generic affine/open tools in the parent are explicitly declared in split_report.tool_uses. The new nodes do not depend on their parent, and no new statement depends on the existing strict-chart-comparison or descent statements that depend on the parent.

The correction requested by the return is the five-way split and the short assembly, not deletion of the old mathematics. Below is an exact handoff of every old text and its dependencies. These are report-only proof guides for the future workers, not proof fields or proof sketches inside the new statements. The long old Step 4+5 argument belongs to the local-lift job and is deliberately left to that worker to split further if needed.

The first server dry run found that its citation scanner did not recognize the two definition ids written together in one bracket in the strict-change statement. I replaced that with two individual brackets, retaining the same two statement dependencies, and clarified the inline meaning of Zariski log structure in the local-charts statement. No mathematical statement of the parent changed.

## Full retained arguments and their new owners

### Returned step 1 -> lem-trf-monoid-chart-characteristic-fan

Start with any fs monoid chart $Q\to M$ on a strict etale neighborhood $U$ of a geometric point of $X$; these neighborhoods cover by the definition of fs. Define $c_Q:U\to\operatorname{Spec}_{\rm mon}Q$ by sending $u$ to the prime ideal complementary to $E_u=\{q:\alpha(q)\in\mathcal O_{U,u}^{\times}\}$. The inverse image of $D(q)$ is the open where $\alpha(q)$ is a unit, so this map is continuous. At a geometric point over $u$, the associated-log stalk formula identifies the characteristic with $Q_{E_u}/E_u^{\rm gp}$: adjoining units first localizes $Q$ at $E_u$, and quotienting by all ring units then kills exactly the units of this localization. The fs face-sharpening lemma says that this is precisely the stalk of the sharp fan sheaf and is sharp fs with free group completion. Thus sharpening $c_Q$ induces an isomorphism of characteristic sheaves. The log structure associated to a constant chart $Q\to\mathcal O_U$ is Zariski: its sections are locally the displayed pairs $[q,a]$ with $a$ a unit, and the same construction pulled to the etale site has the associated-log stalk formula. Hence these are fan charts in the sense of the statement. This proves the first assertion of (i), and also shows that their affine target fans are saturated and torsion free.

Cited inputs retained for that argument: def-trf-fs-log-blowup, def-trf-fine-fan-blowup, lem-trf-associated-log-universal-stalks, lem-trf-fs-face-sharpening.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VIII 3.3.2--3.3.4(ii), 3.3.12; 3.1.1--3.1.10.

### Returned step 2 -> parent Step 1, finite-subcover assembly

Refine each chart neighborhood of Step 1 by affine open neighborhoods. This preserves both the monoid chart and strict etaleness. Each source is quasi-compact by the affine-scheme qcqs lemma. The open-map lemma says that their images in $X$ are open, and these images cover $X$. Quasi-compactness of $X$ therefore selects finitely many of them. Their target fans retain the saturated torsion-free property established in Step 1. This is the finite family required in (i). If $X$ is empty, choose the empty family.

Cited inputs retained for that argument: lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-etale-morphism-open-map.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VIII 3.3.4(ii), finite-cover argument of proof of 3.3.15, pp.109--110.

### Returned step 3 -> lem-trf-fan-chart-local-monoid-lift

Now fix the fan chart $c:(V,\overline N)\to F$ of (ii), so $N$ is Zariski. Around $z=c(v)$ restrict to the open affine fan $F_z$ of generalizations of $z$. To see this directly, choose an affine fan neighborhood presented by $Q$; the generalizations of $z$ form the basic open obtained by inverting its face $E$, since a face of a finitely generated monoid is generated by those of a fixed finite generating set which belong to it. Sharpening gives $F_z=\operatorname{Spec}_{\rm mon}P$ with $P=\mathcal P_{F,z}$. This description is independent of the affine neighborhood because every open containing $z$ contains all its generalizations. The chart identifies $P$ with $\overline N_v$. Applying the face-sharpening result to any fs log chart at $v$ shows that $P$ is sharp fs and $P^{\rm gp}$ is free of finite rank. On $c^{-1}F_z$ the chart supplies the section homomorphism $P\to\overline N$.

Cited inputs retained for that argument: def-trf-fine-fan-blowup, lem-trf-fs-face-sharpening.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VIII 3.1.2--3.1.4, 3.1.8(ii), 3.1.10(ii), 3.3.12.

### Returned step 4 -> lem-trf-fan-chart-local-monoid-lift

Lift the preceding characteristic section homomorphism locally near $v$. In the Zariski stalk there is an exact sequence of groups $\mathcal O_{V,v}^{\times}\to N_v^{\rm gp}\to\overline N_v^{\rm gp}\to0$. Choose lifts of a finite basis of $P^{\rm gp}$, giving a group section $s:P^{\rm gp}\to N_v^{\rm gp}$. For every $p\in P$, any representative $m\in N_v$ of $p$ differs from $s(p)$ by a unit; therefore $s(p)\in N_v$. Represent the finitely many chosen basis lifts by sections of $N^{\rm gp}$ on a common Zariski neighborhood. For a finite generating set $p_1,\ldots,p_t$ of $P$, represent $s(p_i)$ there by sections of $N$; the equalities with the corresponding integer combinations of basis lifts hold after shrinking. They define a homomorphism $h:P\to N$ because $N$ embeds into $N^{\rm gp}$. Shrink again so that the images of these finitely many generators in $\overline N$ equal the prescribed sections from $c$. Thus the sharpening of $h$ is precisely $c$ on this neighborhood. All shrinking is Zariski: the lifts are germs of the Zariski log structure stipulated in the definition of a fan chart.

Cited inputs retained for that argument: def-trf-fs-log-blowup, lem-trf-fs-face-sharpening.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VIII 3.3.12--3.3.13: local lifting of a fan chart, expanded using the free characteristic group in VI 1.6 and VIII 3.1.10.

### Returned step 5 -> lem-trf-fan-chart-local-monoid-lift

The homomorphism $h$ is a log chart, not just a lift of characteristic sections. Indeed its associated-log morphism $L(P,\alpha h)\to N$ exists by the associated-log universal property. At any stalk $w$ its map on characteristics is the isomorphism $P_{E_w}/E_w^{\rm gp}\simeq\overline N_w$ furnished by $c$, with $E_w$ the face of elements becoming units. A homomorphism of integral log monoids over the same local ring that is identity on units and an isomorphism on characteristics is an isomorphism: a target element has a source representative up to a unit, giving surjectivity; two source elements with equal images differ by a unit, and cancellation forces that unit to be $1$, giving injectivity. The associated-log stalk formula therefore proves $h$ is a chart throughout the neighborhood. We have obtained Zariski locally a monoid chart whose sharpening is the given $c$, without assuming a global lift of $c$.

Cited inputs retained for that argument: lem-trf-associated-log-universal-stalks, lem-trf-fs-face-sharpening, def-trf-fs-log-blowup.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VIII 3.3.2, 3.3.12--3.3.13, local chart verification.

### Returned step 6 -> lem-trf-fan-center-local-blowup-charts

Consider one center $J\subset\mathcal P_F$. On an affine fan neighborhood as in Step 3, write its ideal as generated by a finite nonempty set $E\subset P$, and use the local lift $h$ of Steps 4--5. The inverse image in $N$ of the ideal generated by $c^{-1}J$ is exactly the log ideal generated by $h(E)$. To check this, a characteristic class belongs to that ideal precisely when it is $e+p$ for some $e\in E$ and a local characteristic class $p$; lifting $p$ to $N$, the original section is $h(e)$ plus that lift plus a unit. Conversely every such sum maps into the characteristic ideal. Thus the proposed center $\mathcal I$ is nonempty and coherent in the definition of log ideal. This is local and so defines the specified ideal on all of $V$. The log-ideal chart-construction theorem applies to this locally Noetherian fs log scheme and constructs its saturated log blowup $b:(V',N')\to(V,N)$, with the universal property of the definition. No log regularity of $V$ or nonvanishing of its algebraized ring ideal is needed.

Cited inputs retained for that argument: def-trf-fs-log-blowup, def-trf-fine-fan-blowup, lem-trf-coherent-log-ideal-chart-construction.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VIII 3.3.7--3.3.9 and 3.3.13(i).

### Returned step 7 -> lem-trf-fan-center-local-blowup-charts

Compare the charts on this one blowup. Write $R_a=(P[E-a])^{\rm sat}$ for $a\in E$. Over an affine log chart $\operatorname{Spec}A\subset V$, the log-ideal construction gives charts $\operatorname{Spec}(A\otimes_{\mathbf Z[P]}\mathbf Z[R_a])$ with log chart $R_a$. By the definition of saturated fan blowup the corresponding open of $F'=\operatorname{Bl}_J(F)^{\rm sat}$ is the sharpened monoid spectrum of exactly $R_a$. Send a point $w$ of the scheme chart to the prime ideal complementary to the face $H_w$ of elements of $R_a$ whose images are units at $w$. As in Step 1 this is continuous and local, and the associated-log stalk formula and face-sharpening lemma identify both characteristic stalks with $(R_a)_{H_w}/H_w^{\rm gp}$. Hence this local map is a fan chart. The ring tensor products here are the actual saturated log charts supplied by the cited theorem; we do not replace them by an ordinary scheme blowup or its normalization.

Cited inputs retained for that argument: lem-trf-coherent-log-ideal-chart-construction, def-trf-fine-fan-blowup, lem-trf-associated-log-universal-stalks, lem-trf-fs-face-sharpening.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VIII 3.1.19--3.1.25, 3.3.8--3.3.9 and 3.3.13(i),(iii).

### Returned step 8 -> lem-trf-saturated-fan-blowup-lift

These local maps glue canonically to $c':(V',\overline N')\to F'$. Here is the uniqueness check, including overlaps of different local lifts. For a sharp saturated monoidal space mapping to $F$, with the induced ideal locally principal, at any point some member $a$ of a finite generating set $E$ generates that ideal at the stalk: if $t$ generates and $a=t+u$, $t=a+r$, then $u+r=0$ so $u$ is a unit. Near that point every $b-a$, $b\in E$, has a unique image in the integral target monoid. Saturation forces unique images for $R_a$: in the group completion they are already determined, and $nq$ in the monoid implies $q$ is in it. The finite generation of $R_a$ permits representing these germs on a common neighborhood. This determines the lift to the $a$-chart of $F'$. Where two generators work, their difference is a unit, which is exactly the common localization used to glue those fan charts. Thus any two lifts agree locally and then globally. The maps of Step 7 therefore agree on every overlap, regardless of the lift $h$, and their monoid-sheaf maps glue by the sheaf axiom. Their characteristic-sheaf maps are local isomorphisms as proved in Step 7, so $c'$ is a fan chart on the Zariski log scheme $(V',N')$. In particular its map on each geometric stalk is the isomorphism asserted in (ii).

Cited inputs retained for that argument: def-trf-fine-fan-blowup, def-trf-fs-log-blowup, lem-trf-fine-monoid-finite-saturation.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VIII 3.1.19--3.1.25 and 3.3.13(i),(iii): uniqueness and gluing of the chart maps.

### Returned step 9 -> parent Step 4, ordered induction and concatenation

Induct on the length of the ordered tower. At length zero put $(V_0,N_0)=(V,N)$ and $c_0=c$. Given $(V_i,N_i)$ and $c_i$, apply Steps 6--8 to its specified center $J_i$ to produce $(V_{i+1},N_{i+1})$, its pulled-back log center, and $c_{i+1}$. This proves existence and the characteristic-stalk assertion at every level; Step 6 proves nonemptiness and coherence at every level. The schemes remain locally Noetherian, as is part of the cited construction of an fs log scheme in its stated convention. Concatenating two fan towers performs exactly these same operations on the same ordered centers; the universal property of each log blowup identifies the resulting levels, and Step 8 identifies their fan charts. Thus pullback is compatible with composition, including the empty tower.

Cited inputs retained for that argument: def-trf-fs-log-blowup, def-trf-fine-fan-blowup, lem-trf-coherent-log-ideal-chart-construction.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VIII 3.3.9--3.3.10, 3.3.13(i),(iii).

### Returned step 10 -> lem-trf-strict-log-blowup-cartesian

Finally let $g:(W,L)\to(V,N)$ be strict. Its characteristic sheaf is the pullback of that of $V$: in the associated log pushout the additional source units disappear when passing to characteristics. Thus $c\circ g$ is a fan chart, and taking the inverse image of $J$ in characteristics and then in $L$ gives exactly $g^{-1}\mathcal I\,L$, since this can be checked on the generators $h(E)$ of Step 6. Construct $W'=\operatorname{LogBl}^{\rm sat}_{g^{-1}\mathcal I L}W$ by the cited log-ideal theorem. For any fs log scheme $T$ over $W$, the universal property identifies maps $T\to W'$ with invertibility of the pulled-back ideal. The same property identifies maps $T\to V'$ over $V$ with this identical condition. Consequently $W'$ represents $W\times_V V'$ in the fs category. This proves the required base-change isomorphism without asserting that the underlying ordinary scheme fiber product computes an fs fiber product. The local fan maps agree by the uniqueness in Step 8. Induction applies the same argument at every level, and all identifications respect identities and composition because each represents the same universal factorization with its specified center. This establishes strict base-change compatibility for the entire tower.

Cited inputs retained for that argument: def-trf-fs-log-blowup, lem-trf-coherent-log-ideal-chart-construction, lem-trf-associated-log-universal-stalks.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VIII 3.3.8--3.3.11 and 3.3.13(i),(iii).

The parent induction is the routine part left in the assembly. The other old arguments are preserved above with their exact formulas; their conclusions, not their proof text, appear as the five new jobs. The strict-comparison job also records the canonical maps on sections and strictness of the top comparison, needed to iterate the base-change result faithfully.
