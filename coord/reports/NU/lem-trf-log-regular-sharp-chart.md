# Repair report: lem-trf-log-regular-sharp-chart

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-log-regular-sharp-chart.json`: unchanged statement; four assembly steps, 1906 characters total, status split.
- `dag/nodes/sec-trace-formula/lem-trf-chart-face-localization-logification.json`: new statement, unsplit; no Mathlib match. Localize the given fs chart at its unit face, identify both the log stalk and its characteristic, and compute the logification obtained from a supplied product splitting.
- `dag/nodes/sec-trace-formula/lem-trf-integral-monoid-free-sharpening-splitting.json`: new statement, unsplit; no Mathlib match. Split an integral monoid over its sharpening when the sharpening group has a finite basis, allowing torsion units and without assuming finite generation of the original monoid.
- `citations.json`: literal statement quotes for every node used at every parent step. The delivery command consumes this sandbox evidence.

## Attachments

None. I searched `lean/WeilConjectures/` by the item tag, sharp-chart terminology and log-regular/characteristic terminology. There is no matching project declaration there. I also read `lean/Sheaf/AlgebraicGeometry/LogRegularSharpChart.lean`, including its complete signature and proof: `AlgebraicGeometry.exists_sharp_chart_of_logRegular` ends in `sorry`, so it is not an attachment. Its signature gives precisely the fs and sharp characteristic, affine locally Noetherian pointed etale chart, and specified characteristic map of the item. The present repair changes no Lean source or Lean record.

## WANTED

None. All source passages used are present locally.

## What was wrong and what changed

This repairs the sole numbered substance of the batch5 return: 3118 characters of proof were assigned to one unfinished node. The supplied sandbox contained only dispatcher marker files, not a delivered node, report or search log. I therefore copied the current repository's complete returned five-step split as the baseline, retaining its statement, original searches, sources, blueprint ancestry, Lean audit, and existing metadata. No initial split/report was present on which to run the conditional initial dry run. The final delivery tool builds on current main; no repository git command was used.

The repair adds TWO independent unsplit nodes, rather than shortening the argument away or moving it all into one node. The chart-pushout node carries the approximately 1363-character old steps 1 and 4; the monoid-section node carries the approximately 716-character old step 3, plus makes its integral-monoid/group-quotient preliminaries explicit. These are comparable pieces of algebra, with neither depending on the other or the parent. Old steps 2 and 5 remain assembly using their original existing inputs. The explicit basis lift, landing in the positive monoid, two inverse formulas, unit pushout, inverse-image-of-units calculation, preservation of the actual characteristic identification, affine spreading, and local Noetherianity are all retained below. The two new JSON nodes have statements only, empty proof/proof_deps, and null proof_origin. Their future workers can start independently.

No STATEMENT-DISPUTED issue was found, and the item's statement is byte-for-byte unchanged. Log regularity is unused by the proof, as it was before; it remains a hypothesis. No chapter/unit route changes and no SGA source are introduced. The inherited monoidal-resolution ancestry of `lem-trf-local-term-locality` is preserved; I read the current main-20261015 locality proof and do not replace its contracting-correspondence route with this historical subargument.

## Not duplicates

I searched the whole DAG for the localization formulas, log-stalk pushouts, monoid sections and splitting/sharpening terminology; searched `blueprint_refs.py search` with `characteristic chart`, `characteristic monoid`, `sharp chart`, `log pushout`, `face localization`, `monoid section`, `monoid splitting`, and `sharpening splitting`; and inspected the relevant Lean declarations/docstrings. The imported blueprint has no equivalent of either new statement. Searches including common words produced unrelated coefficient/category-theoretic matches; these were not treated as log-geometry matches.

- lem-trf-chart-face-localization-logification vs def-trf-fs-log-blowup: the definition gives the original chart pushout by the preimage of units, but no theorem localizing that chart, identifying its characteristic with the quotient of the localization, or computing the logification of a supplied splitting.
- lem-trf-chart-face-localization-logification vs lem-trf-associated-log-universal-stalks: the latter constructs the associated-log sheaf and computes the unlocalized pushout stalk; it does not give this face-localization/characteristic identification or the effect of a splitting on its specified germ.
- lem-trf-chart-face-localization-logification vs lem-trf-fs-face-sharpening: face sharpening is pure monoid algebra; it has no chart, ring units, associated log stalk, or comparison to the characteristic of a given log structure.
- lem-trf-chart-face-localization-logification vs lem-trf-fine-log-stalk-chart-spreading: spreading ASSUMES that the prescribed germ already has the logification isomorphism. The new lemma proves that prerequisite from a supplied face splitting and makes no neighbourhood-existence claim.
- lem-trf-chart-face-localization-logification vs lem-trf-log-chart-face-tor-comparison: the existing node assumes a section and a sharp characteristic chart and concludes a Tor comparison, not the associated-log-stalk presentation. It also depends on the parent, so citing it here would be circular.
- lem-trf-chart-face-localization-logification vs lem-per-very-tame-equivariant-sharp-chart: the latter gives equivariant neighbourhood existence and a character under tame action hypotheses; it does not state the localized pushout or the conditional isomorphism for a specified splitting. We retain the nonequivariant VI 3.7(a) route instead of invoking an equivariant existence theorem.
- lem-trf-chart-face-localization-logification vs lem-trf-log-regular-sharp-chart: the new lemma starts with a chart and, conditionally, a product splitting; it gives only local algebra and neither constructs a section nor spreads a chart to an affine neighbourhood. It does not restate any existence clause of the parent.
- lem-trf-integral-monoid-free-sharpening-splitting vs lem-trf-fine-monoid-unit-splitting: the existing statement assumes the WHOLE group completion is torsion-free and identifies the units with a finite free group. The new statement permits arbitrary torsion units and need not have a finitely generated source monoid. For example R = N direct-sum Z/2 is integral and fs, has sharpening N, and meets the new hypotheses but not those of the existing node. The existing node cannot supply the old proof's splitting for this permitted fs chart.
- lem-trf-integral-monoid-free-sharpening-splitting vs lem-trf-fs-chart-free-factorization: the latter assumes a morphism of fs monoids with torsion-free group cokernel and produces an injective P direct-sum N^r submonoid with a group-completion isomorphism. It does not identify the entire monoid with its sharpening times its units, nor give the restriction of a group section to the whole sharpening. Its source also has stronger finiteness/saturation hypotheses.
- lem-trf-integral-monoid-free-sharpening-splitting vs lem-trf-fs-face-sharpening: the existing lemma proves the finite free hypothesis and identifies the units in a face localization. It does not construct the group section, prove it lands in the monoid, or give the product isomorphism.
- lem-trf-integral-monoid-free-sharpening-splitting vs lem-per-divisible-unit-lattice-extension: that node needs an n-divisible subgroup and a prescribed finite-index lattice map and constructs an extension of that lattice; none of those hypotheses is available or needed here, and it gives no monoid product decomposition.

Neither new node's source uses a Stacks tag; the only Stacks fact in the assembly remains the existing Tag 01T6 node. The listed pairs also cover the closest matches sharing the ILO VI 3.7(a) source passage.

## Mathlib searches read

The ten new searches are in `searches.jsonl` and copied with their exact tool and query text into the appropriate node. For each node I used LeanSearch, Loogle, grep, and two differently phrased LeanFinder queries. All services answered. I read their types: for chart-face-localization the hits were ordinary scheme/module stalk localizations, manifold stalks, number-field logarithmic embeddings, and a generic monoid-localization equivalence. None mentions a log structure or the required characteristic/pushout computation; the log-structure grep and Loogle searches had zero hits.

For splitting, hits included cancellative-monoid definitions, Grothendieck groups, number-field unit theorems, principal-ideal/nonzero-divisor associates equivalences, and `associatesEquivOfUniqueUnits`. I opened Mathlib/Algebra/GCDMonoid/Basic.lean around line 1013: this last equivalence assumes trivial units and a commutative monoid with zero, so it cannot handle R = N direct-sum Z/2. I read the GrothendieckGroup source: its universal lift to an existing group does not assert the section lands in the monoid or compute the sharpening kernel. Neither node is a Mathlib leaf. The original item's ten recorded searches are retained, with their actual returned types/results, since its statement and search question have not changed.

## Review by NU

I read ILO Expose VI 1.1 (printed p.69), 1.6 (p.70), and 3.7(a) (p.75), and VIII 3.1.1--3.1.5 (pp.98--99), from the local PDF. VI 1.1 supplies the etale-local fs chart convention and the unit quotient. VI 1.6 states fs sharpness and a chart modeled on the given characteristic; VI 3.7(a) writes the group exact sequence (3.a), chooses its splitting, and restricts it to a chart. The new logification statement is the algebraic expansion of those chart and splitting operations; the new integral-monoid statement isolates the basis-lift/restriction operation. I keep their source attribution as agent extractions/generalizations, not as numbered verbatim ILO theorems. For the final scheme clause I opened Stacks `morphisms.tex`, label `lemma-finite-type-noetherian`, Tag 01T6; it states precisely the locally Noetherian ascent used here.

Parent step 1 cites the fs definition for the initial local chart and the new face-localization statement for the face property, BOTH pushout and characteristic identifications, and their compatibility with the initial chart. I ensured the new lemma allows a chart on a pointed etale neighbourhood of the given point: it does not accidentally require a global chart on the original X, or silently assume local Noetherianity of an intermediate chart domain.

Parent step 2 cites the entire statement of `lem-trf-fs-face-sharpening`: it actually says R is fs, its units are F^gp, the quotient is fs sharp, and its group completion is free of finite rank. Its hypotheses are met by Q fs and F a face from step 1. The second new node then applies to the integral R with that exact unit group and finite free sharpening. It supplies the section and the product isomorphism, including the specified inclusion of units. This is why the stronger ambient-torsion-free splitting node was not usable.

Parent step 3 cites the conditional conclusion of the first new node, applied to that supplied product isomorphism. Its statement explicitly gives the trivial inverse image of ring units, the associated-log-stalk isomorphism, and the specified characteristic identification. I opened `lem-trf-fine-log-stalk-chart-spreading` and checked that it assumes exactly a finitely generated integral P and this pushout isomorphism; fs from step 2 implies fine, and an fs log structure is fine by definition. Its conclusion actually says affine neighbourhood AND germ equal to the specified h. That germ equality is what ensures the characteristic map is the prescribed identification, not merely some automorphism of P.

Parent step 4 cites `def-weil-etale-morphism`, whose statement includes locally finite presentation, and `def-sbc-locally-finite-presentation`, whose displayed finite-variable quotient presentations give local finite type directly. The existing `pqf-lem-locnoeth-lft` statement gives local Noetherianity of W because the base X is locally Noetherian. This is the already approved generic off-unit tool; I preserve its existing tool-use record and declaration in split_report rather than introduce an unapproved route. All these citations have literal copies of their used statements in citations.json, including both occurrences of the new chart lemma.

For small cases I checked the trivial log structure (F=Q, P=0, empty basis, h the identity element, logification A^times); Q=N^r with a coordinate face (localization splits off exactly the corresponding Z coordinates); Q=N direct-sum Z/2 with its unit face (torsion survives only in units, so the quotient group remains Z and the new splitting applies); and rank-zero sharpening (R is its unit group and the product formula is immediate). The new integral-monoid lemma also handles arbitrary abelian groups R with B=0, without any claim that their units are free or finitely generated. For a nonfree sharpening group the section conclusion is not asserted. I checked both inverse formulas and the exact kernel U directly. The logification statement keeps the specified maps on Q, U and A^times; no arbitrary characteristic automorphism is inserted.

Against B--E: every new object is introduced in its own statement; additive/multiplicative notation is stated; definitions are cited and all mathematical formulas use single TeX escapes. New nodes contain no proof steps or disguised proof sketch. Every non-elementary use in the parent is a cited statement, none a fact taken just from a cited proof. The new nodes are independent and cannot introduce a parent cycle. The only elementary inference left inline is finite presentation implies finite type, written using its finite generators. All parent steps are below 2000 characters. The repaired parent is below the return's total 3000-character bound and creates two real parallel work items. No statement was weakened, no compiler was run, and every file written is in the sandbox.

## Arguments assigned to the new nodes (future-worker handoff)

The first new node carries old steps 1 and 4, approximately 1363 characters before this more explicit handoff. Choose the fs chart Q at the marked point and set F to the preimage of A^times. For a,b in Q, beta(a+b) is a unit iff both beta(a), beta(b) are: inverse to a product gives inverses to its factors. Thus F is a face. The chart definition gives L = Q pushout_F A^times. Inverting F changes nothing because all its images are already units. Explicitly q-f maps to c(q)c(f)^(-1); this is well defined because the chart maps into a log monoid and equality of differences gives the same unit relation. The inverse comparison of pushouts sends a representative [q-f,u] to [q,beta(f)^(-1)u]. Hence L = Q_F pushout_F^gp A^times compatibly with the original maps. Quotienting by the A^times action gives the isomorphism Q_F/F^gp -> L/A^times. An inverse sends [q-f,u] to the class of q-f; the relations kill precisely F^gp, so both composites are identities.

Given the supplied product isomorphism (p,f) -> s(p)+f, push it out along F^gp -> A^times. On representatives [s(p)+f,u] the inverse to the resulting map P direct-sum A^times -> L sends this class to (p,beta(f)u). Moving f across the pushout relation preserves this expression; the forward map is (p,u) -> h(p)u. Thus both composites are identities. The characteristic map of h is the original canonical map, since its lift has class p. An element of P maps to a ring unit exactly when its characteristic is zero, using the log-structure axiom identifying ring units with log units. Since P=Q_F/F^gp is sharp by face sharpening, its only such element is 0. Therefore E={0}, and the associated prelog-to-log pushout P pushout_E A^times is the displayed product. This proves the entire conditional logification conclusion. This argument uses only the supplied splitting, not the existence of a section, and can be worked on independently of the second new node.

The second new node carries old step 3, approximately 716 characters, with its needed preliminaries exposed. For integral R embedded in G, U=R^times is a subgroup. Equality in B=R/U is exactly difference by U; consequently B injects into G/U. Its group completion is G/U since R generates G. Thus the map pi:G->B^gp is onto with kernel U. Choose a finite basis e_i of B^gp and choose lifts a_i in G. Define t(sum n_i e_i)=sum n_i a_i. Unique basis coordinates prove it is a group homomorphism and pi t=id, including the empty-basis case. For b in B choose r in R above b. Then t(b)-r belongs to U, so t(b)=r+(t(b)-r) lies in R. Restrict t to get j:B->R. The map (b,u)->j(b)+u has inverse r->(q(r),r-j(q(r))); the second component belongs to ker pi=U. Substitution proves both composites identity and shows the quotient is the first projection. No step assumes torsion-freeness of G or U or finite generation of R. This is the explicit basis lift and positive-monoid landing argument that the old proof performed on Q_F.

Old step 2 remains the existing fs face-sharpening statement, with all its conclusions in parent step 2; old step 5 remains prescribed-germ spreading and the finite-presentation/finite-type/locally-Noetherian calculation in parent steps 3--4. The complete returned five-step text is preserved verbatim below, so none of its arguments is lost by extraction.

## Original returned proof (verbatim)

### Old step 1

By the fs-chart definition, choose an etale-local chart $Q\to M$ through $\bar x$ with $Q$ fine saturated. Put $A=\mathcal O_{X,\bar x}$ and let $F\subseteq Q$ be the inverse image of $A^\times$. It is a face: in a commutative ring a product is a unit exactly when both factors are units, since an inverse to $ab$ gives inverses $b(ab)^{-1}$ and $a(ab)^{-1}$ to $a$ and $b$. The chart definition gives $M_{\bar x}=Q\oplus_F A^\times$. Inverting $F$ changes nothing in this pushout, since every element of $F$ already maps to a unit. Thus $M_{\bar x}=Q_F\oplus_{F^{\rm gp}}A^\times$. Quotienting this presentation by $A^\times$ identifies the given characteristic $P$ with $Q_F/F^{\rm gp}$, with the map induced by the original chart.

Uses: def-trf-fs-log-blowup.

### Old step 2

Apply the face-sharpening lemma to $Q,F$. It gives that $P=Q_F/F^{\rm gp}$ is finitely generated, integral, saturated and sharp, and that $P^{\rm gp}=Q^{\rm gp}/F^{\rm gp}$ is free of finite rank. It also gives $(Q_F)^\times=F^{\rm gp}$. These conclusions require saturation of $Q$; no ordinary regularity of $X$ is used.

Uses: lem-trf-fs-face-sharpening.

### Old step 3

Choose a finite basis $e_1,\ldots,e_r$ of $P^{\rm gp}$ and, for each $e_i$, choose a lift $a_i\in Q^{\rm gp}$ through the quotient. Define $s(\sum_i n_ie_i)=\sum_i n_ia_i$ for integers $n_i$. Uniqueness of the basis expression makes $s$ a group homomorphism and the quotient composed with $s$ is the identity. For $p\in P$ choose $q\in Q_F$ representing $p$. Then $s(p)-q\in F^{\rm gp}$, which is the unit group of $Q_F$. Hence $s(p)\in Q_F$. This constructs a monoid section $s|_P:P\to Q_F$. In fact $(p,f)\mapsto s(p)+f$ is an isomorphism $P\oplus F^{\rm gp}\to Q_F$: its inverse sends $q$ to $(\bar q,q-s(\bar q))$, whose second component belongs to $F^{\rm gp}$. Both composites are identities by these formulas.

Uses: lem-trf-fs-face-sharpening.

### Old step 4

Push this isomorphism out along $F^{\rm gp}\to A^\times$. The formulas give an isomorphism $P\oplus A^\times\to M_{\bar x}$ sending $(p,u)$ to $h(p)u$, where $h$ is $s|_P$ followed by $Q_F\to M_{\bar x}$. On the quotient by units the map induced by $h$ is the identity of the specified $P$. Its inverse image of $A^\times$ is therefore $\{0\}$: a germ mapping to a ring unit lies in the unit subgroup of the log structure, and $P$ is sharp. Consequently the log structure associated to the prelog map $P\to A$ is exactly $P\oplus A^\times$, and the displayed map is the stalk logification isomorphism required for chart spreading.

Uses: def-trf-fs-log-blowup, lem-trf-fs-face-sharpening.

### Old step 5

Apply the fine-log stalk-chart spreading lemma to $h$. The source monoid is fine by step 2 and the required logification isomorphism was proved in step 4. It produces an affine pointed etale neighbourhood $W$ and a chart with precisely this germ. Its characteristic map at $\bar w$ is consequently the chosen identification with $P$, not an unspecified automorphism. Finally $W\to X$ is locally of finite presentation by the etale definition. Its affine algebra presentations have finitely many generators, so it is locally of finite type. As $X$ is locally Noetherian, apply the locally-Noetherian finite-type lemma (Stacks Tag 01T6, morphisms-lemma-finite-type-noetherian) to conclude that $W$ is locally Noetherian.

Uses: lem-trf-fine-log-stalk-chart-spreading, def-weil-etale-morphism, def-sbc-locally-finite-presentation, pqf-lem-locnoeth-lft.

## What remains unfinished

The two new statements are intentionally unsplit for other workers. There are no unresolved mathematical gaps in the parent assembly. This delivery proves no Lean theorem and does not claim to remove any sorry. The dry-run and push results are recorded after running the required tools.

## Validation

The required deliver.py --no-push run exited 0 and printed OK (not pushed) at 632ff043c26, with server preflight passed. A local literal-substring check verified every citations.json entry against the current cited statement, and the parent statement is unchanged. After correcting the report search-count typo, the final dry run is repeated before pushing.
