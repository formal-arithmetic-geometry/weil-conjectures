# Q51 repaired stage-1 delivery

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-dvr-nodal-chart-blowup-calculus.json: retained statement, statement dependencies, Q17 Lean record and all other live metadata; replaced proof by six assembly steps (2052 characters).
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-trait-curve-local-properties.json: statement-only, status unsplit, no Mathlib match; added in this repair.
- dag/nodes/sec-six-functors-basics/lem-sfb-binomial-blowup-chart-algebras.json: statement-only, status unsplit, no Mathlib match; added in this repair.
- dag/nodes/sec-six-functors-basics/lem-sfb-monomial-local-completion.json: statement-only, status unsplit, no Mathlib match; retained from the returned delivery.
- dag/nodes/sec-six-functors-basics/lem-sfb-flat-pullback-blowup-chart-restrictions.json: statement-only, status unsplit, no Mathlib match; added in this repair.
- dag/nodes/sec-six-functors-basics/lem-sfb-etale-stalk-invariants.json: statement-only, status unsplit, no Mathlib match; retained from the returned delivery.
- dag/nodes/sec-six-functors-basics/lem-sfb-regular-hypersurface-initial-form.json: statement-only, status unsplit, no Mathlib match; retained from the returned delivery.
- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-three-chart-gluing.json: statement-only, status unsplit, no Mathlib match; added in this repair.
- dag/nodes/sec-six-functors-basics/lem-sfb-binomial-laurent-normal-form.json: statement-only, status unsplit, no Mathlib match; retained from the returned delivery.
- dag/nodes/sec-six-functors-basics/lem-sfb-three-chart-exceptional-curve.json: statement-only, status unsplit, no Mathlib match; added in this repair.
- dag/nodes/sec-six-functors-basics/lem-sfb-dvr-binomial-local-geometry.json: statement-only, status unsplit, no Mathlib match; added in this repair.
- dag/nodes/sec-six-functors-basics/lem-sfb-binomial-geometric-fibres.json: statement-only, status unsplit, no Mathlib match; added in this repair.
- citations.json: one exact statement quotation for every cited node in every assembly step.
- report.md: this report. Searches and result files are retained, including searches.jsonl; no recorded search was invented or repeated without a changed search question.

## Attachments

None. The live WeilConjectures source was searched for the item tag, nodal blowup terms, and smooth relative curves. No finished declaration states all clauses of the item or any complete new statement. The existing Q17 Lean record is preserved; its sorry statements are not attachments.

## WANTED

WANTED: literature/de-jong-families-curves-alterations-1997.pdf, Lemma 3.13, printed p.609. The local archival PDF remains absent. I reopened the publisher PDF https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf; the explicit algebra below is agent work and the source references do not pretend de Jong wrote these detailed calculations.

## What was wrong and what this repair changes

The returned version extracted four generic lemmas but compressed the main blowup and smooth-curve work. The maintainer correctly identified that base steps 5 and 7--13 had not been spread into independent work. This repair adds seven more statement-only nodes. It expressly retains the overlap derivation, both overlap monomial formulas, the conic X,Y-cover and characteristic-two smoothness, restriction of the canonical flat comparison to each chart, and the strict special-fibre prime chain. Every argument in the fifteen-step base proof is mapped below, and its complete text is retained in the final appendix as takeover material. The item statement is unchanged, so no statement dispute or source correction is claimed. No Lean, compiler, Lake or repository mutation was used.

The four retained nodes remain sound on the edge cases identified by the maintainer. The hypersurface initial-form node is retained for its graded-ring and cotangent statements, beyond the existing one-way regular-hypersurface criterion and dimension-drop lemma. The new nodes are extracted subarguments, none is the whole DVR nodal blowup calculus. In particular H constructs charts but gives no regularity, G assumes a chart cover but proves its geometric properties, E is a field-level gluing theorem with no blowup, and T is a general chartwise flat-comparison theorem with no nodal equation. The explicit re-split order calls for S and L even though the item itself contains their specialized conclusions.

## Search and duplicate audit

I reused the four retained nodes' search results after reading them. For the seven further nodes I ran the 35 exact queries in planned_repair_searches.json through the prescribed msearch.py: LeanFinder twice with different formulations, Loogle, source grep and LeanSearch for each node. All 35 services returned OK, including the queries with zero hits. Their unedited outputs are in each node's search-results file and in mathlib_searches, with the queries matching searches.jsonl. Weierstrass coordinate rings concern a different equation; their point-ideal quotient is not the crossing-axis fibre product. SmoothOfRelativeDimension and standard smooth presentation results give tools, not trait normality and local dimension. Krull-dimension quotient results do not identify these local models. Proj.pullbackAwayιIso compares overlaps in a fixed Proj, not flat base change of the Rees algebra and the actual extended ideal. Rees tensor Noetherianity supplies no chart isomorphism. Thus no full match or one-line specialization was found; all eleven new nodes are unsplit, zero Mathlib leaves.

Before creating the seven nodes I searched the whole DAG by nodal/binomial/conic/smooth-relative-curve/blowup-chart and flat-comparison terms, opened the candidate statements, and ran blueprint_refs.py search for blowup, nodal, conic, smooth relative dimension, regular, flat base, binomial and reciprocal. The blueprint contains general blowup/chart interfaces and unrelated smoothness and reciprocal-root statements, but not these computations. The blueprint ancestor tool returns node=None for this created-node chain; new blueprint fields retain that result and the full inherited via list, prefixing this item, and specify the exact base proof argument served. No chapter or unit route changed.

## Retained four-node source and edge-case audit

For lem-sfb-binomial-laurent-normal-form I read algebra.tex Tag 030A (polynomial normality) and Tag 00GY (normality of localizations). The additional algebra is an agent coefficient argument, not a claimed quotation of either tag. Reduction of each mixed monomial by xy=a gives the stated basis: the single monic rewriting relation has no competing overlap, also when R has zero divisors or a=0. For a nonzero in a domain, substitution into K[T,T^-1] separates the pure x and pure y coefficients and proves injectivity. A coefficient of T^-j in the intersection must belong to a^j R; positive coefficients belong to R. This gives exactly R[T,a/T], not the whole Laurent algebra. Each Laurent ring is normal by the cited tags; any element of their common fraction field integral over the intersection lies in both. The domain, nonzero-a, and normality hypotheses are used only for these latter clauses. Tests include a=0 (basis still valid, domain assertion deliberately absent), a a unit (the algebra is Laurent), n=1, and non-Noetherian normal R. No cancellation by a is used in the arbitrary-ring basis clause.

For lem-sfb-monomial-local-completion I read Tag 0315 (completion generalities). This is an agent coefficientwise inverse-limit calculation, not a statement that Tag 0315 itself contains this formula. In P/(J+(T)^N), exactly the monomials of degree <N outside the upward closure D survive. Every polynomial outside the coordinate maximal ideal has nonzero constant term and is invertible in this finite quotient by the finite geometric-series formula, so localization leaves this quotient unchanged. Compatible truncations specify one coefficient at every surviving monomial. In the formal power-series ring, a series supported on D lies in the finitely generated monomial ideal: partition D by the first generator dividing a monomial, then factor that generator from the corresponding subseries. This proves the kernel equality as well as the isomorphism. Finite generation of J is relevant to that last finite sum. Tests: r=0 and empty list give k, J=0 gives the usual power series ring, J=(T) gives k, J=(T^2) retains nilpotents, and J=(xy) gives precisely the two branches needed here. No reducedness or regularity assumption is smuggled into the completion statement.

For lem-sfb-etale-stalk-invariants I read more-algebra.tex Tags 07QP (dimension of an etale extension) and 0AH0 (regularity of an etale extension), and algebra.tex Tags 033C/033G (normal ascent/descent). The scheme-stalk assembly is agent work. Choose an affine etale presentation near u, then base change it to A=O_X,x and localize at the point inducing u. This is the localization of an etale A-algebra; its map A to B is local and flat, hence faithfully flat. Apply the cited local etale dimension and regularity results, including their descent direction. If A is normal, the base-changed etale algebra is normal by 033C and so is its prime stalk B; if B is a normal domain, faithfully flat descent gives normality of A by 033G. This never assumes the entire original affine neighbourhood of x is normal. There is no global Noetherian hypothesis: if a regularity side holds it supplies the local Noetherian condition, while the normal-domain statement does not require one. Tests include a finite separable nontrivial field extension, a localization/open immersion, and etale maps of non-Noetherian normal schemes. Residue fields can extend; they are not identified. This is a nontrivial local comparison with two descent directions, not a restatement of normality under global smooth ascent.

For lem-sfb-regular-hypersurface-initial-form I read algebra.tex Tags 00NO (the graded ring of a regular local ring) and 00KW (quotient by one equation); I also read 00NR/00NQ for comparison. The new content beyond a regularity criterion is the filtered principal-ideal calculation. In a regular local ring the maximal-adic filtration is separated and its graded ring is a polynomial domain. Thus every nonzero f has finite order e; products have additive order and initial forms multiply. Consequently the initial ideal of (f) is generated by F, yielding gr(B)=gr(A)/(F). Its degree-one part loses one dimension exactly when e=1; otherwise it loses none. The dimension drop gives dim B=d-1 and the final iff. Tests: a parameter, its square, xy over k[x,y]_(x,y), xy-pi^2 in mixed characteristic, and characteristic two. The hypothesis f nonzero and in m excludes f=0 and units; d=0 consequently has no admissible f. No coefficient field or completion of A is assumed.


## Further-node sources, arguments and edge cases

For lem-sfb-binomial-geometric-fibres I read algebra.tex Tags 00T6/00T7 and curves.tex Tag 0C59. None is being cited as a theorem about connectedness of these particular rings. The restriction homomorphism for a=0 is injective by the basis 1,x^i,y^j; its image consists exactly of pairs with equal constants. Thus no nilpotents survive and the two components meet as the quotient by (x,y), namely k. Primes contain x or y and consequently lie on a polynomial line; at the origin (x) is strictly below (x,y). For a nonzero substitute y=a/x to get the Laurent line. Smoothness of each punctured axis and Laurent line follows from polynomial or UV-1 standard smooth presentations, with unit derivative; the crossing is nonsmooth since its cotangent space has dimension two versus local dimension one. Base extension preserves all displayed rings and maps. I tested a=0, a=1, imperfect fields and characteristic two; the statement does not incorrectly call the crossing normal or irreducible.

For lem-sfb-dvr-binomial-local-geometry I read algebra.tex Tags 00FN, 00ON, 00PD, 00KU, 0AFS and 07NF and the cited valuation-flatness reference. The normal-form basis makes the algebra torsion-free over the DVR, and hence flat. A DVR is a Noetherian PID and the quotient is finite type, so all local dimension formulas apply to Noetherian rings. The fibre term is at most one by F. At the origin it is exactly one by the explicit chain (x) strictly contained in (x,y) in k[x,y]/(xy), and the base term is one, giving total dimension two. Laurent opens cover the complement because a prime containing x,y contains pi. Their smooth presentations over the regular DVR give regularity. The ambient localization P is regular by smooth ascent and localization; reducing pi,x,y successively modulo the other two proves the cotangent basis, hence its dimension is three. For n=1 the initial form is -Pi; for n=2 it is XY-Pi^2, and for n>2 it is XY. These remain nonzero in characteristic two. Apply D to get the exact cotangent dimension and regularity iff. Tests n=1,2,3, generic points, height-one special-fibre points, mixed characteristic and noncomplete DVRs show that neither equality two at all points nor regularity at n=2 was accidentally asserted.

For lem-sfb-smooth-trait-curve-local-properties I read algebra.tex 07NF and 00ON and the smooth affine-local convention. The regular DVR and its localizations give a regular base. Smooth affine charts are regular by ascent, and regular rings are normal. Smoothness gives flatness and local finite presentation, so the charts are Noetherian. The flat height formula has base term zero or one and fibre term at most one. At a closed fibre point, purity one forces the component generic point to be distinct from that closed point; it supplies a length-one chain. Thus the fibre-local dimension is exactly one there. This reasoning is local on X and assumes no finite affine cover. I tested X empty, empty special fibre (a smooth K-curve viewed as an R-scheme), disjoint unions, the affine line and its generic and closed special points. Normality is stalkwise and no global integrality or connectedness is claimed.

For lem-sfb-binomial-blowup-chart-algebras I read divisors.tex Tag 0804, including its homogeneous-generator proof, and the Proj and chart definitions. In A[I/x] set t=a/x; mixed substitution gives xt=a, y=x^(n-1)t^n, y/x=x^(n-2)t^n, so x,t generate. Embed R[x,t]/(xt-a) in Frac(R)(x) by A to prove no further kernel. The middle is generated by r=x/a,s=y/a with rs=a^(n-2); its injection is the same binomial normal form after scaling x. This explicitly includes n=2 and rs=1, rather than a negative exponent. The y-chart is symmetric. Inside D_+(bT), the homogeneous fraction cT/(bT)=c/b determines the second open, so its intersection with D_+(cT) is D(c/b). On x--a this gives r=1/t and s=x^(n-2)t^(n-1); on y--a it gives s=1/h and r=y^(n-2)h^(n-1). The x--y overlap is D(y/x)=D(x^(n-2)t^n). Extension of I is (x),(a),(y) in the three charts: in each one all generators are multiples of the distinguished generator, and that generator is present. Quotienting yields the three exceptional rings in H. For n>2 the outer overlap vanishes on this quotient; for n=2 it is D(t), with h=1/t, equal to the middle hyperbola. I tested n=2,3,4, a a unit (the centre is empty and all extended ideals are units), and a a nonzero nonunit in a non-Noetherian domain. The nonzero and domain hypotheses are precisely those needed for fraction embeddings; no false cancellation in an arbitrary non-domain is used.

For lem-sfb-nodal-three-chart-gluing I read curves.tex 0C59/0C5A and the actual nodal-fibre definition, which adds nonemptiness and connectedness beyond at-worst-nodal. The outer charts are exponent-one models, the middle is exponent n-2 for n>2, and at n=2 it is a smooth Laurent line. Local flatness and finite presentation glue on this finite chart cover. Generic fibres identify on their whole Laurent charts. For the special fibre the three affine pieces have equations xt=0, rs=0 or rs=1, and yh=0. Each is connected and its overlaps with the middle are nonempty: for n>2 they are punctured middle axes; for n=2 the middle is the hyperbola. Their union is therefore connected. The coordinate descriptions persist over an algebraic closure. Each local singularity is within one chart, giving exactly nodal completions and no hidden singularity from gluing. L classifies all nonregular total-space stalks: both outer charts are regular, and only the middle origin is nonregular when n>=4. I tested n=2,3 (regular total spaces), n=4 (one M_2 singularity), and arbitrary residue characteristic. Connectedness was not inferred from flatness alone.

For lem-sfb-three-chart-exceptional-curve I read the quotient and gluing source around divisors.tex 0804 and the standard projective-line definition. At epsilon=1 the middle hyperbola is precisely the overlap, so the outer lines glue by h=1/t to P1. In homogeneous coordinates [X:P:Y] the maps [1:t:t^2], [r:1:s], [h^2:h:1] satisfy XY=P^2 and agree on both overlaps. On D_+(X) the conic has coordinates P/X=t,Y/X=t^2 and on D_+(Y) it has P/Y=h,X/Y=h^2; these are inverse affine maps. These two opens cover: a homogeneous prime containing X,Y would also contain P and so be irrelevant. Thus both opens are affine lines and prove smoothness in characteristic two without using the derivative 2P. At epsilon=0 the two middle axes complete separately with their outer line to P1 by reciprocal gluing. They meet only at the origin with quotient k, and the absent outer overlap gives no extra intersections. All rings are reduced. Field extension commutes with every presentation and map. I tested epsilon=0, epsilon=1, finite/imperfect fields, characteristic two and algebraic closure; the statement includes the actual reduced scheme intersection, not just its underlying point set.

For lem-sfb-flat-pullback-blowup-chart-restrictions I read the proof of divisors.tex 0805 and its affine generator argument 0804. On affine charts flat tensoring identifies B tensor I^d with (IB)^d in every degree, including zero, so the graded Rees comparison sends each aT to phi(a)T. Its Proj isomorphism therefore preserves D_+(aT) and restricts to the claimed fraction-algebra map b tensor(c/a) -> b phi(c)/phi(a). Localizing at a'/a gives the overlap map with the same fraction formula; extension of the ideal is generated by the corresponding images of I and is respected. Taking the fibre of the Cartesian square and reassociating fibre products gives exactly extension of the original exceptional fibre from kappa(x) to kappa(y). For an etale map the fibre over a closed x is a disjoint union of spectra of finite separable fields by the already existing etale-fibre node. The complement of the chosen singleton is closed in this closed fibre, hence closed in Y. Removing it leaves the scheme-theoretic inverse image precisely Spec kappa(y), not a nonreduced thickening. For a common pointed neighbourhood do this for both closed points and intersect the resulting open neighbourhoods. Tests include the identity, an open immersion, a nontrivial finite separable residue extension, an empty chart (zero generator), a unit ideal (empty centre), and a nonreduced ambient scheme. No arbitrary-base-change assertion was substituted for flat base change, and no residue fields were silently equated.

## Review by Q51

I read the item source, the fifteen base steps, all eleven new statements, the relevant Stacks source text and every statement cited in the six new assembly steps. I compared the sandbox item to current live main: only proof, proof_deps and split_report differed before this repair, and the repair again preserves statement, stmt_deps and the Q17 Lean record. I used the released repair note despite the live split status, as the brief requires.

In assembly step 1, A states the injective normal binomial quotient and normality of every prime localization. The DVR hypothesis gives the nonzero normal coefficient domain needed at a=pi^n. L states Noetherianity, flatness and finite presentation for precisely that DVR equation. The integral-scheme definition says a nonempty domain spectrum is integral; no smooth-ascent theorem is being read out of that definition.

In assembly step 2, F states both fibre equations' geometry after any field extension, including nonemptiness and connectedness, their dimensions, and their smooth complements. B explicitly identifies the completed local quotient, its kernel and compatible truncations; apply it at the crossing with the two variables and J=(xy), over Omega. The nodal-fibre definition asks exactly for these completed local rings at nonsmooth points, as well as the finite presentation already provided by L. This fixes the former reliance on an uncited completion or a weaker at-worst-nodal definition.

In assembly step 3, L supplies the regular ambient local ring P, dimension three, its cotangent basis and the initial forms at each exponent. D says both the graded quotient and the regularity iff for nonzero f in the maximal ideal. Thus its hypotheses hold and the order-one case is exactly n=1. L also supplies the bound two and equality at o, with the explicit special-fibre chain in F and the retained argument above. S states every smooth pure-relative-curve conclusion used, with no properness or nonempty-fibre hypothesis. These are statements of cited nodes, not internal arguments borrowed from their proofs.

In assembly step 4, H is applied with domain R, nonzero a=pi, n>=2, exactly its hypotheses. Its statement contains the injective presentations, their covering assertion, structure maps, full overlap formulas and centre ideals. G assumes just that cover with those same transitions, and concludes flatness, connected reduced nodal geometric fibres and the exact nonregular-point classification. Its middle rs=1 convention at n=2 is explicit. No chart flatness or connectedness is left as an unlabelled inline argument in the item.

In assembly step 5, H gives the quotient rings and their restrictions for the actual extended ideal. E takes exactly that gluing data, epsilon=1 or zero, and states the conic maps, X,Y-cover, characteristic-two smoothness, projective-line identifications and reduced intersection. Its field-extension compatibility gives the geometric exceptional fibre. The existing affine-complement theorem says the blowup is an isomorphism off V(I), here the singleton o. The two nodes are independent subarguments: H computes the blowup algebra but does not prove the field-level gluing classification; E assumes a gluing and does not construct a blowup.

In assembly step 6, the etale definition supplies flatness, so T's comparison applies. T states precisely that the canonical isomorphism restricts to every distinguished chart, respects fractions on overlaps and extends the exceptional fibre along the actual residue-field map. C gives normality and regularity equivalences, dimension equality and faithful flatness for each etale stalk map, so apply it to both legs. The existing etale-fibre theorem states discreteness and a reduced finite-separable field singleton for each fibre point. Since the points downstairs are closed, removing other fibre points gives an open neighbourhood with exactly the reduced point as centre; intersect for the two maps. This last two-line use reuses the existing node as the maintainer explicitly allowed for base step 15. No two different residue fields are identified.

I checked delivery-errors B through E point by point. New statements introduce all data and their notion nodes, contain no proofs, have empty proof/proof_deps, and carry source labels and the prescribed searches. The main proof uses only exact cited statements, with quotes in citations.json; its proof_deps is their union. It contains no long step or hidden diagram comparison. The seven further nodes are not elementary one-line facts: each carries a substantive chart, local dimension, gluing or restriction argument the return explicitly requested. No circular reference to a downstream nodal-blowup descent or projective-fibre node is used. Every argument in the original proof has a named home in the mapping below; the short assembly has not discarded the longer work. I retained the four original node statements and their searches and checked their edge cases again. No target statement, definition or route was weakened, and no SGA source is cited.

## Landing-refusal repair of b44c0919fb7

The 2026-10-22 12:30 UTC return approved the mathematics and refused the landing because the project's completed side DAG had not been promoted to the live DAG read by the queue. I followed that return by continuing the retained eleven-node delivery, rather than replacing it with the live fifteen-step proof. I compared the retained returned files with the current read clone: the item differs only in proof, proof_deps and split_report; all eleven auxiliary nodes are still absent there. The live statement, statement dependencies, Q17 Lean record, source, blueprint and maintainer metadata agree and are preserved. The released keep_plan repair note still requires the re-split, so the old passing review does not discharge it.

I re-opened all current external assembly citations: def-pc-integral-scheme, def-trf-nodal-geometric-fibres, def-weil-etale-morphism, lem-weil-pbc-etale-fibre-discrete-separable-points and lemma-nagata-affine-blowup-complement. The first gives integrality of the nonempty domain spectrum; the second requires connectedness, dimension one and the completed crossing equation; the third supplies flatness; the fourth gives reduced separable-field singletons in discrete fibres; the fifth supplies precisely the complement isomorphism. Their current statements still contain every exact quotation in citations.json. I also re-read all eleven retained auxiliary statements and their actual edge-case qualifications, together with Stacks 0804/0805, 030A/00GY, 0315, 00NO/00KW, 07QP/0AH0, 033C/033G and 02GL. None of the cited statements requires changing the approved split or repeating a search question.

I adjusted assembly step 6 to spell out the ambient-open shrinking: a fibre singleton is open and reduced, an ambient open induces that singleton, and its inverse-image centre is the actual reduced point. This addresses the only place where the retained assembly could conceal which scheme structure was used. It leaves both residue-field extensions intact and adds no new assumption or dependency. All fifteen original arguments, the eleven statement-only nodes, their source and duplicate audit, the search logs and exact citation quotes are retained. landing-repair-citation-audit.json records the statements rechecked at this repair. The initial required dry run terminated successfully at 1096583a212; the final dry run below is run again after these report and assembly changes. Delivery uses deliver.py's current origin/sheaf-dag base; no repository git command or side-DAG promotion is performed by this worker.

## Base proof coverage

- Base step 1: lem-sfb-binomial-laurent-normal-form.
- Base step 2: lem-sfb-dvr-binomial-local-geometry.
- Base step 3: lem-sfb-binomial-laurent-normal-form.
- Base step 4: lem-sfb-binomial-geometric-fibres, lem-sfb-monomial-local-completion.
- Base step 5: lem-sfb-dvr-binomial-local-geometry, lem-sfb-binomial-geometric-fibres.
- Base step 6: lem-sfb-dvr-binomial-local-geometry, lem-sfb-regular-hypersurface-initial-form.
- Base step 7: lem-sfb-smooth-trait-curve-local-properties.
- Base step 8: lem-sfb-binomial-blowup-chart-algebras.
- Base step 9: lem-sfb-nodal-three-chart-gluing.
- Base step 10: lem-sfb-binomial-blowup-chart-algebras.
- Base step 11: lem-sfb-three-chart-exceptional-curve.
- Base step 12: lem-sfb-three-chart-exceptional-curve.
- Base step 13: lem-sfb-flat-pullback-blowup-chart-restrictions, lemma-nagata-affine-blowup-complement.
- Base step 14: lem-sfb-etale-stalk-invariants.
- Base step 15: lem-sfb-flat-pullback-blowup-chart-restrictions, lem-weil-pbc-etale-fibre-discrete-separable-points.

The generic source lemmas used to prove these new statements remain takeover inputs in their source annotations and the retained base proof below; they are not falsely classified as Mathlib leaves. The existing etale-fibre result legitimately replaces the finite-zero-dimensional-ring derivation in base step 15.

## Not duplicates

lem-sfb-monomial-local-completion vs lem-weil-pbc-finite-over-complete-ring: This is finite generation of a module over a complete ring from its reduction, not the explicit localized monomial quotient completion and kernel.

lem-sfb-monomial-local-completion vs lem-weil-pbc-complete-source-surjective-mod-ideal: This is surjectivity of a complete-source map from a surjective reduction, not an isomorphism identifying its monomial kernel or local quotient.

lem-sfb-monomial-local-completion vs lem-weil-pbc-cohen-structure-power-series-surjection: This gives a Cohen coefficient-ring power-series surjection; it does not identify the explicit monomial kernel, localization comparison or compatible truncations.

lem-sfb-etale-stalk-invariants vs lem-sbc-stalk-normalization-boundary-dimension-two: This concerns boundary dimension in a finite normalization pullback with depth hypotheses, not arbitrary etale stalk normality/regularity equivalences.

lem-sfb-etale-stalk-invariants vs lem-sbc-trait-etale-extension: This extends a cover across a punctured normal trait by normalization; it is not an invariant comparison at arbitrary etale stalks.

lem-sfb-etale-stalk-invariants vs lem-sbc-stalk-normalization-normal-part: This proves normality of a relative-normalization pullback over a normal base; it does not give both directions at a specified arbitrary base stalk, regularity or dimension equality.

lem-sfb-etale-stalk-invariants vs lem-sbc-dvr-generic-galois-normalization: This constructs the finite normal normalization for a generic Galois cover over a DVR after base change, not general etale stalk equivalences.

lem-sfb-etale-stalk-invariants vs new-stalk-normalization-boundary-dimension-two-transfer: This transfers a dimension-at-least-two condition through finite normalization, not equality of etale stalk dimensions together with regularity/normality.

lem-sfb-etale-stalk-invariants vs lem-sfb-faithfully-flat-normal-ring-descent: This is one-way faithfully flat descent of normality; it has no etale normal ascent, regularity equivalence, dimension comparison or scheme-stalk construction.

lem-sfb-etale-stalk-invariants vs lem-sfb-galois-component-presentation: This presents geometric components of proper normal varieties using finite Galois fields, not arbitrary etale local-ring invariants.

lem-sfb-etale-stalk-invariants vs lem-sfb-dvr-nodal-chart-blowup-calculus: The item treats explicit DVR nodal surfaces and their blowups; the new lemma instead compares arbitrary etale scheme stalks, without a DVR, curve or blowup hypothesis, and does not supply any model calculation.

lem-sfb-etale-stalk-invariants vs lem-per-faithfully-flat-normal-ring-descent: This is normal descent along an arbitrary faithfully flat ring map, not etale normal ascent or regularity/dimension comparison at scheme stalks.

lem-sfb-etale-stalk-invariants vs lem-per-ind-etale-regular-coordinate-locus: This concerns an open regular coordinate locus over a quasi-excellent Noetherian base and its ind-etale pullback; it does not state unrestricted individual normal-stalk equivalences.

lem-sfb-etale-stalk-invariants vs lem-weil-pbc-smooth-over-normal-ring-normal: This is global smooth ascent from an entirely normal base ring; it does not compare normality at one arbitrary base stalk in both directions or compare dimensions and regularity.

lem-sfb-etale-stalk-invariants vs lem-weil-pbc-etale-colimit-normal-local-domain: This handles injectivity and normality of a filtered etale colimit over a normal domain; it gives no arbitrary scheme-stalk iff or regularity/dimension comparison.

lem-sfb-etale-stalk-invariants vs lem-weil-pbc-smooth-normal-domain-approximation: This approximates a smooth algebra by Noetherian normal base models, rather than asserting the local normality/regularity/dimension equivalences.

lem-sfb-etale-stalk-invariants vs lem-weil-pbc-normal-finite-type-subalgebra-extension: This enlarges a finite-type integral subalgebra to a normal one; it has no etale stalk comparison.

lem-sfb-etale-stalk-invariants vs lem-weil-pbc-finite-type-z-domain-normalization-finite: This is finiteness of integral closure for a finite-type Z-domain, not invariance under an etale stalk map.

lem-sfb-etale-stalk-invariants vs lem-weil-pbc-directed-subalgebra-ring-colimit: This identifies a directed ring-colimit of subalgebras; it does not assert these local invariants.

lem-sfb-etale-stalk-invariants vs lem-weil-pbc-normal-ring-field-extension-descent: This descends normality after a field extension; it does not give etale ascent, scheme-stalk assembly, regularity or dimension equality.

lem-sfb-etale-stalk-invariants vs lem-weil-pbc-directed-subalgebra-tensor-colimit: This identifies a tensor product with a directed subalgebra colimit, without the etale local invariant comparisons.

lem-sfb-etale-stalk-invariants vs lem-weil-pbc-etale-over-normal-ring-normal: This is global normal ascent for an etale algebra over a normal ring; the new statement requires localizing after base change to a specified base stalk and gives descent, regularity and dimension too.

lem-sfb-etale-stalk-invariants vs lem-fin-etale-normal-components: This is a finite clopen decomposition of a Noetherian normal scheme into integral components, not arbitrary etale stalk comparison.

lem-sfb-etale-stalk-invariants vs lem-sc-divisor-exact-sequence: This is an etale-sheaf divisor exact sequence on a proper curve; sharing a normality source tag does not make it a local-ring invariant theorem.

lem-sfb-etale-stalk-invariants vs lem-sc-etale-local-dimension: This gives only dimension equality for etale ring localizations, not faithful flatness, the two normal/regular equivalences or their scheme-stalk assembly.

lem-sfb-regular-hypersurface-initial-form vs lem-sbc-depth-two-punctured-principal-slice-connected: This is connectedness of a punctured principal slice using depth, not the initial ideal and graded ring of an arbitrary regular hypersurface.

lem-sfb-regular-hypersurface-initial-form vs lem-zl-bertini-finite-cover-irreducible-system: This is a Bertini statement for linear systems and finite covers, not the local filtered principal-ideal computation.

lem-sfb-regular-hypersurface-initial-form vs lem-sc-regular-local-domain: This asserts that a regular local ring is a domain; it does not compute the graded ring of a hypersurface quotient or its cotangent dimension.

lem-sfb-regular-hypersurface-initial-form vs lem-sc-effective-cartier-affine-dimension-drop: This gives dimension drop for an effective Cartier equation over a field, not an arbitrary mixed-characteristic regular local graded quotient.

lem-sfb-regular-hypersurface-initial-form vs lem-sc-principal-quotient-dimension-full-height: This gives dimension drop under full-height hypotheses, without the associated graded quotient or cotangent/regularity criterion.

lem-sfb-regular-hypersurface-initial-form vs lem-weil-pbc-global-complete-intersection-local-regular-sequence: This produces local regular sequences for field-polynomial complete intersections, not an arbitrary regular-local initial-form computation.

lem-sfb-regular-hypersurface-initial-form vs lem-weil-pbc-noetherian-height-quotient-bound: This gives a height inequality in a Noetherian quotient; it does not identify the graded quotient or embedding dimension.

lem-sfb-regular-hypersurface-initial-form vs lem-weil-pbc-regular-sequence-dimension-at-point: This computes dimensions for regular sequences in polynomial algebras over a field, not the general regular-local initial-form theorem.

lem-sfb-regular-hypersurface-initial-form vs lem-weil-pbc-global-complete-intersection-equidimensional: This gives equidimensionality of field-polynomial complete intersections, not the local associated graded computation.

lem-sfb-regular-hypersurface-initial-form vs lem-weil-pbc-polynomial-quotient-dimension-lower-bound: This is a dimension lower bound for polynomial quotients over a field, not the regular-local graded quotient and cotangent calculation.

lem-sfb-regular-hypersurface-initial-form vs lem-weil-pbc-dimension-quotient-nonzerodivisor: This supplies the dimension drop only; it does not give gr(A/(f)), the initial ideal, or cotangent dimensions.

lem-sfb-regular-hypersurface-initial-form vs lem-sc-tsen: This is the C1/Brauer-vanishing theorem for a curve function field; the shared algebra tag does not state a hypersurface initial-form theorem.

lem-sfb-binomial-laurent-normal-form vs lem-trf-basis-cone-polynomial-normal: This identifies a basis-cone monoid algebra over a field with a polynomial ring; it has no arbitrary-base binomial deformation or two-Laurent-ring intersection.

lem-sfb-binomial-laurent-normal-form vs lem-trf-normal-polynomial-surjection: This provides a polynomial-ring surjection from a normal Z-algebra, not normality or the coefficient basis of a binomial quotient.

lem-sfb-binomial-laurent-normal-form vs lem-trf-finite-monic-polynomial-divisors: This proves finiteness of monic polynomial divisors over a field, not a binomial normal form over an arbitrary ring.

lem-sfb-binomial-laurent-normal-form vs lem-weil-pbc-polynomial-ring-normal-domain: This proves normality of a polynomial ring over a normal domain; xy-a is a quotient, and the new statement identifies it with an intersection before applying polynomial normality.

lem-sfb-binomial-laurent-normal-form vs lem-weil-pbc-localization-normal-domain: This preserves normality under localization of an already normal domain; it does not prove the binomial ring normal or identify its Laurent intersection.

lem-sfb-binomial-laurent-normal-form vs lem-pur-polynomial-field-pid: This is the PID property of a univariate polynomial ring over a field, not the arbitrary-base binomial quotient or intersection computation.

lem-sfb-regular-hypersurface-initial-form vs lem-weil-pbc-regular-local-hypersurface-criterion: The existing theorem gives the regularity implication for f outside m^2. The new theorem computes the associated graded quotient and both cotangent cases, and hence also supplies the converse; this is not a one-line specialization of that criterion.

lem-sfb-regular-hypersurface-initial-form vs lem-weil-pbc-regular-local-quotient-independent-generators: The existing result infers independent generators from an already regular quotient; it does not compute the initial ideal or graded quotient of an arbitrary f.

lem-sfb-monomial-local-completion vs lem-trf-homogeneous-continuous-formal-division: Formal division under the stated basis hypotheses does not identify the local polynomial quotient completion or its finite truncation maps.

lem-sfb-monomial-local-completion vs lem-trf-monoid-completion-coefficients: The existing completion is for a monoid embedded in a free abelian group; the quotient by xy has zero divisors and cannot be identified with that integral monoid algebra.

lem-sfb-monomial-local-completion vs lem-trf-completed-monoid-support-projection: Its monoid-subring support projection does not give the quotient by a monomial ideal or the local polynomial-to-formal quotient comparison.

lem-sfb-etale-stalk-invariants vs lem-sfb-pulled-torsor-normalization-model: This describes normalization of a pulled-back finite Galois torsor between Noetherian normal domains, including total fraction algebras and finiteness. It neither compares normality of arbitrary etale stalks in both directions nor gives their regularity or dimension invariance.

lem-sfb-etale-stalk-invariants vs lem-sfb-weakly-etale-normal-ring-ascent: Weakly etale normal ascent is more general for the ascent clause alone, but does not state normal descent, regularity or dimension comparison, or identify arbitrary scheme stalks by localization after base change. The new lemma needs all these local comparisons and is not a specialization of this one-way global ascent statement.

lem-sfb-monomial-local-completion vs lem-trf-coefficient-field-generator-presentation: This gives a continuous surjection onto an already complete Noetherian local algebra with a coefficient field and some finite kernel generators. It does not identify that kernel with a prescribed monomial ideal or identify the completion of a localized polynomial quotient with all compatible truncations.

lem-sfb-binomial-laurent-normal-form vs lem-sfb-finite-normalization-model-functoriality: Normalization in a finite function-field extension, its finiteness and semilinear functoriality do not give arbitrary-base xy-a normal forms or the Laurent-intersection computation.

lem-sfb-etale-stalk-invariants vs lem-sfb-galois-geometrically-integral-splitting: This decomposes components after a finite Galois constant extension of an integral variety; it gives no arbitrary etale-stalk regularity/dimension equivalence or normality descent.

lem-sfb-regular-hypersurface-initial-form vs lem-pur-smooth-codimension-one-cartier: Smooth codimension-one closed immersions are Cartier; this does not compute an arbitrary regular-local principal initial ideal, graded quotient and both cotangent cases.

lem-sfb-smooth-trait-curve-local-properties vs def-sbc-smooth-morphisms: The existing statement is about "Smooth morphisms"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-sbc-etale-regular-divisor-base-change: The existing statement is about "Regular divisor under etale base change"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-trf-power-series-cohen-hypersurface-normality: The existing statement is about "Normal ambient power-series rings and Cohen hypersurfaces"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-trf-smooth-local-tangent-cone-extension: The existing statement is about "Tangent cone and minimal-prime dimensions of an essentially smooth local extension"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-sfb-dvr-nodal-chart-blowup-calculus: The existing item is the parent whose released re-split order explicitly requires extracting this separate argument; the new node is strictly smaller and supplies only simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR, not the full item. It is not used in its own proof.

lem-sfb-smooth-trait-curve-local-properties vs lem-sfb-henselian-parameter-root-domain-tower: The existing statement is about "Domains in henselian parameter-root towers and their filtered colimits"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-per-finite-etale-formal-monoid-coefficient-lift: The existing statement is about "Finite etale local factors lift from formal monoid coefficients"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-weil-pbc-smooth-ring-map-iff-smooth-affine: The existing statement is about "A ring map is smooth iff the morphism of spectra is smooth"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-weil-pbc-geometrically-regular-finitely-generated-extensions: The existing statement is about "Geometric regularity tested on finitely generated field extensions"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-weil-pbc-flat-over-regular-with-regular-fibre: The existing statement is about "Flat local maps with regular source and fibre have regular target"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-weil-pbc-smooth-restrict-open-subschemes: The existing statement is about "Smoothness under restriction to open subschemes, composition with an open immersion, and isomorphism"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-weil-pbc-flat-fiber-local-depth: The existing statement is about "Local depth formula expressed at a prime of the fibre ring"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-weil-pbc-pth-root-cotangent-dimension: The existing statement is about "Cotangent dimensions and residue finiteness for the regular p-root quotient"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-weil-pbc-polynomial-presentation-height-field-extension: The existing statement is about "Height difference in a polynomial presentation after field extension"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-weil-pbc-polynomial-complete-local-formal-fibres: The existing statement is about "Formal fibres of a polynomial ring over a complete local ring at a maximal ideal over the closed point"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-weil-pbc-finite-gl-dim-regular-local: The existing statement is about "A Noetherian local ring of finite global dimension is regular (Serre)"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-weil-pbc-regular-local-localization: The existing statement is about "A localization of a regular local ring at a prime is a regular local ring"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-weil-pbc-degree-p-extension-regular: The existing statement is about "Adjoining an n-th root of an element with unit derivative preserves regularity"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-weil-pbc-flat-fiber-prime-height: The existing statement is about "Height formula expressed at a prime of the fibre ring"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-weil-pbc-completion-dimension: The existing statement is about "The completion of a Noetherian local ring has the same dimension"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-weil-pbc-geometrically-regular-smooth-ascent: The existing statement is about "Geometric regularity ascends along smooth ring maps"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-weil-pbc-flat-height-formula: The existing statement is about "Height formula for flat ring maps of Noetherian rings"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-weil-pbc-polynomial-complete-local-generic-fibre: The existing statement is about "Generic polynomial formal fibres over complete local domains"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-smooth-trait-curve-local-properties vs lem-weil-pbc-regular-ring-smooth-ascent: The existing statement is about "Regularity ascends along smooth ring maps"; it does not state simultaneous stalkwise regularity, normality and exact local dimensions of arbitrary smooth pure relative curves over a DVR. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-blowup-chart-algebras vs lem-trf-marked-controlled-blowup-charts: The existing statement is about "Controlled transforms in smooth marked blowup charts"; it does not state the saturated xy-a^n blowup presentations, injectivity, all transition fractions and actual exceptional quotient charts. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-blowup-chart-algebras vs lem-trf-excellent-blowup-projective-transforms: The existing statement is about "Excellent blowup geometry and projective closed transforms"; it does not state the saturated xy-a^n blowup presentations, injectivity, all transition fractions and actual exceptional quotient charts. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-blowup-chart-algebras vs def-trf-controlled-transform-ideal: The existing statement is about "Ideal quotient for the controlled transform"; it does not state the saturated xy-a^n blowup presentations, injectivity, all transition fractions and actual exceptional quotient charts. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-blowup-chart-algebras vs lem-sfb-blowup-rees-symmetric-presentation: The existing statement is about "The symmetric quotient and Rees presentation of the ordinary blowup"; it does not state the saturated xy-a^n blowup presentations, injectivity, all transition fractions and actual exceptional quotient charts. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-blowup-chart-algebras vs lem-sfb-integral-blowup-chart-density: The existing statement is about "Integral blowup charts and density of the center complement"; it does not state the saturated xy-a^n blowup presentations, injectivity, all transition fractions and actual exceptional quotient charts. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-blowup-chart-algebras vs lem-pur-dnc-affine-blowup-complement: The existing statement is about "Affine deformation chart after removing the strict transform"; it does not state the saturated xy-a^n blowup presentations, injectivity, all transition fractions and actual exceptional quotient charts. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-sbc-finite-etale-open-generic-algebra: The existing statement is about "Generic algebra embedding for finite etale open covers"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-trf-marked-controlled-blowup-charts: The existing statement is about "Controlled transforms in smooth marked blowup charts"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-trf-excellent-blowup-projective-transforms: The existing statement is about "Excellent blowup geometry and projective closed transforms"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-trf-blowup-base-change-preserved-open-diagram: The existing statement is about "The flat blowup comparison identifies preserved opens and ambient closed-immersion diagrams"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-trf-etale-completed-local-ring-iso: The existing statement is about "Etale local invariance at a point with algebraically closed residue field"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-trf-module-strict-transform-flat-pullback: The existing statement is about "Module strict transform commutes with flat source and base pullback"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs def-trf-controlled-transform-ideal: The existing statement is about "Ideal quotient for the controlled transform"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-trf-affine-etale-split-neighbourhood: The existing statement is about "Split an affine etale morphism near a marked geometric fibre"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-pc-dense-separable-points: The existing statement is about "Density of rationally defined closed points"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-sfb-integral-finite-etale-generic-field: The existing statement is about "Generic fibre and function field of a surjective integral finite etale cover"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-sfb-blowup-rees-symmetric-presentation: The existing statement is about "The symmetric quotient and Rees presentation of the ordinary blowup"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-sfb-nodal-point-blowup-local-descent: This is the downstream descent of a nodal blowup and uses the parent item; it cannot be cited to prove the parent. It does not supply the independent general the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-sfb-integral-blowup-chart-density: The existing statement is about "Integral blowup charts and density of the center complement"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-sfb-dvr-nodal-chart-blowup-calculus: The existing item is the parent whose released re-split order explicitly requires extracting this separate argument; the new node is strictly smaller and supplies only the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map, not the full item. It is not used in its own proof.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-sfb-finite-etale-normal-generic-components: The existing statement is about "Generic fields and normalization components of a finite etale cover"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-weil-pbc-etale-smooth-zero-dimensional-fibres: The existing statement is about "An etale morphism is smooth with zero-dimensional fibres"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-weil-pbc-constructible-field-finite-separable-constant: The existing statement is about "A constructible sheaf of modules on the spectrum of a field becomes constant over a finite separable extension"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-weil-pbc-finite-separable-extension-etale: The existing statement is about "A finite separable field extension is etale"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-weil-pbc-etale-fibre-discrete-separable-points: The existing statement is about "The fibres of an etale morphism are disjoint unions of spectra of finite separable field extensions"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-weil-pbc-etale-cover-geometric-point-lift: The existing statement is about "A geometric point lifts to some member of a jointly surjective etale family"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-weil-pbc-etale-algebra-residue-field-separable: The existing statement is about "Residue field extensions of an etale algebra are finite separable"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-weil-pbc-spec-finite-product-fields: The existing statement is about "The spectrum of a finite product of fields is a finite discrete scheme whose points are the spectra of the factors"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-pur-dnc-affine-blowup-complement: The existing statement is about "Affine deformation chart after removing the strict transform"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-exc-etale-field-geometric-points-detect: The existing statement is about "Geometric points detect maps from étale field schemes"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-exc-etale-coproduct-etale: The existing statement is about "Coproducts of finite separable etale field spectra are etale"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-flat-pullback-blowup-chart-restrictions vs lem-exc-etale-field-point-map-local: The existing statement is about "Local realization of equivariant geometric-point maps"; it does not state the restriction of the canonical flat blowup comparison to each generator chart and overlap, its exact tensor fraction formula and residue-fibre map. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-etale-stalk-invariants vs lem-trf-etale-coordinate-intersection-geometry: The existing statement is about "Regular coordinate intersections and their etale transport" and does not state the new node's full normality, regularity and dimension under an etale stalk map.

lem-sfb-etale-stalk-invariants vs lem-trf-etale-coordinate-divisor-parameters: The existing statement is about "Marked coordinate divisor parameters under etale pullback" and does not state the new node's full normality, regularity and dimension under an etale stalk map.

lem-sfb-nodal-three-chart-gluing vs lem-trf-semistable-marked-base-change: The existing statement is about "Arbitrary base change of semistable marked curves and fibrewise stability"; it does not state global connectedness and nodal geometry of the specified three-chart gluing and its unique possible middle nonregular point. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-nodal-three-chart-gluing vs def-trf-nodal-geometric-fibres: The existing statement is about "Nonempty connected one-dimensional nodal geometric fibres"; it does not state global connectedness and nodal geometry of the specified three-chart gluing and its unique possible middle nonregular point. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-nodal-three-chart-gluing vs lem-trf-geometric-node-residue-rationalization: The existing statement is about "Rationalizing a geometric node over its finite separable residue field"; it does not state global connectedness and nodal geometry of the specified three-chart gluing and its unique possible middle nonregular point. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-nodal-three-chart-gluing vs lem-trf-projective-nodal-family-geometry: The existing statement is about "Base change and the unramified singular subscheme of a nodal family"; it does not state global connectedness and nodal geometry of the specified three-chart gluing and its unique possible middle nonregular point. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-nodal-three-chart-gluing vs lem-trf-lci-unramified-singular-nodal-recognition: The existing statement is about "Nodal recognition from local complete intersection fibres and an unramified singular subscheme"; it does not state global connectedness and nodal geometry of the specified three-chart gluing and its unique possible middle nonregular point. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-nodal-three-chart-gluing vs lem-trf-nodal-family-fitting-singular: The existing statement is about "Fitting singular subscheme of a nodal relative curve"; it does not state global connectedness and nodal geometry of the specified three-chart gluing and its unique possible middle nonregular point. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-nodal-three-chart-gluing vs lem-trf-nodal-family-etale-local-model: The existing statement is about "Etale local model uv=h of an at-worst-nodal family of relative dimension one"; it does not state global connectedness and nodal geometry of the specified three-chart gluing and its unique possible middle nonregular point. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-nodal-three-chart-gluing vs def-sfb-nodal-geometric-fibre-local-rings: The existing statement is about "Completed local ring, split-node ring and geometric-fibre projection"; it does not state global connectedness and nodal geometry of the specified three-chart gluing and its unique possible middle nonregular point. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-nodal-three-chart-gluing vs lem-sfb-dvr-nodal-etale-local-form: The existing statement is about "Etale local equations of nodal curves over a DVR"; it does not state global connectedness and nodal geometry of the specified three-chart gluing and its unique possible middle nonregular point. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-three-chart-exceptional-curve vs lem-trf-marked-controlled-blowup-charts: The existing statement is about "Controlled transforms in smooth marked blowup charts"; it does not state the reciprocal-glued conic and pair-of-projective-lines classification, explicit conic maps, characteristic-two cover and reduced intersection. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-three-chart-exceptional-curve vs lem-trf-excellent-blowup-projective-transforms: The existing statement is about "Excellent blowup geometry and projective closed transforms"; it does not state the reciprocal-glued conic and pair-of-projective-lines classification, explicit conic maps, characteristic-two cover and reduced intersection. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-three-chart-exceptional-curve vs def-trf-controlled-transform-ideal: The existing statement is about "Ideal quotient for the controlled transform"; it does not state the reciprocal-glued conic and pair-of-projective-lines classification, explicit conic maps, characteristic-two cover and reduced intersection. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-three-chart-exceptional-curve vs lem-sfb-blowup-rees-symmetric-presentation: The existing statement is about "The symmetric quotient and Rees presentation of the ordinary blowup"; it does not state the reciprocal-glued conic and pair-of-projective-lines classification, explicit conic maps, characteristic-two cover and reduced intersection. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-three-chart-exceptional-curve vs lem-sfb-integral-blowup-chart-density: The existing statement is about "Integral blowup charts and density of the center complement"; it does not state the reciprocal-glued conic and pair-of-projective-lines classification, explicit conic maps, characteristic-two cover and reduced intersection. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-three-chart-exceptional-curve vs lem-pur-dnc-affine-blowup-complement: The existing statement is about "Affine deformation chart after removing the strict transform"; it does not state the reciprocal-glued conic and pair-of-projective-lines classification, explicit conic maps, characteristic-two cover and reduced intersection. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sbc-regular-principal-prime-localization-dvr: The existing statement is about "A regular principal-prime localization is a DVR"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sbc-punctured-dvr-normalization-stalk-domain: The existing statement is about "Domain property of the localized normalization stalk"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-adic-reduction-cohomology-sequence: The existing statement is about "The completed DVR quotient universal-coefficient sequence"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sbc-punctured-dvr-normalization-stalk-torsion-free: The existing statement is about "Torsion-free relative normalization stalks over punctured DVR stalks"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sbc-dvr-galois-components-stalk-principal: The existing statement is about "Principal maximal ideal of a normalized finite Galois component stalk"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sbc-dvr-uniformizer-root-algebra: The existing statement is about "A DVR after adjoining a positive-order root of a uniformizer"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sbc-etale-regular-divisor-base-change: The existing statement is about "Regular divisor under etale base change"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sbc-dvr-normalized-compositum-local-diagram: The existing statement is about "Compatible local DVR diagram of a finite normalized compositum"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sbc-root-normalization-stalk-principal-ideal: The existing statement is about "The normalized root stalk maximal ideal is principal independently of ramification"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-adic-tor-flat-cohomology: The existing statement is about "All-level adic cohomology Tor compatibility and flatness"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sbc-root-normalization-generic-stalk-flat: The existing statement is about "Flat normalization stalks at the generic root divisor"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-adic-flat-iff-supplied-model-flat: The existing statement is about "Ambient and supplied-model Padic cohomology flatness"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sbc-regular-cartier-generic-stalk-dvr: The existing statement is about "The generic ambient stalk of a regular integral Cartier divisor is a DVR"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sbc-dvr-unit-root-at-prime: The existing statement is about "DVR and separable residue extension at a unit-root prime"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sbc-punctured-dvr-normalization-stalk-torsion-free-injective: The existing statement is about "Injectivity of the localized normalization stalk map"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sbc-root-cover-generic-pullback: The existing statement is about "The generic root-cover model is a pullback"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-adic-tor-implies-flat-cohomology: The existing statement is about "All-level Padic Tor vanishing implies ambient flat cohomology"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs def-weil-regular-scheme: The existing statement is about "Regular local ring, regular ring, regular scheme"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-trf-power-series-cohen-hypersurface-normality: The existing statement is about "Normal ambient power-series rings and Cohen hypersurfaces"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-trf-fg-commutative-monoid-finite-presentation: The existing statement is about "Finite presentations of finitely generated commutative monoids"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-trf-smooth-local-tangent-cone-extension: The existing statement is about "Tangent cone and minimal-prime dimensions of an essentially smooth local extension"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-trf-etale-coordinate-divisor-parameters: The existing statement is about "Marked coordinate divisor parameters under etale pullback"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-trf-flat-module-torsionfree-domain: The existing statement is about "Flat modules over domains are torsion-free"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-trf-extended-hilbert-local-upper-bound: The existing statement is about "Pointwise local upper bound for extended Taylor Hilbert functions"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-trf-local-tower-collapse-noetherian: The existing statement is about "Noetherian collapse of a supplied local ring tower diagram"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-trf-valuation-separable-closure-extension: The existing statement is about "Finite-height faithfully flat valuation extension to a separable closure"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-trf-local-module-arrow-noetherian-descent: The existing statement is about "Simultaneous Noetherian local approximation of a morphism of finitely presented modules"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-trf-valuation-torsionfree-flat: The existing statement is about "Torsion-free modules over valuation rings are flat"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sc-p1-polynomial-noetherian: The existing statement is about "A one-variable polynomial ring over a field is Noetherian"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sc-dvr-saturation-line-smith-normal-form: The existing statement is about "Smith normal form for a submodule of a finite free PID module"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sfb-regular-trait-curve-surface-components: The existing statement is about "Components and vertical DVR stalks of a regular proper flat trait scheme"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sfb-dvr-nodal-chart-blowup-calculus: The existing item is the parent whose released re-split order explicitly requires extracting this separate argument; the new node is strictly smaller and supplies only the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms, not the full item. It is not used in its own proof.

lem-sfb-dvr-binomial-local-geometry vs lem-sfb-parameter-root-boundary-dvrs: The existing statement is about "Boundary primes and DVR localizations of a simultaneous parameter-root algebra"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sfb-regular-point-blowup-functions: The existing statement is about "Regular functions under a regular point blowup"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sfb-dvr-matrix-smith-powers: The existing statement is about "Rectangular Smith matrices over a DVR"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sfb-dvr-scalar-tor: The existing statement is about "Tor of finitely presented DVR modules and cyclic power quotients"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sfb-henselian-parameter-root-domain-tower: The existing statement is about "Domains in henselian parameter-root towers and their filtered colimits"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sfb-henselian-parameter-root-regularity: The existing statement is about "Henselian regular parameter-root algebra with residue field and parameter basis"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-per-normal-surface-exceptional-curves: The existing statement is about "Finite exceptional-curve data for a normal excellent surface modification"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-per-finite-etale-formal-monoid-coefficient-lift: The existing statement is about "Finite etale local factors lift from formal monoid coefficients"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-rees-algebra-noetherian: The existing statement is about "The Rees algebra of an ideal of a Noetherian ring is Noetherian"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-geometrically-regular-finitely-generated-extensions: The existing statement is about "Geometric regularity tested on finitely generated field extensions"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-cohen-completion-dvr: The existing statement is about "The completion of a flat local p-adic algebra with maximal ideal (p) is a DVR"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-field-regular-ring: The existing statement is about "A field is a regular ring"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-z-localizations-dvr: The existing statement is about "Localizations of the integers are fields or discrete valuation rings"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-localization-noetherian: The existing statement is about "Localizations of Noetherian rings are Noetherian"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-flat-over-regular-with-regular-fibre: The existing statement is about "Flat local maps with regular source and fibre have regular target"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs def-weil-pbc-cohen-ring: The existing statement is about "Cohen ring"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-regular-local-cotangent-dimension: The existing statement is about "Fundamental inequality dim R <= dim m/m^2, with equality iff regular"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-completion-of-dvr-is-dvr: The existing statement is about "The completion of a discrete valuation ring is a discrete valuation ring"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-pid-torsion-free-module-flat: The existing statement is about "A torsion-free module over a principal ideal domain is flat"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-flat-local-ring-maps: The existing statement is about "A flat ring map induces flat local maps of local rings"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-surjective-image-noetherian: The existing statement is about "A ring receiving a surjection from a Noetherian ring is Noetherian"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-serre-criterion-normal: The existing statement is about "Serre's criterion for normality"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs def-weil-pbc-regular-system-of-parameters: The existing statement is about "Regular system of parameters"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-fibre-ring-noetherian: The existing statement is about "Fibre rings of a Noetherian algebra are Noetherian"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-flat-fiber-local-depth: The existing statement is about "Local depth formula expressed at a prime of the fibre ring"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-localization-of-regular-ring: The existing statement is about "A localization of a regular ring is regular"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-colimit-eventually-flat: The existing statement is about "A flat colimit of finite modules over Noetherian local stages is flat at some stage"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-pth-root-cotangent-dimension: The existing statement is about "Cotangent dimensions and residue finiteness for the regular p-root quotient"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-polynomial-presentation-height-field-extension: The existing statement is about "Height difference in a polynomial presentation after field extension"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-polynomial-complete-local-formal-fibres: The existing statement is about "Formal fibres of a polynomial ring over a complete local ring at a maximal ideal over the closed point"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-finite-gl-dim-regular-local: The existing statement is about "A Noetherian local ring of finite global dimension is regular (Serre)"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-dvr-unit-times-uniformizer-power: The existing statement is about "In a DVR every nonzero element is a unit times a power of a uniformizer"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-regular-local-localization: The existing statement is about "A localization of a regular local ring at a prime is a regular local ring"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-degree-p-extension-regular: The existing statement is about "Adjoining an n-th root of an element with unit derivative preserves regularity"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-flat-fiber-prime-height: The existing statement is about "Height formula expressed at a prime of the fibre ring"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-pid-noetherian-normal: The existing statement is about "A principal ideal domain is a Noetherian normal domain"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-completion-dimension: The existing statement is about "The completion of a Noetherian local ring has the same dimension"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-geometrically-regular-smooth-ascent: The existing statement is about "Geometric regularity ascends along smooth ring maps"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-regular-local-dim-one-iff-normal: The existing statement is about "A Noetherian local ring of dimension one is regular iff it is a normal domain"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-finite-type-algebra-noetherian: The existing statement is about "Finitely generated algebras over Noetherian rings are Noetherian"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-finite-algebra-noetherian: The existing statement is about "A module-finite algebra over a Noetherian ring is Noetherian"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-principal-maximal-dim-one-regular: The existing statement is about "A one-dimensional local domain with principal maximal ideal is regular"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-flat-height-formula: The existing statement is about "Height formula for flat ring maps of Noetherian rings"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-polynomial-complete-local-generic-fibre: The existing statement is about "Generic polynomial formal fibres over complete local domains"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-regular-ring-smooth-ascent: The existing statement is about "Regularity ascends along smooth ring maps"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-dvr-completion-regular: The existing statement is about "Characteristic-zero DVR completion is a regular map"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-weil-pbc-graded-finiteness-cohomology: The existing statement is about "Cohomology of a finite type graded module over f^*B~ is a finite B-module"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-exc-punctured-curve-branches: The existing statement is about "The punctured strictly local curve has DVR branches"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs def-sc-discrete-valuation-ring: The existing statement is about "Discrete valuation rings and uniformizers"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sc-dvr-field-extension-order: The existing statement is about "A DVR keeps its normalized order after extending its residue field"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sc-smooth-connected-curve-local-rings: The existing statement is about "Smooth connected curves: integral, local rings at closed points are DVRs"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sc-normal-dim1-dvr: The existing statement is about "One-dimensional normal local rings"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-dvr-binomial-local-geometry vs lem-sc-dvr-dimension-one: The existing statement is about "A discrete valuation ring has dimension one"; it does not state the DVR-specific xy-pi^e model, origin dimension, regular Laurent complement and all three initial forms. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs sbc-lem-affine-space-smooth: The existing statement is about "Affine space is smooth"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-zl-bertini-singular-first-order-model: The existing statement is about "First-order linear kernel containing a Bertini singular fibre"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-zl-hypersurface-nonzero-relative-differential: The existing statement is about "Nonzero relative differential gives a smooth hypersurface point"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-trf-semistable-marked-base-change: The existing statement is about "Arbitrary base change of semistable marked curves and fibrewise stability"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-trf-smooth-local-tangent-cone-extension: The existing statement is about "Tangent cone and minimal-prime dimensions of an essentially smooth local extension"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs def-trf-nodal-geometric-fibres: The existing statement is about "Nonempty connected one-dimensional nodal geometric fibres"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-trf-geometric-node-residue-rationalization: The existing statement is about "Rationalizing a geometric node over its finite separable residue field"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-trf-projective-nodal-family-geometry: The existing statement is about "Base change and the unramified singular subscheme of a nodal family"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-trf-lci-unramified-singular-nodal-recognition: The existing statement is about "Nodal recognition from local complete intersection fibres and an unramified singular subscheme"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-trf-nodal-family-fitting-singular: The existing statement is about "Fitting singular subscheme of a nodal relative curve"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-trf-nodal-family-etale-local-model: The existing statement is about "Etale local model uv=h of an at-worst-nodal family of relative dimension one"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-sc-standard-smooth-etale-polynomial-chart: The existing statement is about "A standard-smooth map admits an etale polynomial chart"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-pd-relative-smooth-dimension-codescent: The existing statement is about "Fixed relative smooth dimension descends under faithfully flat ring base change"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-pc-smooth-characterization: The existing statement is about "Smoothness versus flatness"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-sfb-binomial-chart-smooth-relative-dimension: The existing statement is about "Standard smooth atlas for a diagonal plane hypersurface"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-weil-pbc-standard-smooth-base-change: The existing statement is about "Base change of a standard smooth presentation"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-weil-pbc-standard-smooth-conormal-basis: The existing statement is about "The conormal module of a standard smooth presentation is free on the equations"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-weil-pbc-standard-smooth-over-field-dimension-at-points: The existing statement is about "A standard smooth algebra over a field has dimension n-c at every point"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-weil-pbc-popescu-delocalize-jacobian-localization: The existing statement is about "PopescuDelocalizeJacobianLocalization"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-weil-pbc-popescu-delocalize-dehomogenization-equiv: The existing statement is about "PopescuDelocalizeDehomogenizationEquiv"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-weil-pbc-smooth-locally-standard-smooth: The existing statement is about "Smooth morphisms are locally standard smooth"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-weil-pbc-smooth-over-product-ring: The existing statement is about "Smoothness over a product ring is checked factorwise"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-weil-pbc-standard-smooth-is-smooth: The existing statement is about "A standard smooth algebra is smooth"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs def-weil-pbc-standard-smooth-algebra: The existing statement is about "Standard smooth algebra"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-weil-pbc-polynomial-ring-smooth: The existing statement is about "A polynomial ring in finitely many variables is smooth over its coefficient ring"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-weil-pbc-smooth-at-maximal-ideal-alg-closed-differentials-bound: The existing statement is about "Over an algebraically closed field, few differentials at a closed point imply smoothness there"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-weil-pbc-popescu-delocalize-weak-localization-smooth: The existing statement is about "Smoothness of the localized auxiliary algebra in the weak delocalization"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-weil-pbc-standard-smooth-kahler-basis: The existing statement is about "Differentials of a standard smooth algebra are free of rank n-c"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

lem-sfb-binomial-geometric-fibres vs lem-pur-etale-at-point-from-differentials: The existing statement is about "Differential criterion for an etale coordinate map"; it does not state the explicit xy-a curve, two-axis fibre-product ring, smooth locus, prime chain and field-extension geometry. Shared tags supply partial tools or context, not an exact or more general version of the new statement.

## Validation and unfinished work

The prescribed initial dry run exited zero and printed OK (not pushed) at 1096583a212 against the current server base. That runs the required server preflight including check_dag and review_split. After the landing-refusal review and the explicit reduced-centre clarification, the same required dry run is repeated before pushing. Every new node remains statement-only for the next split level; no Lean proof is claimed.

## Retained complete base arguments for takeover

These are the original fifteen proof arguments, retained verbatim as source material and mapped above into the new node statements. They are not extra unsplit proof steps of the item.

### Base step 1

Write $K=\operatorname{Frac}R$ and $A_n=R[x,y]/(xy-\pi^n)$. Repeatedly replace a mixed monomial $x^ay^b$ by $\pi^{n\min(a,b)}x^{a-\min(a,b)}y^{b-\min(a,b)}$. Thus every element has an expression $c_0+\sum_{i>0}a_ix^i+\sum_{j>0}b_jy^j$, with finite sums and coefficients in $R$. The homomorphism to $K[X,X^{-1}]$ given by $x\mapsto X$, $y\mapsto\pi^nX^{-1}$ sends this expression to $c_0+\sum a_iX^i+\sum b_j\pi^{nj}X^{-j}$. Independence of Laurent monomials and $\pi\ne0$ show that a zero image has all coefficients zero. This proves both uniqueness and injectivity, so $A_n$ is a domain, its fraction field is $K(X)$, and its $R$-module has the displayed basis. The zero prime is generic and all localizations are domains, so its spectrum is integral by the integral-scheme definition. This computation works also for $n=0$, with relation $xy=1$; that case will be used only for the middle blowup chart.

Inputs: def-sc-discrete-valuation-ring, def-weil-polynomial-ring, def-pc-integral-scheme.

### Base step 2

A DVR is a PID, so it is Noetherian and a normal domain by the cited PID lemma. Each $A_n$ is a finite type $R$-algebra, hence Noetherian. Its prime localizations are Noetherian as well: every ideal of a localization is generated by the images of generators of its inverse image. The injection of step 1 makes $A_n$ torsion-free over $R$. The valuation-ring characterization in the DVR definition and the torsion-free-flat lemma therefore imply that $A_n$ is flat over $R$. The displayed presentation is finite, so it is also finitely presented. No assumption on completion or excellence enters these deductions.

Inputs: lem-weil-pbc-pid-noetherian-normal, lem-weil-pbc-finite-type-algebra-noetherian, def-sc-discrete-valuation-ring, lem-trf-valuation-torsionfree-flat.

### Base step 3

In the common field $K(X)$ the two rings $(A_n)_x=R[X,X^{-1}]$ and $(A_n)_y=R[\pi^nX^{-1},\pi^{-n}X]$ are normal domains: apply polynomial normality to the normal domain $R$, then localization normality. Their intersection is exactly $A_n$. Indeed, membership of $\sum c_iX^i$ in the first says $c_i\in R$, and membership in the second says $c_i\in\pi^{-ni}R$. For $i\ge0$ the intersection of these coefficient conditions is $R$; for $i=-j<0$ it is $\pi^{nj}R$. These are precisely the coefficients in the normal form of step 1. If $z\in K(X)$ is integral over $A_n$, its same monic equation makes it integral over each of the two Laurent rings; normality puts it in their intersection. Hence $A_n$ is a normal domain. Applying localization normality once more gives every prime localization of $A_n$ a normal domain, proving the asserted scheme normality.

Inputs: lem-weil-pbc-polynomial-ring-normal-domain, lem-weil-pbc-localization-normal-domain, def-weil-pbc-normal-ring.

### Base step 4

For a geometric point over the generic point of $\operatorname{Spec}R$, the fibre ring is $\Omega[x,x^{-1}]$, since $\pi$ is a unit. Over the closed point it is $\Omega[x,y]/(xy)$. The latter ring injects into $\Omega[x]\times\Omega[y]$ by restrictions to the axes: its image consists of pairs with the same constant coefficient. It is therefore reduced, its two affine-line components meet at the origin, and it is connected of dimension one. The generic Laurent line is also nonempty, connected and of dimension one. For dimension use the polynomial-line dimension lemma and its chains of primes, restricting to the open where the coordinate is invertible for the Laurent line. Away from the origin the special fibre is an open in one of the two lines and is smooth. At the origin its completion is $\Omega[[x,y]]/(xy)$ directly from the completion definition: modulo $(x,y)^d$ the basis is $1,x,\ldots,x^{d-1},y,\ldots,y^{d-1}$, with all mixed products zero. Compatible truncations are exactly pairs of one-variable formal series with equal constants, the same description as the displayed power-series quotient. Smoothness of the line and Laurent line can be checked by lifting a coordinate across a square-zero ideal; a lift of an invertible coordinate is invertible, with inverse obtained by correcting any lifted inverse by the square-zero error. Thus these fibres satisfy every part, including connectedness, of the nodal-geometric-fibre definition.

Inputs: lem-sc-p1-polynomial-dimension-one, def-trf-nodal-geometric-fibres, def-weil-pbc-adic-completion, def-sbc-smooth-morphisms.

### Base step 5

Apply the flat local dimension formula to $R\to A_n$ at any prime, using the Noetherianity and flatness of step 2. The base-local dimension is zero on the generic fibre and one on the special fibre, since a DVR has dimension one and its only primes are $(0)$ and $(\pi)$. Each fibre-local dimension is at most one by step 4, so every local ring of $M_n$ has dimension at most two. At $o$, the special-fibre local ring $\bigl(k[x,y]/(xy)\bigr)_{(x,y)}$ has dimension one: there is the strict prime chain $(x)\subsetneq(x,y)$, while every prime contains $x$ or $y$ and hence lies on a one-dimensional affine line. Thus $\dim\mathcal O_{M_n,o}=1+1=2$.

Inputs: lem-weil-pbc-flat-height-formula, lem-sc-dvr-dimension-one, lem-sc-p1-polynomial-dimension-one.

### Base step 6

The DVR $R$ is regular local: its maximal ideal has the single generator $\pi$ and its dimension is one. It is a regular ring by regular-local localization. Both Laurent rings covering $M_n\setminus\{o\}$ are smooth over $R$: $R[U,V]/(UV-1)$ is standard smooth, with derivative $V$ a unit. Standard smooth implies smooth, so regularity ascends to them. The cover really misses only $o$: a prime containing both $x$ and $y$ contains $\pi^n$ and hence $\pi$. At $o$, when $n=1$, $\pi=xy$ and the maximal ideal is generated by $x,y$; dimension two from step 5 proves regularity. When $n\ge2$, put $P=R[x,y]_{(\pi,x,y)}$ and $\mathfrak m=(\pi,x,y)P$. The three classes $\pi,x,y$ form a $k$-basis of $\mathfrak m/\mathfrak m^2$: reducing successively modulo $(x,y)$, $(\pi,y)$, and $(\pi,x)$ proves their linear independence. The relation $xy-\pi^n$ lies in $\mathfrak m^2$, so passing to $\mathcal O_{M_n,o}=P/(xy-\pi^n)$ leaves that cotangent space three-dimensional. Any two generators of its maximal ideal would span it by two vectors, impossible. This proves nonregularity for $n\ge2$.

Inputs: def-weil-regular-scheme, lem-sc-dvr-dimension-one, lem-weil-pbc-regular-local-localization, def-weil-pbc-standard-smooth-algebra, lem-weil-pbc-standard-smooth-is-smooth, lem-weil-pbc-regular-ring-smooth-ascent.

### Base step 7

Let $X\to\operatorname{Spec}R$ now be smooth of pure relative dimension one. On affine neighbourhoods its ring maps are smooth, by the affine-local equivalence in the smooth-morphism definition. Since $R$ is regular, smooth regular ascent gives regular affine rings; regular rings are normal, so $X$ is regular and normal. Smoothness also supplies flatness and local finite presentation. Apply the flat local dimension formula to each such affine ring. The fibres have pure dimension one, so their local rings have dimension at most one, and at a closed point of a fibre the dimension is one: a component containing that closed point has dimension one, and its generic point strictly generalizes the closed point, while no chain can be longer than one. The base has local dimensions zero or one as before. All stalks of $X$ consequently have dimension at most two, with dimension two at every closed point of the special fibre. The empty $X$ is allowed, all these assertions then being vacuous.

Inputs: def-sbc-smooth-morphisms, lem-weil-pbc-regular-ring-smooth-ascent, lem-weil-pbc-regular-ring-normal, lem-pc-smooth-flat, lem-weil-pbc-flat-height-formula, def-weil-pure-dimension.

### Base step 8

For $n\ge2$, apply the affine blowup chart-cover theorem to $I=(x,\pi,y)\subset A_n$. Its three charts are the subalgebras $A_n[I/x]$, $A_n[I/\pi]$, and $A_n[I/y]$ inside the corresponding localizations. For the first put $t=\pi/x$. In the common fraction field $xt=\pi$, $y=x^{n-1}t^n$, and $y/x=x^{n-2}t^n$. Hence the chart algebra is generated by $x,t$ and is the image of $R[x,t]/(xt-\pi)$. The normal-form injection of step 1, now with exponent one and the same fraction field embedding, proves that this presentation has no further kernel. Interchanging $x,y$ gives $R[y,t']/(yt'-\pi)$ with $t'=\pi/y$ and $x=y^{n-1}(t')^n$. For the middle chart set $r=x/\pi$, $s=y/\pi$. Then $rs=\pi^{n-2}$ and the chart is generated by $r,s$. The normal-form injection, with exponent $n-2$ (including exponent zero), again proves injectivity of $R[r,s]/(rs-\pi^{n-2})$ into the common fraction field. These are therefore exactly the three charts and the stated structure maps, rather than the unsaturated substitutions $x^2(\cdots)=0$.

Inputs: prop-nagata-affine-blowup-chart-cover, def-nagata-blowup-chart-ring, def-nagata-affine-proj, def-nagata-homogeneous-away-to-chart.

### Base step 9

Both outer charts in step 8 are $M_1$, so steps 2, 4 and 6 show that they are flat, regular and have reduced nodal geometric fibres. The middle chart is $M_{n-2}$ when $n\ge3$; when $n=2$ it is $\operatorname{Spec}R[r,r^{-1}]$, which is smooth and flat by its explicit Laurent presentation and the preceding smoothness calculation. Thus every chart is flat and has reduced one-dimensional geometric fibres with only nodes. Their generic fibres glue to the original Laurent line. On the special fibre the two outer equations are $xt=0$, $yt'=0$; the middle equation is $rs=0$ for $n>2$, or $rs=1$ for $n=2$. Their overlaps are obtained by $r=1/t$, $s=1/t'$ where defined. For $n=2$ the middle hyperbola connects the two outer crossing points. For $n>2$ its two axes meet and connect them. Thus the special fibre is connected, and the fibre conditions include the connectedness required by the definition. The regularity calculation of step 6 shows that the outer charts have no nonregular points, and the middle one has a nonregular point exactly if $n-2\ge2$, uniquely its origin. In particular the entire blowup is regular for $n=2$ and $n=3$.

Inputs: def-trf-nodal-geometric-fibres, def-weil-flat-morphism, def-weil-regular-scheme.

### Base step 10

The scheme-theoretic exceptional fibre is obtained by quotienting each chart by the extension of $I=(\pi,x,y)$. In the $x$-chart this ideal is $(x)$, so the exceptional chart is $\operatorname{Spec}k[t]$; in the $y$-chart it is $(y)$, giving $\operatorname{Spec}k[t']$; in the $\pi$-chart it is $(\pi)$, giving $\operatorname{Spec}k[r,s]/(rs-1)$ for $n=2$ and $\operatorname{Spec}k[r,s]/(rs)$ for $n>2$. These quotient calculations determine the fibre scheme, including its reduced structure. For two generators $a,b$ of $I$, inside $D_+(at)$ the other standard open $D_+(bt)$ is the locus where $bt/(at)=b/a$ is invertible, by the homogeneous-prime and fraction descriptions of Proj. Thus the overlap is $D(b/a)$ in $A_n[I/a]$. On the $x$--$\pi$ overlap $r=1/t$ and $s=x^{n-2}t^{n-1}$; on the $y$--$\pi$ overlap $s=1/t'$ and $r=y^{n-2}(t')^{n-1}$. Restricting to the exceptional fibre gives the gluing relations used in the next two steps.

Inputs: def-nagata-blowup-chart-ring, def-nagata-affine-proj, def-nagata-homogeneous-away-to-chart.

### Base step 11

If $n=2$, on the exceptional middle chart $rs=1$ and the overlap relations become $t=1/r=s$, $t'=1/s=r$. Thus the two outer affine lines glue by $t'=1/t$; the middle chart is just their overlap. This is $\mathbf P^1_k$ by its standard-cover definition. It is also the smooth plane conic $XY=P^2$: on the $x$-chart send $t$ to $[1:t:t^2]$, on the $y$-chart send $t'$ to $[(t')^2:t':1]$, and on the middle chart use $[r:1:s]$. These formulas agree on both overlaps and identify the respective affine coordinate rings of the conic with those just computed. The $X$- and $Y$-opens cover the conic, since $X=Y=0$ would force $P=0$. Each is an affine line, proving smoothness also in residue characteristic two. Base extension to an algebraic closure gives the stated geometric exceptional fibre.

Inputs: def-sc-p1-standard.

### Base step 12

If $n>2$, the exceptional middle chart is the union of its $r$- and $s$-axes. Its $r$-axis glues to the $x$-chart by $r=1/t$ on the nonzero coordinates, yielding one $\mathbf P^1_k$; its $s$-axis glues to the $y$-chart by $s=1/t'$, yielding a second. The two axes meet in precisely $(r,s)=(0,0)$, with local equation $rs=0$. There is no outer-chart overlap on the exceptional fibre, since in the $x$-chart $y/x=x^{n-2}t^n$ vanishes there and similarly for $x/y$ in the other chart. Thus there are exactly two reduced projective-line components and their sole intersection is that one reduced node. This gluing description persists after extending $k$ to an algebraic closure.

Inputs: def-sc-p1-standard.

### Base step 13

The affine blowup-complement lemma identifies the blowup with $M_n$ off $V(I)=\{o\}$. For any etale $e:U\to M_n$, flatness is part of the etale definition. The flat blowup comparison of the cited construction is therefore defined, and the flat-base-change theorem says it is an isomorphism $\operatorname{Bl}_{IU}(U)\simeq U\times_{M_n}B_n$. Restricting this isomorphism to the three covering opens gives precisely the pulled-back chart rings and maps. Its fibre at a point $u\in U$ over $o$ is $B_n\times_{M_n}\operatorname{Spec}\kappa(u)$, hence the exceptional fibre of steps 10--12 with coefficients extended from $k$ to $\kappa(u)$. Its geometric fibre is accordingly the conic or pair of projective lines already calculated.

Inputs: lemma-nagata-affine-blowup-complement, def-weil-etale-morphism, def-nagata-blowup-flat-base-change-map, thm-nagata-blowup-flat-base-change.

### Base step 14

Consider a pointed etale map $(U,u)\to(X,x)$. The local dimensions agree by etale local dimension invariance. Its stalk map is flat and local, hence faithfully flat. For normality ascent, base-change an affine etale chart to $\operatorname{Spec}\mathcal O_{X,x}$, which stays etale by the etale base-change lemma. If the base local ring is a normal domain, its localizations are normal by localization normality; etale normal ascent makes the base-changed algebra normal, so its stalk at $u$ is normal. Normality descent follows from faithfully flat normal-ring descent. For regularity ascent perform the same base change; a regular local base is a regular ring by regular-local localization, and the etale algebra is smooth by the etale-smooth lemma, so smooth regular ascent applies. Its stalk is regular. For descent, a regular local source is a regular ring by regular-local localization, and faithfully flat regular descent applies to the stalk map. Applying these implications to each leg of a common pointed etale neighbourhood transports normality, regularity (including nonregularity), and local dimension in both directions. Only the indicated stalks are compared; no isomorphism of residue fields is presumed.

Inputs: lem-sc-etale-local-dimension, lem-weil-pbc-etale-algebra-flat, lem-weil-pbc-flat-local-ring-maps, lem-weil-pbc-flat-local-hom-faithfully-flat, lem-weil-pbc-etale-base-change-finite-limits, lem-weil-pbc-localization-normal-domain, lem-weil-pbc-etale-over-normal-ring-normal, lem-sfb-faithfully-flat-normal-ring-descent, lem-weil-pbc-regular-local-localization, lem-weil-pbc-etale-smooth-zero-dimensional-fibres, lem-weil-pbc-regular-ring-smooth-ascent, lem-weil-pbc-regular-ring-faithfully-flat-descent.

### Base step 15

Finally take a common pointed etale neighbourhood and the reduced point in it lying over $o$. After shrinking around that point, the inverse image of $o$ is exactly this reduced point as a subscheme. To see this, choose an affine etale chart: its fibre over $o$ is a finite type $k$-algebra and therefore Noetherian. Etale local dimension invariance makes all its local dimensions zero. Thus every prime is minimal and maximal; the Noetherian minimal-prime finiteness lemma makes its set of points finite. Remove the other fibre points. Normal ascent from the field $k$ shows the fibre is reduced; the remaining one-point ring is a field, because a zero-dimensional normal local domain has zero maximal ideal. Hence its ideal is exactly the ideal of the reduced point. The blowup comparison of step 13 now applies to this centre, and the local-property comparisons of step 14 apply to the models and the common neighbourhood. This proves the last pointed-neighbourhood clause with the actual reduced centre, without replacing it by a thickening or using completions of $R$.

Inputs: lem-weil-pbc-etale-base-change-finite-limits, lem-weil-pbc-finite-type-algebra-noetherian, lem-sc-etale-local-dimension, lem-weil-pbc-noetherian-finitely-many-minimal-primes, lem-weil-pbc-etale-over-normal-ring-normal, thm-nagata-blowup-flat-base-change.


lem-sfb-binomial-blowup-chart-algebras vs lem-trf-supported-kernel-blowup-charts: the existing statement identifies supported-section kernels on arbitrary affine blowup base-change charts, while this node computes the three explicit Rees chart algebras, their transition maps, and exceptional quotients for the binomial surface; neither statement contains the other.
lem-sfb-three-chart-exceptional-curve vs lem-trf-supported-kernel-blowup-charts: the existing statement identifies module-support kernels on blowup charts, while this node classifies the exceptional-fibre gluing as a conic or two projective lines with explicit maps and reduced intersection; neither statement contains the other.
lem-sfb-binomial-blowup-chart-algebras vs lem-sfb-point-blowup-local-chart-package: the existing local-package statement handles a regular point blowup in dimensions at most two and gives abstract ratio charts, whereas this node computes all three explicit charts, transitions, and exceptional quotient for the singular binomial surface $xy=a^n$; neither contains the other.
lem-sfb-three-chart-exceptional-curve vs lem-sfb-point-blowup-local-chart-package: the existing local-package statement describes ratio charts of a regular-point blowup, whereas this node classifies the glued exceptional fibre as a conic or two projective lines, with explicit homogeneous maps and reduced intersection; neither contains the other.
