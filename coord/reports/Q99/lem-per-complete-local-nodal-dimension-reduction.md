# Stage-1 report: lem-per-complete-local-nodal-dimension-reduction

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-complete-local-nodal-dimension-reduction.json: existing statement unchanged; split into eight steps following ILO VII 3.1--4.2.
- dag/nodes/sec-deligne-laumon-a1/lem-per-ordinary-alteration-cover-base-change.json: statement only, unsplit; geometrically reduced flat base change and component covers for the ordinary alteration topology. No Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-log-regular-pair-regular-pullback.json: statement only, unsplit; strict regular pullback of divisorial log regular pairs. No Mathlib match.
- citations.json: one verbatim statement quotation per cited node per step (35 citations), including the exact clauses supplying the data used.

## Attachments

None. Searched lean/WeilConjectures for the item tag, alteration, nodal, log regularity, partial algebraization, and uniformization. The few nodal mentions are counterexamples in unrelated cohomological docstrings. No finished project declaration states this result. No Lean was written or compiled.

## WANTED

None for this delivery. The item's source and the local algebra sources of the two new nodes are present. I read the existing stronger preparation statements as black boxes; their future proofs remain their own DAG work.

## Corrections and scope

The item statement is retained literally. In particular it does not assert regularity of the output, and its empty-marking/unit-ideal clause is retained. There is no statement dispute. The initial proof was empty. The inherited blueprint ancestry passes through the ordinary weak-uniformization branch of the regular-neighbourhood input; its parent review already notes that the ancestry via Artin--Gabber is stale. I read the newest blueprint ancestor statement/proof and unit, and recorded that inherited relationship without changing chapter or unit routes. This delivery supplies the ILO VII subargument of the existing parent; it does not change the current blueprint's perverse statement.

A prime-to-ell algebraization theorem can be reused here because a complete local ring always has some prime ell invertible (different from its residue characteristic). I explicitly choose this auxiliary prime, apply the stronger existing statements, and then forget degree information. No prime restriction has been added to the item, no prime-to-ell uniformization theorem is invoked, and no dimension-d uniformization result or log resolution is used. A dependency traversal of the existing preparation/nodal statements did not reach the item.

I corrected an early draft of step 5: etaleness of the marking by itself is not a sufficient citation for its Cartier pullback. The final step uses that D is Cartier and flat over the base (etale by definition), hence relative effective Cartier, and cites the existing relative-Cartier base-change lemma. This also avoids hiding a local-coordinate lemma inside the step.

## Review by Q99

I read ILO Expose V 3.1.3--3.1.4 (printed p.66), VI 1.2--1.9 (pp.69--71), VII 2.3 and 3.1--4.3 (pp.81--83), stopping the proof before 4.3, and II 1.2.3--1.2.9 and 2.3.1--2.3.4 (pp.24--28). VII 3.1 supplies the dimension-lowering algebraization, 3.3 compactifies and Cartierizes, 3.4 gives marked nodal reduction, 4.1 uses the lower-dimensional induction hypothesis, and 4.2 applies VI 1.9. VII 3.2 is the regular-completion return to the original scheme. I also read Stacks algebra.tex Tag 031E, lemma-flat-over-regular-with-regular-fibre, and Tag 00ON, lemma-dimension-base-fibre-equals-total, and divisors.tex Tags 056Q, lemma-relative-Cartier, and 062T, definition-relative-effective-Cartier-divisor.

For the ordinary-cover helper, the source's II 1.2.3 fourth bullet permits ordinary fibre products for a reduced (flat geometrically reduced) base change; II 2.3.4 preserves covers even for a non-finite-type completion map. The reduced-component family is the proper-surjective generator. This is a topological/scheme-theoretic tool, with no induction, marked preparation or log regularity in its conclusion. For the log-pullback helper, I checked the chart argument behind VI's definition: at compatible strict local rings A -> C the map is regular local and characteristic nonunits stay nonunits. If I is the chart ideal, C/IC is regular over A/I. Writing F=C/m_A C, the two flat local dimension formulas give dim C=dim A+dim F and dim(C/IC)=dim(A/I)+dim F, so their difference is exactly the same characteristic rank. This is not an assertion that the whole source scheme is regular. VI 1.4 then identifies the log regular inverse-image structure with the divisorial structure and its dense triviality locus. This comparison is why the new statement is a real lemma, not a one-line elementary step. Its future split must formalize this argument.

I opened the statement of every node cited in each step:

1. Complete-local excellence applies to A, which is Noetherian and complete. The marked algebraization node requires a normal complete local scheme, dimension at least two and an invertible prime; the chosen ell provides its only additional parameter. Its statement gives the ordinary completed local ring, the regular map g, the lower-dimensional excellent regular Y_0, integral W and the exact marking equality. The generic marking avoids the generic point of the integral curve; the existing nowhere-dense curve lemma then gives its required dimension bound.
2. Proper generic curve preparation requires an affine excellent integral base, an affine integral relative generic curve and a zero-dimensional/empty generic marking; step 1 gives each. Its statement supplies P, P-circ, h and E, including the exact inverse-image equality and the smooth geometrically integral generic curve. Proper generically finite surjections are covers by the ordinary definition; their degrees are irrelevant.
3. Relative marked nodal reduction requires a proper dominant curve, a smooth irreducible generic curve, an etale generic marking and a projective base over an affine Noetherian scheme. Y_1 is affine, so its identity supplies that projectivity hypothesis. Its statement supplies all nodal and boundary data. The dimension lemma states exactly that a proper dominant generically finite map of integral locally Noetherian schemes preserves dimension, so dim Y' <= d-1, independently of the dimension of P or C.
4. The induction assumption is applied only to Y', which is excellent, integral (hence reduced), Noetherian and of the checked dimension. The definition of U supplies integral regular Noetherian S_j and the exact strict boundary T_j. Finite-type-over-excellent on affine charts supplies excellence of S_j. The regular-boundary chart theorem explicitly concludes that a regular scheme with that strict normal crossings boundary is a log regular pair; it needs no field base.
5. The projective nodal family geometry statement explicitly preserves the nodal curve properties and the smooth locus under arbitrary Noetherian base change. The etale base-change lemma preserves D_j -> S_j. Etale includes flatness in its definition, so D is relative effective Cartier; the relative-Cartier pullback lemma (with f flat and finitely presented, already given by the nodal theorem) supplies its Cartier pullback. The nodal-log-regularity statement then has every hypothesis: log regular base, proper flat finitely presented nodal curve, smoothness off T_j, and an etale Cartier marking in its smooth locus. It concludes nowhere density and log regularity. The ordinary-cover base-change helper applies to C -> Y', flat geometrically reduced by the nodal fibre condition; it says that the usual products are alteration objects, controlling their generic points.
6. Log-regular divisorial structure explicitly gives normal local domains. The Cartier ideal of E is pulled through maps whose generic points dominate P; a generator cannot become zero, and in a local domain nonzero means non-zero-divisor. This is the elementary argument required by the effective-Cartier definition, not a claim that every arbitrary pullback of a Cartier ideal is Cartier. The marked containment is exactly the nodal theorem's containment. Open restriction is regular and preserves the pair by the new log-pullback lemma. The ordinary base-change lemma applies to this open immersion. The proper surjective alteration C -> P and h then compose with the finite covering by the covering-sieve axioms stated in the ordinary-topology definition.
7. The ordinary-cover helper expressly permits non-finite-type regular base change. The existing regular ring-map base-change lemma requires the other map finite type; C_j-circ -> W is finite type, so the projection N_j -> C_j-circ is regular. The new log helper applies to this projection, not to a non-flat modification. Flat Cartier pullback gives the precise ideal and zero-set. Finite type over a complete excellent Noetherian base yields Noetherianness and excellence of N_j; the cited statements cover exactly these properties.
8. The divisorial-structure statement gives normality; the normal topologically Noetherian components lemma supplies a finite disjoint union of integral open and closed components, including the possible empty case. Component-cover calculus and transitivity retain covering. The finite surjective p is an ordinary cover. The pulled-back markings have the required equality, and the unit ideal handles Z empty directly. We do not apply ILO VII 4.3.

I tested the statements on the empty source/empty boundary, the identity map, restriction to a dense open, a field and inseparable field-extension examples. The cover helper requires geometrically reduced fibres, excluding a purely inseparable field extension that would make an ordinary product nonreduced. A finite etale cover can split after regular base change, so the final source is not assumed integral until its disjoint normal components are taken. In mixed characteristic the auxiliary prime differs from residue characteristic; in residue characteristic zero any prime is a unit. The item starts at d=2; then the base dimension bound is one, within the induction hypothesis. The log helper allows regular pullbacks with nontrivial regular fibres, and the rank is unchanged while both stratum and total dimension acquire the same fibre dimension. A toric log regular singularity is not made regular by this argument, as required by the item.

B--E audit: the two new nodes are self-contained statement-only unsplit nodes; their notions are either defined inline or cite their definition nodes. TeX is encoded once. Searches were run with msearch.py, read, and recorded from searches.jsonl with the exact tool/query; both semantic services, Loogle and grep were successful, with no match. Second phrasings were tried. No successful service was called unavailable. The grep finds no alteration or log-regularity theory in Mathlib; generic precoverage/base-change facts do not supply either geometric comparison. Whole-DAG and whole-blueprint searches were run by keywords, relevant tags and ancestry, with no exact blueprint node; existing stronger preparations and normality/component lemmas were reused. The new log lemma is not the existing regular-source normal-crossings pullback lemma, nor a specialization of it. No new node restates the item or a clause of its induction conclusion. All eight steps are below 2000 characters. Citations were checked against node statements, never their proofs, and copied verbatim into citations.json. Generic tools of other units are declared in split_report.tool_uses for the independent reviewer. No chapter, unit, live source, launcher file or git worktree was edited.

## Not duplicates

lem-per-ordinary-alteration-cover-base-change vs lem-per-alteration-cover-calculus: the existing statement is for a prime-to-ell topology and dominant finite-type new base; the new statement is for the ordinary topology and geometrically reduced flat maps of arbitrary type, including completion.
lem-per-ordinary-alteration-cover-base-change vs lem-per-alteration-generators-reduced-base-change: the existing statement preserves prime-to-ell generators and categorical products, expressly without claiming covering families; the new statement covers arbitrary finite ordinary alteration covers and component refinements.
lem-per-ordinary-alteration-cover-base-change vs lem-per-flat-geometrically-reduced-pullback: the existing statement concludes only reducedness of ordinary products, not membership in the alteration category or preservation of its covers.
lem-per-log-regular-pair-regular-pullback vs lem-per-regular-pair-alteration-pullback: the existing result assumes regular sources with strict normal crossings markings and a prime-to-ell cover; the new lemma starts with possibly singular log regular sources and identifies the inverse-image log structure with the divisorial one, without an alteration or prime parameter.
lem-per-log-regular-pair-regular-pullback vs lem-trf-log-smooth-log-regular: the existing lemma requires a smooth chart morphism, whereas a regular completion map need not be smooth or of finite presentation.
lem-per-log-regular-pair-regular-pullback vs lem-per-log-smooth-invertible-torsion-log-regular: the existing lemma again has smooth chart maps, including invertible torsion, rather than arbitrary regular maps and the claimed divisorial identification.

lem-per-log-regular-pair-regular-pullback vs lem-trf-smooth-local-tangent-cone-extension: the existing statement is an associated-graded and minimal-prime dimension theorem for essentially smooth local Q-algebras; it has no divisorial log structure or regular-map pullback conclusion.

lem-per-log-regular-pair-regular-pullback vs lem-trf-polynomial-strict-local-coordinate-dimension: the existing statement concerns dimensions of coordinate quotients and strict henselizations of polynomial rings over a field; it does not treat arbitrary regular pullbacks of log regular pairs.

lem-per-log-regular-pair-regular-pullback vs lem-trf-polynomial-localization-order-reflection: the existing statement concerns regular local polynomial rings and contraction of powers of their maximal ideals; it has no log structure or boundary.

lem-per-log-regular-pair-regular-pullback vs lem-trf-polynomial-log-chart-regularity: the existing statement adjoins polynomial coordinates and enlarges the characteristic monoid by a free factor; the new lemma allows arbitrary regular maps with unchanged characteristic at corresponding points and identifies the pulled-back divisorial structure.

lem-per-log-regular-pair-regular-pullback vs lem-sfb-smooth-trait-curve-local-properties: the existing statement is regularity and local dimension of a smooth relative curve over a DVR; it has no general log regular pair or arbitrary regular morphism.

lem-per-log-regular-pair-regular-pullback vs lem-sfb-ind-etale-henselian-regular-stages: the existing statement is about ind-etale rings and regular parameter quotients; it does not identify divisorial log structures under arbitrary regular maps.

lem-per-log-regular-pair-regular-pullback vs lem-sfb-dvr-binomial-local-geometry: the existing statement computes regularity and cotangent dimensions of explicit xy=pi^e surfaces; it does not state log regularity under pullback.

lem-per-log-regular-pair-regular-pullback vs lem-sfb-smooth-integral-fibre-vertical-divisors: the existing statement is a divisor-group identification for smooth geometrically integral-fibre algebraic spaces over a regular base; it does not allow singular log regular bases or assert the divisorial log pullback comparison.

lem-per-log-regular-pair-regular-pullback vs lem-sfb-smooth-generic-trivial-line-descent: the existing statement descends a generically trivial line bundle along a smooth surjection of regular schemes; the objects and conclusion differ from log regular pullback.

lem-per-log-regular-pair-regular-pullback vs lem-per-regular-pair-alteration-pullback: the existing statement assumes regular sources with strict normal crossings and a prime-to-ell cover; the new lemma includes singular log regular pairs and arbitrary regular maps with no cover or prime hypothesis.

lem-per-log-regular-pair-regular-pullback vs lem-weil-pbc-flat-over-regular-with-regular-fibre: the existing statement is regularity ascent for local rings; it does not preserve fine saturated log charts or identify the divisorial log structure.

lem-per-log-regular-pair-regular-pullback vs lem-weil-pbc-regular-map-ascent: the existing statement concerns ordinary regularity of rings, whereas the new statement allows underlying singular rings and a log regular divisorial structure.

lem-per-log-regular-pair-regular-pullback vs lem-weil-pbc-flat-fiber-local-depth: the existing statement is the depth formula for a flat local fibre, not a log-regularity or log-structure comparison theorem.

lem-per-log-regular-pair-regular-pullback vs lem-weil-pbc-pth-root-cotangent-dimension: the existing statement computes cotangent dimensions for a specific pth-root algebra, not arbitrary regular pullbacks of divisorial log regular pairs.

lem-per-log-regular-pair-regular-pullback vs lem-weil-pbc-polynomial-presentation-height-field-extension: the existing statement is a height identity for polynomial presentations after field extension; it has no log structure and does not supply the divisorial comparison.

lem-per-log-regular-pair-regular-pullback vs lem-weil-pbc-flat-fiber-prime-height: the existing statement is the height formula for a prime of a flat fibre, not preservation of log charts or divisorial structure.

lem-per-log-regular-pair-regular-pullback vs lem-weil-pbc-completion-dimension: the existing statement only preserves total Krull dimension under local completion; it gives neither log regularity nor a comparison of boundary log structures.

lem-per-log-regular-pair-regular-pullback vs lem-weil-pbc-flat-height-formula: the existing statement is the flat local dimension/height formula; it supplies no chart, fs condition, triviality locus or divisorial identification.

## Unfinished work

The two new nodes remain unsplit intentionally, as required by the one-level stage-1 contract. No other mathematical gap is being deferred inside the item. The final dry run and push status are supplied by deliver.py.
