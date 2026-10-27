# Q88 stage-1 delivery: lem-trf-separable-smooth-cotangent-germ

## Files written

- dag/nodes/sec-trace-formula/lem-trf-separable-smooth-cotangent-germ.json: statement, split into six proof steps; not a Mathlib leaf.
- citations.json: sixteen step/cited-node pairs, with the statements copied verbatim (including the hypotheses and normalized arrows actually used).
- report.md: this report. searches.jsonl records the five new searches actually run. The earlier item's search records are retained, with their original dates and results.

New nodes: 0. New Mathlib leaves: 0. Existing definition and theorem nodes supply all inputs; no statement-only surrogate for the item was created.

## Attachments

None. Read-only searches of lean/WeilConjectures for the exact blueprint tag and for cotangent germs, separable smooth points, and nonzero relative differentials found no declaration giving this package. The regular-local/separable-smooth and field-theoretic results found by broader searches do not provide its germ, affine chart and compatible identifications. No Lean was written or compiled.

## WANTED

None. All needed Stacks sources are present locally.

## Corrections and route

The item's mathematical statement and stmt_deps are retained verbatim. There is no statement dispute. The original node was unsplit, not a prior completed delivery, and there is no repair note for it. Its old search records were read and retained; new searches used msearch.py exclusively. Loogle returned no hit for `KaehlerDifferential, Algebra.IsSeparable`; the semantic services returned smooth chart and smooth locus facts, and the grep returned cotangent quotient maps and presentation results. A second semantic phrasing returned affine chart theorems again. None is a one-line theorem stating the full item. The search results are logged exactly; none was unavailable.

The live chapter and unit records and literature/blueprint/latest were read. The current ancestor lem-trf-local-term-locality is the contracting-correspondence theorem, while this already-existing auxiliary item belongs to a historical 057G slice branch (as its blueprint.from.place already records). Its generic local-algebra proof does not replace any unit-level argument, and no unit/chapter file was modified. Blueprint searches for `057D`, `nonzero differential`, `smooth differentials` found no imported statement duplicating this item; broader cotangent/differential searches and whole-DAG statement/title searches located the reused tools. The historical provenance and same_as=[] are preserved.

Off-unit tools declared in split_report.tool_uses: smooth differential rank/trivialization, the affine smooth-ring comparison, the fibre-stalk quotient, regularity of smooth local rings over a field, and the regular-local domain theorem. They are generic algebraic geometry facts used as black boxes inside this auxiliary lemma, not substitutions for a unit proof. The remaining off-unit inputs are definitions or already marked Mathlib leaves.

## Review by Q88

I read the complete proof of Stacks 057D (more-morphisms.tex, lemma-slice-smooth-once), and 057G (lemma-slice-smooth), especially the positive-dimensional case where finite separability kills residue differentials. The former explicitly uses localization of differentials, the conormal exact sequence and a lift to the original local ring; the latter supplies the finite separable specialization. I also read the exact theorem statements and proofs in algebra.tex for 00RT (lemma-differentials-localize), 00RU (lemma-differential-seq), 00RV (lemma-differentials-base-change), 00T4 (lemma-base-change-smooth), 00TT (lemma-characterize-smooth-over-field), 00NP (lemma-regular-domain), and 090W (lemma-characterize-separable-algebraic-field-extensions), and the affine differential/rank statements 01UT and 02G1 in morphisms.tex. Schemes 01HV(6),(7) gives the ring and associated-module stalk comparisons; 0HA1 gives the actual surjective fibre-stalk map. These are the sources for the existing nodes, not new source claims hidden in the proof. Tag-label pairs were checked against tags/tags.

Step 1 takes exactly the chart and differential rank from lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension. Its hypotheses are just smoothness and the point; the fibre dimension in its statement is our assumed d. That node does not state that the chosen ring map is smooth, so I separately cited lem-weil-pbc-smooth-restrict-open-subschemes(a) and lem-weil-pbc-smooth-ring-map-iff-smooth-affine. Their statements were opened: the former permits simultaneous source and target open restriction and the latter uses the project's formally-smooth definition, so no unproved switch between two meanings of smoothness occurs.

Step 2 uses lem-trf-affine-fibre-point-dimension for precisely its affine fibre open immersion, prime and finite type assertion. The finite-presentation hypothesis holds because the chosen ring map is smooth. lem-weil-pbc-affine-open-stalk-localization gives the canonical localization of the fibre chart at that prime, not just an abstract ring isomorphism. lem-sbc-scheme-fibre-stalk-quotient gives the actual structural surjection T -> R and its kernel J=m_s T. I wrote out J contained in m_x, the quotient maximal ideal and the residue field identification; localness of a scheme stalk map is part of being a locally ringed space morphism. This avoids silently assuming that a fibre stalk has the original residue field or that its maximal ideal has arbitrary lifts in the original maximal ideal.

Step 3 cites clause (1) of lem-weil-pbc-smooth-ring-map-base-change-composition for k -> k tensor_B A. No flatness or finiteness condition on B -> k is required. lem-weil-pbc-smooth-over-field-regular-local is applied to this smooth k-algebra at its prime q. Finally lem-sc-regular-local-domain says exactly that a regular local ring is a nonzero integral domain. The item does not assume a Noetherian base, and the proof never needs one; Noetherianness of R is supplied by regular-local regularity. These three cited statements were read independently; none is merely a definition substituted for the theorem.

Step 4 uses the actual isomorphisms of lem-weil-pbc-kahler-differentials-base-change and lem-weil-pbc-kahler-differentials-localization. The first applies to B -> k and B -> A; the second to C -> C_q. The relative differential sheaf definition supplies the associated module on the chosen chart, and lem-weil-pbc-spec-tilde-stalk-localization supplies its module stalk and the germ formula. Scalar-extension reassociation and the tensor swap are elementary. I explicitly computed d(a/t)=t^{-1} da-a t^{-2} dt on both routes, so the claimed differential compatibility holds for all germs, not just coordinate-ring sections. There is no separately asserted comparison lemma hidden here: this is the composition of the two cited universal-derivation isomorphisms and the cited stalk isomorphism, evaluated using the Leibniz rule.

Step 5 uses the exactness and the left-arrow formula, both stated by lem-weil-pbc-jacobi-zariski-differential-maps, with ideal m and quotient L. lem-trf-separable-field-differentials-vanish has exactly the finite separable hypothesis assumed here. Thus the last differential space is zero, making the conormal map onto. Selecting a nonzero vector of L^d, pulling it back and choosing a representative in m/m^2 is elementary once those results are available. In particular no Nakayama lemma or unmentioned cotangent injectivity theorem is being used.

Step 6 cites only the fibre-stalk surjection already stated by lem-sbc-scheme-fibre-stalk-quotient. It uses earlier established maximal-ideal and differential identifications. Membership of any lift in m_x follows from m=m_x/J. The differential of zero vanishes, so the chosen fibre germ is nonzero. The last injectivity assertion is the explicitly written domain cancellation argument, not another node restating that clause. This is elementary from the preceding steps and the cited surjection.

I checked delivery-errors B1--B10: no new nodes, no hidden proofs inside statements, no new definitions or unintroduced objects, valid existing source tags, blueprint provenance present, no missing Mathlib or attachment shortcut. For C1--C8 I opened every cited statement, verified each fact used is actually stated, recorded every use in citations.json, kept proof_deps equal to their union, and checked their transitive dependencies do not reach the item (no new cycle). Generic off-unit statement tools are expressly declared. For D1--D5 the steps carry the germ-selection argument rather than moving clauses into new nodes. For E1--E7 I checked all hypotheses, the quotient and point identifications, and the fraction derivation formula; no source error was found. All steps are shorter than 2000 characters.

Small cases: for A=k[t], x=(t), d=1, the construction gives a nonzero cotangent vector represented by t and multiplication by t is injective in k[t]_(t). For a nontrivial finite separable residue extension, the same conormal argument applies without choosing a k-rational point or subtracting a residue scalar inside A. With d=0, E would be zero and vector selection would fail, exactly why d>=1 is assumed. An inseparable residue extension need not have zero differentials and is correctly excluded. The argument does not impose any reducedness on the base or on X; only the smooth fibre local ring is shown to be a domain.

## Unfinished work

None at the authorized stage-1 level. This delivery claims a natural-language split, not a Lean proof.
