# Stage-1 report: lem-sfb-regular-group-rigidified-line-extension

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-regular-group-rigidified-line-extension.json: existing statement, split in seven steps; original statement and hypotheses retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-regular-space-divisor-line-dictionary.json: statement, unsplit; no Mathlib match after LeanFinder, LeanSearch, Loogle and source grep, including two semantic phrasings.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-integral-fibre-vertical-divisors.json: statement, unsplit; no Mathlib match after the same four searches and two semantic phrasings.
- citations.json: a verbatim statement quotation for each node used by each proof step.
- report.md: this report. searches.jsonl retains the command-generated search records.

## Attachments

None. Searched the live lean/WeilConjectures tree by the item blueprint tag and by rigidification, rational sections, Cartier/Weil divisors and vertical divisors. The module Modules/Rigidification.lean concerns generators and pullback criteria, not this regular-base equivalence for group algebraic spaces. The Picard and theorem-of-the-cube matches do not prove this item's clauses. No exact finished project declaration was found. Nothing was compiled.

## WANTED

WANTED: Pierre Deligne, Le lemme de Gabber, Astérisque 127 (1985), Section 4.2, printed p.142, for lem-sfb-regular-group-rigidified-line-extension and the source explanation of lem-sfb-smooth-integral-fibre-vertical-divisors. The local PDF named by the inherited node is absent. The primary Numdam PDF was read online at https://www.numdam.org/article/AST_1985__127__131_0.pdf (PDF page 12). No literature was downloaded or written.

## Findings and corrections

The imported statement is consistent with the source's argument. It was not a completed proof: its proof list was empty. The source gives an unrigidified extension, corrects at the identity, and uses irreducible geometric fibres for uniqueness. The essential omitted explanation is the vertical-divisor calculation. I did not assume that functions on a nonproper group are constant, or that a generic isomorphism extends merely because its source and target are lines.

For unrigidified existence I used divisor closure in the regular total space. This is a node-level alternative to the coherent-extension determinant in Deligne, not a change to a unit or chapter route: the same extension, identity normalization and irreducible-fibre uniqueness are realized. The dictionary support node states the needed general divisor theorem; it does not state extension of rigidified lines. The vertical support node classifies prime divisors of a general smooth morphism; it has no group law, identity or rigidified-line assertion. The item itself writes the normalization, cancellation and gluing arguments. Neither support node is a restatement of the item or of its equivalence clauses.

The current blueprint is literature/blueprint/latest (the main-20261023-1620 snapshot in COMMITS.txt). I read the latest unit text, the inherited DAG unit record and the fixed chapter record. This is a supporting node created well below the unit's direct-image alteration/moduli route, not its key node, so no unit realization file was changed. The DAG unit record has historical text, but that discrepancy does not alter this auxiliary geometric argument. tools/blueprint_refs.py ancestor returns None for the item; I preserved the inherited null ancestor and entire via chain. The from.place is specific and same_as is empty after whole-blueprint searches for rigidified, regular algebraic space, Cartier divisors, coherent extension, determinant and vertical divisor. The source-library search also covered the two new statements.

## What remains

Only stage 1 was requested. The two support statements remain unsplit for later workers. There is no Lean writing, build, compiler invocation or stage-2 statement in this delivery. The required server dry run and push follow this report.

## Review by Q125

I read Deligne Section 4.2 on printed p.142, with its preceding normalized Jacobian line, and checked the mathematical content against the current item. For the dictionary statement I read spaces-divisors.tex, lemma-Noetherian-regular-separated-pic-effective-Cartier (0DMM), lemma-regular-meromorphic-section-exists (0EPQ) and its compute-meromorphic hypotheses, plus divisors.tex lemma-weil-divisor-is-cartier-UFD (0AGA). These supply rational sections and local Cartier representatives; the dictionary records their combination for regular separated Noetherian algebraic spaces, including the zero-order generator criterion. For the vertical statement I read algebra.tex lemma-dimension-base-fibre-equals-total (00ON), descent.tex lemma-regular-local-smooth (036D), and the regularity conventions in spaces-properties.tex. Neither new node contains a proof: the following explanation is the handoff to its next worker.

On a regular chart, a codimension-one integral closed subspace is locally principal. Ratios of equations for the same divisor have zero valuation at every height-one prime and hence are units in the regular local UFD. Consequently equations glue as Cartier divisors, their inverse generators define line modules, and the same criterion detects when a rational section is an everywhere regular generator. The generic-point description in 0EPQ supplies a rational section of every line. This works component by component, with no integrality assumption on the whole base. For a smooth flat chart over a regular base, 00ON says that a vertical height-one point lies over a height-one base point and is generic in that fibre. The fibre is integral, so that generic point is unique; smoothness makes it reduced, so a base uniformizer has order one. The inverse image of the integral base divisor is itself integral (flatness and integral fibres over an integral base). This gives exactly the prime-divisor classification, not just a numerical equality. Smoothness also makes inverse images of dense opens dense. All constructions are etale local, and flat base change preserves the reduced, multiplicity-one description. No excellence or properness assumption enters.

Step 1 uses the vertical node's explicit regularity, Noetherianity, absolute-separatedness over an affine open, and density clauses. The dictionary then applies with precisely its Noetherian and separated hypotheses. The identity section verifies nonempty fibres, a hypothesis that cannot simply be omitted from that node. The affine-base proof is explicitly globalized later.

Step 2 uses the dictionary's existence of rational sections, construction of O(D), uniqueness for a rationally trivialized line, and compatibility with open restriction. Taking the finite closures of the divisors is an actual construction: their generic points and local rings do not change on closing up from an open, so their codimension is still one. It does not use a scheme representability theorem or the mere proof of a cited node.

Step 3 uses only rank-one evaluation and the ringed-site model's composition clause. The formula involving t inverse was checked in a free generator: applying rho on the identity gives lambda(h), exactly evaluation. This ensures that the specified rigidification extends. The construction involves actual tensor inverse image, rather than inverse image of abelian sheaves.

Step 4 uses the dictionary to attach a divisor to the rational isomorphism, and the vertical node's isomorphism on supported divisor groups to write it uniquely as p*D. Its rational section is initially defined on the genuinely dense G_V, verified in Step 1. Both node statements say these things; no cited definition is being used as a substitute for a theorem.

Step 5 is the crucial cancellation, written in local equations. The associated line for a Cartier equation f is f inverse times O, so its section and line commute with pullback along p. Pullback along e is legitimate at generic points because e over V lies in the original domain of the isomorphism. The resulting rational section is 1 under the two rigidifications. Thus its divisor is zero, but pe=1 identifies that divisor with D. The dictionary's zero-divisor criterion makes the original rational isomorphism a global isomorphism. Its dense-open equality clause proves both preservation of rigidification and uniqueness. This proves extension of a specified isomorphism, not just uniqueness of line isomorphism classes.

Step 6 uses the algebraic-space definition only to choose a scheme etale atlas, and uses the precise statement of lem-trf-algebraic-space-invertible-descent for effectiveness and the Hom bijection. The affine-base full-faithfulness argument first constructs the comparison on affine refinements of overlaps; local uniqueness gives both gluing and the triple cocycle. Only after this do I invoke scheme-atlas descent. This avoids applying the cited statement directly to a cover by algebraic spaces. Ordinary invertible modules on those scheme charts are exactly covered by the cited statement's Zariski/etale comparison clause. The identity rigidifications glue as maps of sheaves on the base.

Step 7 uses the vertical node's etale-base-change clause to check regularity, local Noetherianity and density on S', and the ringed-site model's composition compatibility to identify the two restrictions with their rigidifications. The comparison and all composition coherences are the unique extensions of the same dense-open map by the full faithfulness already proved. I did not claim the regular-base equivalence for arbitrary nonflat base changes.

I tested V=S, S empty, the identity group, a disconnected regular base, a boundary of codimension at least two, and the nonproper torus over a DVR. For the torus, generic automorphisms can be powers of the coordinate, so replacing uniqueness by a claim that units are constant would be wrong; the vertical-divisor cancellation does not do so. If the geometric fibres have several components, different vertical components need not be a base pullback, explaining why the given hypothesis is used. A ramified non-smooth trait map can give multiplicity greater than one, so the smoothness hypothesis in the vertical lemma is also essential. In dimension zero V=S componentwise, making the empty divisor case automatic.

I checked delivery-errors B through E: the two support statements introduce their objects, inline the divisor and rational-section notions, use TeX once, have no proofs or proof dependencies, have honest command-logged searches, and have no claimed Mathlib matches. Every non-elementary proof step cites its inputs, every citation was reread and backed by a verbatim quote in citations.json, and the uses union equals proof_deps. There is no reference from either support node back to this item. All seven proof steps are under 2000 characters. The off-unit ringed-site and descent tools are declared under split_report.tool_uses; they interpret and glue lines and do not replace the unit route. The statement was not weakened and no statement dispute was found.

## Not duplicates

lem-sfb-regular-space-divisor-line-dictionary vs lem-per-regular-prime-divisor-local-equations: gives a local Cartier equation and DVR for a single prime divisor on a scheme; it does not give rationally trivialized line modules on algebraic spaces or the vertical divisor classification.

lem-sfb-regular-space-divisor-line-dictionary vs lem-sc-divisor-module-local: gives explicit local generators for divisor modules on a smooth curve over an algebraically closed field; the new dictionary concerns arbitrary-dimensional regular algebraic spaces.

lem-sfb-smooth-integral-fibre-vertical-divisors vs lem-trf-smooth-local-tangent-cone-extension: computes tangent cones of essentially smooth local Q-algebras, rather than vertical prime divisors of a global algebraic-space morphism.

lem-sfb-smooth-integral-fibre-vertical-divisors vs lem-trf-polynomial-strict-local-coordinate-dimension: computes dimensions for polynomial strict-local coordinate quotients over a field, rather than classifying vertical divisors.

lem-sfb-smooth-integral-fibre-vertical-divisors vs lem-trf-polynomial-log-chart-regularity: proves log regularity and dimension formulas for polynomial log charts; it has neither general integral fibres nor vertical-divisor pullback.

lem-sfb-smooth-integral-fibre-vertical-divisors vs lem-sfb-smooth-trait-curve-local-properties: gives local regularity and dimensions for relative curves over a DVR, rather than the vertical-divisor classification in arbitrary relative and base dimension.

lem-sfb-smooth-integral-fibre-vertical-divisors vs lem-sfb-smooth-dvr-generic-line-extension: extends a line on the generic fibre of a smooth scheme over a DVR; it supplies neither the algebraic-space Cartier/Weil dictionary nor the classification of vertical divisors over an arbitrary regular base.

lem-sfb-smooth-integral-fibre-vertical-divisors vs lem-sfb-dvr-binomial-local-geometry: computes regularity and dimensions of a specific binomial surface, without a general smooth integral-fibre divisor theorem.

lem-sfb-smooth-integral-fibre-vertical-divisors vs lem-weil-pbc-flat-over-regular-with-regular-fibre: is a local ring regularity ascent statement, not a divisor classification theorem.

lem-sfb-smooth-integral-fibre-vertical-divisors vs lem-weil-pbc-flat-fiber-local-depth: is a local depth formula, not a theorem about global prime divisors.

lem-sfb-smooth-integral-fibre-vertical-divisors vs lem-weil-pbc-pth-root-cotangent-dimension: is a cotangent-space calculation for a particular characteristic-p quotient, not a smooth integral-fibre divisor theorem.

lem-sfb-smooth-integral-fibre-vertical-divisors vs lem-weil-pbc-polynomial-presentation-height-field-extension: is a prime-height identity for scalar extension of a polynomial presentation over fields, not a vertical-divisor theorem.

lem-sfb-smooth-integral-fibre-vertical-divisors vs lem-weil-pbc-flat-fiber-prime-height: states a flat affine ring height formula; it does not identify global fibre divisors, show multiplicity one or give descent for algebraic spaces.

lem-sfb-smooth-integral-fibre-vertical-divisors vs lem-weil-pbc-completion-dimension: compares a local ring with its completion, not vertical divisors.

lem-sfb-smooth-integral-fibre-vertical-divisors vs lem-weil-pbc-flat-height-formula: states the flat local-ring dimension formula; the new node includes the separate irreducibility, reduced multiplicity-one, and global divisor identification for algebraic spaces.
