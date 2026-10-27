# Stage-1 report: lem-sfb-borel-characteristic-picard-sequence

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-borel-characteristic-picard-sequence.json: item, statement unchanged, split into six complete proof steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-borel-quotient-proper-geometry.json: statement, unsplit; no Mathlib match. Smooth regular integral geometry for a represented homogeneous quotient, and properness for a maximal connected solvable subgroup.
- dag/nodes/sec-six-functors-basics/lem-sfb-split-solvable-torsors-and-variety.json: statement, unsplit; no Mathlib match. Split solvable torsors, the underlying affine-space-times-torus variety, and its Picard triviality after field extension.
- dag/nodes/sec-six-functors-basics/lem-sfb-rosenlicht-product-unit-factorization.json: statement, unsplit; no Mathlib match. Product-unit factorization for integral varieties.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-generic-trivial-line-descent.json: statement, unsplit; no Mathlib match. Generic-fibre-trivial invertible sheaves along smooth maps with integral fibres come from the regular base.
- citations.json: verbatim statement quotations for every proof-step citation.

## Attachments

None. Searched the live lean/WeilConjectures source for the item id, Borel, Rosenlicht, characteristic/Picard and solvable-group notions. No project declaration states the item or any of the four inputs. Unrelated Artin--Schreier characters and curve Picard declarations are not attachments.

## WANTED

None. Milne and the relevant Stacks source files are available locally. No SGA source is used.

## Findings and changes

The original statement is correct, including non-reductive smooth connected affine groups. The existing reductive-borel-pair-structure node cannot be applied to such a group: reductivity is an extra hypothesis. I retained the statement and used the existing algebraic-group-homogeneous-quotient for representability. The new geometric node supplies properness and smooth integral geometry for general connected groups; it does not reconstruct the quotient.

Milne 18.32 writes the last exactness check only as "similarly straightforward". The new generic-trivial-line node exposes the general lemma hidden by that phrase rather than making a new node which merely repeats surjectivity of Pic(G/B) -> Pic(G). Its intended argument is as follows. Choose a nowhere-zero section of M over the entire generic fibre, and regard it as a rational section of M on Y. Its finite divisor has no horizontal component. For a vertical prime divisor D, flatness and the dimension formula 00ON give codim_S f(generic(D)) = 1 and fibre codimension zero. The integral fibre has one generic point; smoothness gives multiplicity one. Consequently D is the closure of the inverse image of the corresponding prime divisor E of S. Pullback of E has no additional components over higher-codimension points, again by the dimension formula. Thus div(s)=f^*(sum n_E E). Since S is regular, 0AG0 and 0AGA make that finite Weil divisor Cartier, and the divisor/invertible-sheaf dictionary gives M ≅ f^* O_S(sum n_E E). This argument uses no properness and no rational section of f, and is strictly more general than the item's final clause. It remains in the statement-only node's future split, not in its statement.

The normalized-unit observation needs no separate node: applying the Rosenlicht product identity to u(xy) at (e,e) gives multiplicativity in one line. Similarly, tensor compatibility of associated lines and triviality for restrictions of characters are explicit operations on descent data, not new lemma nodes.

The inherited blueprint ancestry has from.node = null. tools/blueprint_refs.py ancestor reports None for this item; I preserved that field and the existing via chain, and extended the precise place for each new input. I read the latest blueprint (main-20261023-1620, 7284bb09da) sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and direct-images proof (3). This item supports its alteration route through the inherited Milne covering construction; it does not replace that route or modify a unit record. The item is not a unit key node.

## Searches

Read all five actual search results for each of the item and the four prospective new statements. search-plan.json records the exact queries; the individual .txt files preserve full outputs, and searches.jsonl is the msearch.py log. Each set contains two LeanFinder phrasings, Loogle, grep and LeanSearch. All services answered. In particular I inspected Mathlib/RingTheory/PicardGroup.lean lines 618 and 855--862: relPic and Submodule.mulExact_unitsToPic_mapAlgebra refer to invertible submodules of a faithful ring algebra. They neither describe characters of a group scheme nor give the regular-family generic-fibre lemma. Topological quotient/Borel-space results and vector-bundle trivializations have different objects. No new statement is a one-line specialization of these hits.

Before naming new nodes I searched the whole DAG by Borel, solvable, torsor/Picard, Rosenlicht, units/products, quotient, generic fibre and the source numbers 5.28, 12.48, 12.49, 16.55, 16.56, 18.32, and Stacks 00ON/0AGA/0AG0. blueprint_refs.py searches included Borel, torsor, divisor, homogeneous, solvable, units, Picard, quotient by, Rosenlicht, Borel fixed, homotopy, generic fibre, line bundle, invertible regular, proper reduced and vertical divisor. No imported blueprint node states any of the four supporting results.

## Not duplicates

lem-sfb-borel-quotient-proper-geometry vs lem-sfb-reductive-borel-pair-structure: the latter assumes reductivity and includes root data; the new assertion applies to arbitrary smooth connected affine groups and supplies smoothness/regular integral geometry for their already represented homogeneous quotients.

lem-sfb-borel-quotient-proper-geometry vs lem-sfb-algebraic-group-homogeneous-quotient: the existing node constructs a separated finite-type quotient and its flat coset projection; it does not assert properness, smoothness, regularity or geometric integrality. The new node assumes precisely that quotient interface and states these additional properties.

lem-sfb-borel-quotient-proper-geometry vs lem-sfb-flag-effective-picard-generators: the existing statement gives effective Picard generators, not quotient geometry.

lem-sfb-split-solvable-torsors-and-variety vs lem-sfb-perfect-solvable-unipotent-torus: the existing statement constructs the unipotent radical and torus quotient, but gives neither Zariski triviality of arbitrary torsors nor the underlying variety or Picard triviality.

lem-sfb-split-solvable-torsors-and-variety vs lem-sfb-lie-kolchin-triangular-embedding: the existing node gives a triangular faithful representation; it does not give splitting series, torsor triviality or Picard groups. The new node records the further consequences 16.52, 16.55 and 16.56.

lem-sfb-split-solvable-torsors-and-variety vs lem-sfb-affine-space-invertible-trivial: affine spaces alone omit the torus factor and the general solvable torsor theorem.

lem-sfb-split-solvable-torsors-and-variety vs lem-sfb-ufd-invertible-module-trivial: the latter is an algebraic criterion for a module over a given UFD, not a group-structure/torsor theorem.

lem-sfb-rosenlicht-product-unit-factorization vs lem-sfb-normal-big-cell-character-functions: the existing node constructs specific rational functions on a reductive big cell, whereas the new node factors every global unit on arbitrary integral product varieties.

lem-sfb-smooth-generic-trivial-line-descent vs lem-sfb-smooth-integral-fibre-vertical-divisors: the existing node identifies divisors supported outside an already specified dense open base. It does not assert that a generic-fibre trivialization of a line bundle comes from the base, or identify its entire vertical divisor without first shrinking the base.

lem-sfb-smooth-generic-trivial-line-descent vs lem-sfb-regular-space-divisor-line-dictionary: the existing node is the divisor/line dictionary for one regular space; it contains no generic fibre or smooth-map descent assertion. It can be reused when splitting the new node.

lem-sfb-smooth-generic-trivial-line-descent vs lem-sfb-smooth-dvr-generic-line-extension: that node extends a line bundle from a generic fibre of a family over a DVR, whereas this statement descends an existing generically trivial bundle to the base for an arbitrary regular integral base.

lem-sfb-smooth-generic-trivial-line-descent vs lem-sfb-regular-group-rigidified-line-extension: the existing node concerns extending rigidified lines on a group family, not all invertible sheaves on a smooth integral-fibre morphism.

lem-sfb-borel-quotient-proper-geometry vs lem-sfb-smooth-dvr-generic-line-extension: the existing statement extends invertible sheaves from a generic fibre over a DVR; it does not state any homogeneous quotient properness or geometry.

lem-sfb-borel-quotient-proper-geometry vs lem-sfb-smooth-integral-fibre-vertical-divisors: the existing statement assumes a smooth map with integral fibres and proves its vertical divisor comparison over a specified dense open; the new node establishes the homogeneous quotient's smoothness/integral geometry and properness, which are hypotheses rather than conclusions of that divisor result.

lem-sfb-smooth-generic-trivial-line-descent vs lem-weil-pbc-completion-dimension: the existing node states dimension invariance for a Noetherian local completion; it does not assert that an invertible sheaf trivial on the whole generic fibre is pulled back from the base.

lem-sfb-smooth-generic-trivial-line-descent vs lem-weil-pbc-flat-fiber-local-depth: the existing node states a depth formula for flat ring maps; it does not assert that an invertible sheaf trivial on the whole generic fibre is pulled back from the base.

lem-sfb-smooth-generic-trivial-line-descent vs lem-weil-pbc-flat-fiber-prime-height: the existing node states the height formula for a flat ring map; it does not assert that an invertible sheaf trivial on the whole generic fibre is pulled back from the base.

lem-sfb-smooth-generic-trivial-line-descent vs lem-weil-pbc-flat-height-formula: the existing node states the dimension/height formula for flat Noetherian ring maps; it does not assert that an invertible sheaf trivial on the whole generic fibre is pulled back from the base.

lem-sfb-smooth-generic-trivial-line-descent vs lem-weil-pbc-flat-over-regular-with-regular-fibre: the existing node states regularity of a flat local algebra with regular base and closed fibre; it does not assert that an invertible sheaf trivial on the whole generic fibre is pulled back from the base.

lem-sfb-smooth-generic-trivial-line-descent vs lem-weil-pbc-polynomial-presentation-height-field-extension: the existing node states a height identity for polynomial presentations after scalar extension; it does not assert that an invertible sheaf trivial on the whole generic fibre is pulled back from the base.

lem-sfb-smooth-generic-trivial-line-descent vs lem-weil-pbc-pth-root-cotangent-dimension: the existing node states a cotangent-space dimension identity for a purely inseparable root algebra; it does not assert that an invertible sheaf trivial on the whole generic fibre is pulled back from the base.

lem-sfb-smooth-generic-trivial-line-descent vs lem-sfb-dvr-binomial-local-geometry: the existing node states the singularity and local dimensions of xy=pi^e; it does not assert that an invertible sheaf trivial on the whole generic fibre is pulled back from the base.

lem-sfb-smooth-generic-trivial-line-descent vs lem-sfb-smooth-trait-curve-local-properties: the existing node states regularity and local dimensions of smooth relative curves over DVRs; it does not assert that an invertible sheaf trivial on the whole generic fibre is pulled back from the base.

lem-sfb-smooth-generic-trivial-line-descent vs lem-trf-polynomial-log-chart-regularity: the existing node states log regularity and the dimension formula in a polynomial logarithmic chart; it does not assert that an invertible sheaf trivial on the whole generic fibre is pulled back from the base.

lem-sfb-smooth-generic-trivial-line-descent vs lem-trf-polynomial-strict-local-coordinate-dimension: the existing node states dimensions of strict henselizations of polynomial coordinate localizations; it does not assert that an invertible sheaf trivial on the whole generic fibre is pulled back from the base.

## Review by Q44

I read Milne Theorem 18.15 and the preceding associated-bundle convention on printed p.390; I then read the complete proof of 18.32 and its Borel specialization on pp.395--396. For the new geometry input I read 5.24--5.28 (p.105), 7.15 (pp.142--143) and 17.6--17.9 (pp.353--354); for solvable groups I read 16.52, 16.55 and 16.56 (pp.343--344), together with the UFD/Picard discussion A.79. For the units input I read 12.48--12.50 (pp.246--247), including its explicit product formula. For generic descent I read Stacks algebra.tex 00ON (lemma-dimension-base-fibre-equals-total), more-algebra.tex 0AG0 (lemma-regular-local-UFD), and divisors.tex 0AGA (lemma-weil-divisor-is-cartier-UFD); this is explicitly an agent-formulated consequence filling the source's omitted argument. I rejected 0DLQ after reading it: it only concerns a local algebra over a valuation ring and does not state the needed lemma. I did not cite it.

In step 1 I opened the existing homogeneous-quotient statement and checked that it really gives test-scheme coset fibres and fpqc local lifts, so Yoneda gives the torsor identity written in the proof. The new geometry statement supplies every smooth/integral/regular/proper hypothesis later used. Borel existence uses the elementary maximal-dimension argument for smooth connected closed subgroups of a finite-dimensional group; the zero-dimensional identity case is included. Split solvability and Zariski sections come from the new solvable statement, which applies to B without requiring G reductive.

In step 2 I opened lem-pc-fpqc-descent and checked clauses 1 and 3: effectiveness, full faithfulness and rank-one descent are all stated. The cocycle, tensor map and the section for a restricted character are written out, so no unspecified associated-bundle theorem is used. The open local sections may be chosen as a finite cover since Q is finite type; q is also a faithfully flat finite-presentation morphism. Thus the fpqc hypotheses hold.

In step 3 the Rosenlicht node states precisely the formula applied to u(xy). The new geometry statement with identity subgroup provides integrality for G and B; no unproved reduction from a possibly disconnected group is made. I opened lem-weil-pbc-proper-reduced-algclosed-global-sections-product: it explicitly identifies global sections with one copy of F per connected component. Here Q is nonempty connected and reduced by step 1, so it gives exactly F. Its use and fpqc module descent are declared generic tool uses in split_report, not as an undeclared route change.

In step 4 I checked the sign rather than copying the source loosely. The relation [gb,z]=[g,lambda(b)z] forces t(gb)=lambda(b)^(-1)t(g), so u=t/t(e) restricts to lambda^(-1) and u^(-1) extends lambda. The earlier one-line observation follows from the cited product-unit statement; it is not hidden in a new node. In step 5 the same relation makes (g,z) -> s(g)z invariant with lambda(b)=a(e,b), giving L_lambda -> L with the displayed action. Rosenlicht applies to integral separated finite-type G and B, and full faithfulness of the cited descent statement really descends this isomorphism. All formulas are identities of regular morphisms, so nilpotent test algebras are not silently replaced by F-points.

In step 6 I checked that the chosen local section reaches the generic point (Q is integral), and that the solvable node states Picard triviality after every field extension, in particular F(Q), not just over F. The generic descent node has precisely the regular integral separated finite-type base and source and smooth integral-fibre map produced by step 1. I checked its divisor argument above and the multiplicity-one point. It has weaker and independent hypotheses than the Borel Picard-surjectivity clause, so it is a genuine supporting lemma, not that clause relabelled.

Small cases: G=1 and G=G_m or G_a have B=G and Q=point; restriction is the identity and the remaining groups vanish as predicted. SL_2/B=P^1 gives a characteristic generator and Pic(SL_2)=0; PGL_2 gives the expected nontrivial cokernel in Pic(G), so I have not incorrectly made the characteristic map surjective. Non-reductive split solvable G is retained. The generic descent statement for f=id is tautological; projections A^1_S and G_m,S pass, while reducible fibres would permit individual vertical components and are explicitly excluded. All new nodes have complete self-contained statements with empty proof/proof_deps, and no step exceeds 2000 characters. Every step citation has a verbatim quote in citations.json. I preserved the item statement, original search history and provenance metadata.

## Unfinished work

The four supporting nodes intentionally remain statement-only stage-1 items. No Lean has been written or compiled. Delivery checks follow below through the required server dry run.
