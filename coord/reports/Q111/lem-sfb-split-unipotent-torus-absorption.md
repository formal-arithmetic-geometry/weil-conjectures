# Stage 1 delivery: lem-sfb-split-unipotent-torus-absorption

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-split-unipotent-torus-absorption.json: item, statement unchanged, now split into six steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-split-unipotent-torus-stable-series.json: one new statement-only structural node, unsplit, no Mathlib match.
- citations.json: verbatim statements for every direct proof-step citation.
- searches.jsonl: search command's unedited log. milne.txt is a sandbox-only pdftotext reading aid.

## Attachments

None. Searched lean/WeilConjectures both for the exact blueprint id and for split torus, unipotent, split-solvable and filtration terminology. The only unipotent matches concern biproduct matrices. Searched lean/Sheaf as well: SplitUnipotentSeries supplies a definition, and the affine quotient file cites torsor triviality; neither proves this item or the new structural lemma. No Lean was written and no compiler or build command was run.

## WANTED

WANTED: Brian Conrad, Linear Algebraic Groups I (Stanford, Winter 2010), notes typed by Sam Lichtenstein, edited February 8, 2020, Appendix D.3, proof of Theorem D.3.2, printed pp.86–87, for lem-sfb-split-unipotent-torus-stable-series. URL: https://math.stanford.edu/~conrad/252Page/handouts/alggroups.pdf . The notes are absent from this repository's literature; no download or repository edit was made. I read the relevant primary-source passage through the web reader to check the arbitrary-field formulation. It builds a normal split-unipotent series with vector-group quotients, linearizes the torus actions and refines by weight lines. The new node's local source record explicitly identifies this wanted structural input. The item is marked proof_origin.by=agent, rather than claiming its expanded arbitrary-field proof is printed in Milne.

## What was wrong or missing

The live item was unsplit. Its arbitrary-field assertion agrees with Milne Proposition 16.54, printed p.344. I did not dispute or alter it. The nearby solvable-torus-complement and triangular-section-conjugacy statements are over algebraically closed fields and cannot supply a rational conjugator over arbitrary k. Milne Corollary 16.24 likewise assumes perfect k; using it unchanged would add an unavailable hypothesis. The new lemma replaces this hidden structural input with its precise split-unipotent, arbitrary-field version. Nothing here invokes reductive-group rational conjugacy or the item’s ancestors, so it does not introduce a circular conjugacy argument.

The inherited blueprint.from.node is null. The required ancestor command prints exactly that a node created for this item has blueprint.from.node=None. This live lineage was retained; the exact absorption place and added filtration place are recorded, with the inherited via list extended for the new node. Read the current blueprint/latest six-functor unit and its direct-images proof (3); this is its inherited supporting alteration branch, not a change to chapter or unit routes. Whole-blueprint searches for split solvable, unipotent torus, unipotent, crossed homomorphism, central series, vector group, torus stable and 16.54 found no equivalent blueprint statement (the single unipotent hit was the unrelated curve Sylow/trace lemma).

## What could not be finished

No unresolved gap in the item's assembly proof relative to its explicit cited nodes. The new equivariant-series node is intentionally statement-only, as required for a one-level split; its proof belongs to a later stage-1 item. One new node, zero new Mathlib leaves. Existing Mathlib leaves for fppf-cover and finite-presentation base change are reused.

## Not duplicates

lem-sfb-split-unipotent-torus-stable-series vs def-sfb-split-unipotent-series: the existing node defines an arbitrary subnormal additive series; it does not give a new series invariant under a prescribed torus action or linear quotient actions.

lem-sfb-split-unipotent-torus-stable-series vs def-sfb-split-solvable-right-torsors: a definition of splitness and torsors, not an equivariant filtration theorem.

lem-sfb-split-unipotent-torus-stable-series vs lem-sfb-unitriangular-coordinate-filtration: that node filters the ambient unitriangular matrix group. Intersecting with U need not give smooth connected additive quotients over an imperfect field. The new node gives those exact properties for a split U and the prescribed torus action.

lem-sfb-split-unipotent-torus-stable-series vs lem-sfb-unipotent-central-additive-subgroup: the existing node assumes perfect k and gives one central additive subgroup, with no action invariance; the new node assumes split U and works over arbitrary k with torus invariance and explicit quotient weights.

lem-sfb-split-unipotent-torus-stable-series vs lem-sfb-nilpotent-connected-central-series: the existing node assumes perfect k and produces smooth connected central terms, not additive quotients with prescribed torus characters.

lem-sfb-split-unipotent-torus-stable-series vs lem-sfb-smooth-diagonal-additive-crossed-vanishing: the existing node proves principality of an additive-subgroup cocycle over an algebraically closed field, rather than a structure theorem about split U over arbitrary k. Its scalar conclusion is proved directly in item step 3 by Laurent coefficients, so no arbitrary-field generalization of that node is created.

lem-sfb-split-unipotent-torus-stable-series vs lem-sfb-solvable-torus-complements: the existing node gives an isomorphism from a maximal torus to a quotient over an algebraically closed field, not a torus-stable additive filtration over k.

lem-sfb-split-unipotent-torus-stable-series vs lem-sfb-triangular-quotient-section-conjugacy: the existing node gives conjugacy of sections over an algebraically closed field, not a filtration. Neither its proof nor its unrecorded hypotheses are used.

lem-sfb-split-unipotent-torus-stable-series vs lem-sfb-perfect-exponent-p-vector-group: the existing node identifies a perfect-field commutative exponent-p group with a vector group; it supplies neither the arbitrary-field split-kernel series nor linearization of the given action.

No Stacks tag is asserted for this new structural result, so there is no same-Stacks-tag duplicate pair. Sources are the actual Milne proposition and wanted Conrad passage, rather than an invented tag.

## Review by Q111

I read Milne Definition 14.61 and paragraphs 14.62–14.68 (printed p.299), the triangular normal-series argument of Theorem 16.21 (p.330), Corollaries 16.23–16.24 (p.331, explicitly perfect-field only), the crossed-homomorphism proof of Theorem 16.27 (p.333), the split-kernel case of Summary 16.29(d) (p.334), and Propositions 16.54–16.55 (p.344). Proposition 16.54 supplies the exact field scope and rational-unipotent conjugacy of the item. For the new node I read the above Conrad primary-source passage, which explains the stronger arbitrary-field filtration rather than applying 16.24 outside its hypotheses. The structural argument behind the statement is: construct successive central split vector subgroups in characteristic p (or use the characteristic-zero derived series), pass to the split quotients, linearize the split torus action on each vector quotient, and refine each by weight lines. Pulling these lines back gives normal smooth connected terms, additive quotient schemes and the monomial weights stated. This is a substantive structure lemma, not a reformulation of torus absorption: it says nothing about T inside U semidirect D or conjugators. All other calculations stay in the item.

Step 1 uses only the explicitly given semidirect multiplication: projection is a homomorphism and its first coordinate satisfies the displayed crossed identity. It never treats c as a homomorphism or assumes a:T->D injective. Step 2 uses exactly the new node's existence of invariant smooth geometrically connected additive terms, kernel identities and monomial quotient actions; all its hypotheses are already present for U and the induced split-T action. The tail series is literally a tail of that output, so the splitness of each kernel is justified without claiming all subgroups of split unipotent groups are split.

Step 3 is the elementary Laurent coefficient comparison written in full. I checked the identity and sign: for nonzero n the result is b(1-X^n), while n=0 forces zero. It uses independent formal variables, not evaluations on k-points, so finite fields and nonreduced test algebras present no issue. It is one coefficient argument with no omitted comparison theorem or separate structural subclaim.

For step 4 I opened the complete statements of lem-sfb-affine-normal-quotient-geometry and lem-sfb-split-unipotent-affine-torsor-section. The former says the quotient is represented, has exactly the kernel, is faithfully flat finitely presented and is a right torsor. The latter gives a section over any affine finite-type base for a smooth connected kernel with an additive split series. Normality and all finiteness/smoothness conditions hold for V_i and V_{i+1}; Spec k is the stated affine base. I additionally opened lem-trf-fppf-covering-base-change and read Stacks Tag 021O, topologies.tex label lemma-fppf part (3), and opened lem-weil-pbc-qcqs-morphism-permanence clause (3). They provide exactly the base-change properties of the fibre map. The torsor isomorphism restricts explicitly to the fibre, so no general torsor-base-change lemma is hidden. This review corrected the initial draft by adding these base-change citations rather than calling those scheme facts elementary. These two reused Mathlib leaves are generic scheme tools, not trace-formula or proper-base-change arguments.

Step 5 is the explicit finite induction using the preceding steps: w_0=1; lift the scalar principal element b to v; set w_{i+1}=w_i v. The formula v^{-1}c_i(t)(a(t)·v) has quotient -b+f_i(t)+chi_i(t)b=0. Invariance keeps all factors in V_i; the kernel identity factors the morphism through V_{i+1}. No new lemma is cited after proving it inline, and the induction has its base, inductive claim and terminal term. Step 6 takes u=w_m^{-1}, the correct sign for the requested uTu^{-1}. The coordinate formula (1,a(t)) proves the subgroup-scheme factorization on all algebras, not just containment of geometric points.

I tested U=1 (empty filtration), T=1 and D=1, the trivial character, nontrivial weights over F_2 where rational density would fail, characteristic p weights divisible by p, additive U with a character action, the Heisenberg group and length-two Witt-type unipotent extensions. The filtration concerns group quotients, so it does not assert U is a vector group or force such extensions to split as groups. The imperfect-field hypothesis is specifically protected by splitness in the new structural input. All six steps are shorter than 2000 characters; none hides a longer unreviewed lemma. New node has no proof or proof dependencies, uses complete inline definitions, and remains unsplit. Queries and actual results are copied from the search-command log; no unavailable service was mislabeled. The abstract group central-series hits and GroupExtension.IsConj source were read and do not state the algebraic group scheme assertions.
