# NX: lem-sfb-weyl-cell-hom-gluing

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-weyl-cell-hom-gluing.json: item, statement, split; not a Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-rank-one-cell-enlargement.json: new statement-only geometric prerequisite, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-bruhat-inversion-factorization.json: new statement-only geometric prerequisite, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every node used by every numbered proof step.
- searches.jsonl: actual msearch.py searches and their returned digests. The sandbox also retains write_split.py, the item-specific construction script.

## Attachments

None. I searched lean/WeilConjectures for the exact item tag and for Weyl cells, normalizers, and root subgroups, and searched the proposed new ids and concepts in both source roots. The normalizer results concern Hopf ideals of matrix-group closures, not split reductive root-cell gluing. No exact project declaration was found. No Lean file was written or compiled.

## Literature wanted

WANTED: Brian Conrad, Reductive Group Schemes, archival local copy of https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Theorem 6.2.1 and its proof, printed pp.198--200, for lem-sfb-weyl-cell-hom-gluing; Theorems 4.1.4, 4.1.7 and 5.1.13, pp.110,112--113,143--145, for lem-sfb-rank-one-cell-enlargement; Theorem 1.4.12 and the preceding longest-element paragraph, pp.37--38, for lem-sfb-bruhat-inversion-factorization. I read these places online; no PDF was downloaded and no SGA source was used.

## Audit findings and corrections

The item was unsplit and had no proof. Its statement is unchanged. There is no released repair note for it and no previous item/report in the sandbox to recover. Its inherited searches and blueprint provenance are retained, with this run's logged searches appended. The chapter, unit, imported fields and maintainer-owned fields are not changed.

Conrad sketches the word-length argument after the positive-unipotent homomorphism construction; simply invoking that sketch or a full-root-extension theorem would either hide the assigned work or create a cycle. The split now carries the prefix induction explicitly. A rank-one enlarged cell permits the simple-reflection calculation without assuming that a point of a general test algebra has a Bruhat decomposition. Intersections of intermediate translated cells are then dense on geometric fibres, and schematic density extends the resulting morphism identities over arbitrary bases. This is essential for nonreduced rings: equality on geometric points alone would not suffice. The existing smooth-fibrewise-density node supplies exactly the missing scheme-theoretic assertion, so a provisional candidate for an additional density lemma was not created.

The statement's source calls the cover a consequence of Corollary 1.4.14. Its argument needs the explicit inversion-root support of the factors in Bruhat decomposition, which the existing longest-cell node does not state. The new inversion-factorization node states that geometric input rather than a second version of the desired open-cover clause. The item itself proves the cover by conjugating those factors.

The latest blueprint path is literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/. I read its unit and direct-image proof, in particular (3), as well as the imported chapter/unit records. The inherited from.node is null, also returned as None by blueprint_refs.py ancestor; I retain it and its full via chain rather than invent an imported ancestor. The exact source place at the end of that chain is expanded for each new node. Global blueprint searches for big cell, open cell, Bruhat, Weyl, rank-one cell, inversion root, Levi, fibrewise dense, schematically dense, and the relevant Stacks tags produced no blueprint theorem stating either new geometric assertion. No chapter or unit route is changed; this item is a supporting node, not the unit's key theorem.

## Not duplicates

lem-sfb-rank-one-cell-enlargement vs lem-sfb-relative-root-rank-one-centralizer: the latter constructs the rank-one reductive centralizer and its roots and tangent module; it does not give the open immersion V^- x K_alpha x V^+ into G or its open-cell restriction.

lem-sfb-rank-one-cell-enlargement vs lem-sfb-relative-dynamic-subgroups: the latter gives the open immersion for abstract attracting subgroups and their centralizer. The new result identifies those subgroups with the specified all-but-one root products and identifies the centralizer with the torus centralizer K_alpha over arbitrary rings. This identification is not a one-line specialization.

lem-sfb-rank-one-cell-enlargement vs lem-sfb-standard-parabolic-levi-charts: the existing statement is over an algebraically closed field and assumes a semisimple group; it does not assert the relative enlarged open chart over a possibly nonreduced ring.

lem-sfb-rank-one-cell-enlargement vs lem-sfb-integral-simple-reflection-gauss-chart: that statement concerns an explicit integral partial chart for a rational semisimple simply connected realization, before constructing its integral ambient group. Here an arbitrary split reductive group is already given and its full rank-one centralizer replaces the three rank-one cell factors.

lem-sfb-rank-one-cell-enlargement vs lem-sfb-split-root-subgroup-weyl-calculus: root calculus provides the ordinary cell and ordered root products; it does not provide the enlarged cell with the full rank-one centralizer in the middle.

lem-sfb-bruhat-inversion-factorization vs lem-sfb-bruhat-longest-cell-charts: that statement gives a cell factor V^w but leaves its root support unspecified. The new statement identifies it as U_{I_w}, with I_w explicitly defined by w^{-1}c negative, which is needed to put every cell inside n_w Omega. It asserts the scheme factorization, not just a choice of cell dimensions or an arbitrary translated flag-chart cover.

lem-sfb-bruhat-inversion-factorization vs lem-sfb-unipotent-root-intersection-products: the existing statement computes intersections of two unipotent radicals; it does not state that the Bruhat stratum is the product of that subgroup, a Weyl representative and the Borel factors.

lem-sfb-bruhat-inversion-factorization vs lem-sfb-split-bruhat-affine-stratification: that statement provides unnamed affine strata in the quotient G/B over a field. It neither labels them by Weyl elements nor supplies their root-supported factors inside G.

lem-sfb-bruhat-inversion-factorization vs lem-sfb-simple-bruhat-double-coset-product: that statement is a multiplication rule for double cosets in a semisimple simply connected group, with no inversion-root coordinate identification. The new statement is for arbitrary pinned split reductive groups over an algebraically closed field.

Both new nodes are independent group geometry and mention no H, f_N, F_+/- or E_alpha. Neither restates the overlap or multiplication clause of the item. No new node shares a Stacks tag with an existing node: there is no Stacks tag for either reductive-group geometric assertion. The existing density and morphism-gluing lemmas are reused.

## Review by NX

I checked B--E of delivery-errors.md against the node statements and sources, including both copies of those sections. The item follows the omitted calculation in Conrad Theorem 6.2.1, printed p.199, and is marked as an agent proof because the details here are supplied by me. The two new nodes have statements only, empty proof/dependency arrays, separate actual searches, and the required blueprint/creation fields. Each has a strictly geometric task below the item. None assumes a reduced, connected, Noetherian, semisimple or simply connected base/group where the item does not.

For the rank-one node I read Theorem 4.1.7(3),(4), p.113, the rank-one open immersion of Theorem 4.1.4, p.110, and Theorem 5.1.13 and its proof, pp.143--145. The proof to be split later chooses an integral multiple of a rational cocharacter vanishing on alpha and positive on every other simple root. Its attracting groups are precisely V_alpha^+/- and its zero-root centralizer is K_alpha; the dynamic open immersion then gives the enlarged chart. This needs the relative identification of these groups, so it is a real geometric lemma rather than an elementary reordering step. The ordinary rank-one cell inside K_alpha gives the asserted restriction to Omega. In semisimple rank one the other-root products are trivial and the chart is K_alpha=G, so this test passes. The cocharacter can be zero in that case. With a central torus factor the torus is retained in K_alpha, and no root-spanning hypothesis is used.

For the Bruhat node I read Theorem 1.4.12, p.38. Its explicit definition of the roots of U_w is exactly the I_w in the new statement, with inverse w^{-1}, not w. I also read the longest-element paragraph on p.37 and Corollary 1.4.14 on p.39. The result is geometric and is never applied to arbitrary ring-valued points in the item's proof. For SL2 its two factors are U_{I_1}=1 and U_{I_s}=U_alpha, giving B and U_alpha n_s B. With no roots there is one stratum, the torus itself. No rank-two target homomorphism is inserted.

Step 1 uses the root-calculus statement's any-order product coordinates and conjugation action, together with the given homomorphism and equivariance hypotheses. Moving the torus factor explicitly verifies both semidirect-product laws and the B^- left/B^+ right formula. This is elementary assembly, not an invocation of a missing commutator theorem.

Step 2 uses exactly the new Bruhat statement's inverse-root support and partition, and root calculus's conjugation of root groups. Conjugating each factor of v gives a negative root, so the geometric point lies in the stated C_w. Openness comes from the given cell and translation. Coverage of geometric fibres implies coverage of the underlying scheme, including nilpotents in the base; no scheme identity is inferred from geometric points here.

Step 3 uses the new enlarged chart and its precise open-cell restriction. The E_alpha restriction to N intersect K_alpha is used at n_alpha, which the new geometric statement explicitly places in K_alpha. The other-root reflection assertion is written out from sign coherence, and root calculus identifies the conjugated subgroups. The displayed two-line calculation of b_alpha(n_alpha x) uses no unseen property of a cited node.

Step 4 cites the identity-component statement for irreducibility of each connected geometric fibre and the smooth-fibrewise-dense-open statement for injectivity on structure sheaves. I opened both statements: the first concerns all locally finite-type groups over algebraically closed fields and therefore applies to every reductive geometric fibre; the second permits arbitrary base schemes and arbitrary base change, with precisely fibrewise density as its hypothesis. I checked the base and induction step for prefixes and the domain on which every intermediate value is defined. A finite intersection of nonempty translated opens in an irreducible fibre is nonempty and dense. The conclusion extends by applying the injective sheaf map to coordinate functions of affine H, not by testing only on fields. Negative letters are replaced using the explicit root-calculus square n_alpha^2=alpha^vee(-1), and torus factors preserve the cell. There is no assumption that a general normalizer point is a single constant Weyl image over a disconnected algebra; only the chosen constant word representatives are needed.

Step 5 invokes the exact existence/uniqueness clause of the existing morphism-gluing statement after proving the overlaps by the displayed substitution. This generic tool is the only off-unit proof citation; it is declared in split_report.tool_uses. The newly introduced f is a morphism at this stage; multiplicativity is still to be proved.

Step 6 uses the same two density/irreducibility statements and root coordinates. The relevant domains are G, U^- x G and T x G, all smooth; their geometric fibres are integral, as is also seen affine-locally from polynomial or Laurent polynomial rings over the integral group-fibre rings. The equality opens are stated explicitly. Thus the extensions are identities of morphisms on those domains even when A has nilpotents.

Step 7 uses the Bruhat statement's longest element, root calculus to conjugate the ordered root products, and the equality clause of morphism gluing. Applying the already established left-equivariance successively for n_0, v and n_0^{-1} proves left U^+ equivariance. Left Omega equivariance then follows by its three-factor formula, and the C_w cover gives multiplicativity for every first factor. Restriction to the triple loci is now exactly the item's final equation. The empty-root case was checked directly: G=T and f=f_N. Products of rings and dual-number bases require no special descent because every extension used schematic, rather than geometric-point, equality.

I read the actual msearch hits, including root-pairing Weyl inductions, Geck Lie-algebra constructions, general scheme gluing, topological open subgroups, and the reduced-source ext_of_isDominant lemmas. None states either new result or the item as a one-line specialization. The reduced-source equality lemma cannot replace universal schematic density over a nonreduced base. The recorded searches reproduce the actual tool/query text and results; no service failure was counted as absence. Earlier inherited searches remain untouched. Every non-elementary step cites its needed node statements; citations.json records those statements verbatim. The longest non-elementary step is 1267 characters, so there is no step over the 2000-character audit threshold.

## What remains

The two new geometric nodes are intentionally unsplit stage-1 prerequisites. No part of the item's seven-step argument is left implicit except what their statements and the existing cited statements explicitly supply. No statement dispute was found.

## Validation

The server check_dag and review_split commands passed before packaging. The required delivery dry run and final push are recorded below after completion.

Required dry run completed successfully: `deliver.py NX lem-sfb-weyl-cell-hom-gluing --no-push` printed `OK (not pushed)` at commit `4e03ffc7909`, with server preflight passed. Final direct delivery follows this successful dry run, as authorized by the worker brief.
