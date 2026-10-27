# Q69: lem-sfb-rank-one-frobenius-extension

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-rank-one-frobenius-extension.json`: statement, split into five steps; statement unchanged, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-rank-one-semidirect-presentation.json`: new statement-only geometric presentation lemma; unsplit, no Mathlib match.
- `citations.json`: a verbatim statement quote for every cited node at every step.

## Attachments

None. I searched the live `lean/WeilConjectures` for the exact blueprint tag and the rank-one reductive, SL2, root-parametrization and Frobenius-extension concepts. The rank-one files under LinearAlgebraicGroup concern Weil characters and cyclic extensions, not these reductive group schemes. There is no declaration stating the item.

## WANTED

None. The needed literature is already present.

## Problems and corrections

The imported item is a correct rank-one extension statement, but has no proof. Its inherited searches are retained. The reference to 23.16 is a consequence/application of 23.14 rather than an additional construction. The proof of 23.14 in Milne uses the semisimple reduction and lifting through PGL2; I give an explicit agent proof using the SL2 map of 20.32/21.24 instead. This is a choice below the unit, not a change of the unit's direct-image/alteration route. It replaces the lifting diagrams by a scheme-theoretic coroot-kernel calculation.

I read the current `literature/blueprint/latest` unit and direct-image proof, and retained the inherited chain from its alteration prerequisite through root-datum isogeny realization. `blueprint_refs.py ancestor` reports null for this imported-created chain; both item and new node retain that null, with a precise place and the correctly extended via list. No unit record is changed: this is not the unit's key statement.

The source's Theorem 20.33 has a missing semisimple-rank-one hypothesis in its first sentence and reversed derived-group descriptions in its last paragraph. The existing classification node already corrects both. I use only its corrected rank-one content to check the new lemma; neither mistake is reproduced. No statement dispute or correction is needed in this item.

## Unfinished work

Only the new presentation lemma remains unsplit, as required for a one-level split. It does not assert existence of an extension between two groups, mention a torus homomorphism between groups, or assume root/coroot Frobenius compatibility.

## Not duplicates

lem-sfb-rank-one-semidirect-presentation vs lem-sfb-opposite-root-sl2-parametrizations: the existing node constructs a map SL2 to H and specifies root restrictions and the coroot; it does not assert equivariance on all SL2 or give a faithfully flat SL2 semidirect T presentation and its scheme-theoretic kernel.

lem-sfb-rank-one-semidirect-presentation vs lem-sfb-split-rank-one-classification: the classification gives three matrix models for a pair (H,T), not a presentation associated to any specified normalized SL2 map, its multiplication, faithful flatness or its full kernel.

lem-sfb-rank-one-semidirect-presentation vs lem-sfb-central-torus-semisimple-derived-product: the latter covers a central torus times the derived group with finite kernel; here T is a maximal torus, generally noncentral, the product is semidirect with SL2, and the kernel is a one-dimensional torus rather than a finite group.

lem-sfb-rank-one-semidirect-presentation vs lem-sfb-reductive-central-pushout-reconstruction: that node uses a universal cover and the full centre with an anti-diagonal finite central kernel. It does not give the root-character action of the entire maximal torus on SL2 or the coroot kernel used here.

lem-sfb-rank-one-semidirect-presentation vs lem-sfb-reductive-rank-one-reflections: that node supplies rank-one centralizers, reflections and an SL2 map, not this faithfully flat quotient or its kernel. The triangular-diagonal-kernel and Borel root-product nodes concern solvable or unipotent subgroups, not H.

I searched all DAG nodes for semidirect, coroot graph, SL2, rank one, the literature numbers 20.32/20.33 and 21.11, and searched the whole imported blueprint for SL2, semidirect, coroot, rank one and rank-one semidirect presentation. No blueprint node states either the item or the new presentation. Mathlib semantic searches used two different formulations of the presentation, as recorded in searches.jsonl, plus LeanSearch, Loogle and actual source grep. The source reads were RootSystem/Hom.lean:45-75 (isogenies TODO), GroupTheory/SemidirectProduct.lean:190-220 (abstract lift only), and the matrix/group types in the returned signatures. None is a group-scheme presentation. Every recorded new search was actually run with msearch.py; there were no unavailable services.

## Review by Q69

I read Milne, Algebraic Groups (iAG2017), Proposition 23.14 and its preceding reduction 23.11--23.13, printed pp.488--490, and Proposition 23.5 with formula (146), printed pp.485--486. I also read Proposition 20.32, Theorem 20.33 and Corollary 20.34, printed pp.418--419, and Theorem 21.11 with 21.23--21.24, printed pp.429--432. These provide the rank-one SL2 models and root-normalized coroot map. The item's arbitrary-dimensional torus, characteristic exponent convention, both roots and all-test-algebras assertions are retained. I checked delivery-errors B--E against these sources and the actual statements of every cited node.

Step 1 uses `lem-sfb-opposite-root-sl2-parametrizations` precisely for existence of v_i and its two root-group isomorphisms and coroot formula, all of which its statement explicitly gives. The new presentation node is then used for its explicit E multiplication, faithful flatness, equivariance and identification of the entire kernel. Each H_i is split reductive and has exactly two roots, as both applications require. I opened both cited statements; no fact is borrowed from a cited proof.

For the new node I checked that its assertion is a strictly smaller geometric input: one H and one normalized v are fixed; there is no second reductive group and no extension problem. Its only nonstandard constructions, the SL2 matrix functor and the semidirect law, are written explicitly, and reductivity, roots and coroots point to their actual notion nodes. It is a statement only, with no proof or proof dependencies. As an independent truth check, use the corrected three matrix models: for a torus times SL2 the map is ordinary multiplication M d(s) on the SL2 factor; for a torus times GL2 it is M diag(t1,t2), with kernel M=d(s), (t1,t2)=(s^-1,s); for a torus times PGL2 it is [M] times the diagonal class, whose inverse image in SL2 is the determinant-one diagonal torus. In each case the central-torus coordinate in the kernel is 1. Thus the full kernel is exactly (d(s),gamma-coroot(s)^-1), not merely its reduced points. Faithful flatness follows in the GL2 and SL2 cases directly from these matrix presentations; in PGL2 one uses the scalar-torsor local matrix representatives, then the same determinant-one factorization. Normalized choices of v differ by diagonal conjugation (Milne 21.24), which preserves this formula and both root images. These checks are explanation in the report, not a proof hidden in the unsplit statement.

Step 2 is the elementary binomial/matrix calculation: qth powers preserve sums by iterating the characteristic-p binomial formula and preserve products; applying this to the entries of MN and to ad-bc proves the group law and determinant identity. The polynomial morphism fixes the coefficient field in its coordinate-algebra map. I explicitly distinguished it from absolute Frobenius, which would not in general be F-linear. This avoids an incorrect base-field identification.

Step 3 cites the new presentation only for its displayed multiplication (also its target multiplication). The root assumption beta(h(t))=alpha(t)^q makes the upper-right and lower-left weights exactly match under entrywise powers. Multiplication in E then verifies the homomorphism without any implicit lifting theorem or root-generation theorem. This is elementary substitution into the two multiplication formulas.

Step 4 cites the new node for faithful flatness and the kernel formula, and `lem-sfb-faithfully-flat-group-quotient-universal` for descent of a homomorphism trivial on the scheme-theoretic kernel. I opened that node: it requires affine finite-type groups and faithful flatness of coordinate algebras, and gives a unique homomorphism, exactly as used. Here E_alpha is affine finite type by the presentation, and H_1,H_0 are so by reductivity. The coroot equality kills every k_alpha(s) over every algebra, hence kills the full kernel scheme. This is not a check only on algebraically closed field points. Evaluation on (I,t) and (x_plus/minus(a),1) proves the restrictions directly.

Step 5 uses no additional theorem: parametrization changes are affine-line automorphisms fixing zero. Degrees of inverse polynomials multiply, so they are scalar maps. I wrote the actual substitution and constants b_plus/minus times a_plus/minus^(-q). The monomial map has free coordinate algebra of rank q by monic division, so the root image is the whole subgroup scheme; surjectivity on A-points is not asserted. All steps are below 2000 characters and no non-elementary inline identification is hidden in a long step.

Small cases checked: q=1 in characteristic zero or e=0; SL2 to PGL2 with the scalar mu2 kernel; the reverse direction in characteristic two with q=2 (the coroot condition allows it, and the full scheme-theoretic computation still works); GL2 with its two-dimensional diagonal torus; and products with arbitrarily many central G_m factors. In characteristic two mu2 is not reduced, so the all-algebras kernel calculation is essential. For A=F[epsilon]/(epsilon^2) and q=2 the root map kills epsilon, consistent with faithful flat surjectivity of schemes and not with pointwise bijectivity. The torus finite-index hypothesis is allowed throughout, though this explicit construction actually needs only the displayed root/coroot identities. No hypothesis is added, dropped or used without being available.

The initial proof was empty. I corrected no target statement: the substantive additions are the explicit semidirect input, the equivariance calculation, the scheme-theoretic kernel check, coefficient-fixed polynomial Frobenius, and the distinction between subgroup-scheme image and arbitrary algebra-points. All citation quotes are copied verbatim from the actual statements. No Lean files were written and no compiler or build was run.

The first full dry run found a citation-format issue: the new statement grouped notion references inside comma-separated brackets, which the gate does not parse. I changed them to separate single-id brackets and regenerated the exact citation quotes; the mathematics and dependencies are unchanged.
