# Stage-1 report: lem-a1-affine-relation-local-basis-reduction

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-affine-relation-local-basis-reduction.json: statement, split into eight proof steps; unchanged statement and statement dependencies. Mathlib searches find no exact match.
- citations.json: one verbatim statement quotation for every step-node citation.
- report.md: this report. No new DAG nodes; no new Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for affine groupoids, finite flat groupoids, groupoid bases and semilocal submodule bases. No declaration states the item. The only relevant broad groupoid hit, InvariantAffineNeighbourhoods.lean, concerns invariant affine neighbourhoods, not this basis reduction.

## WANTED

None. All sources used are present.

## Issues and changes

The item was unsplit and its sandbox empty. Its statement agrees with Stacks 03BM's local reduction, with source and target interchanged in the last basis selection (which is valid by symmetry), and with 03C8 in exactly the orientation stated. No STATEMENT-DISPUTED or source error is needed. Its inherited blueprint place was stale as detailed below; this is a provenance error, not a mathematical source error. Its inherited rank claim holds on all points, not only maximal points; step 5 now gives the specialization/generalization argument using invariant clopen rank strata. No constant-rank hypothesis is added.

I did not cite lem-a1-affine-relation-comparison-preparation: it assumes a functorial equivalence relation whereas this item's hypotheses give a groupoid plus a surjective tensor comparison. The more general groupoid-basechange-polynomial-norm node supplies precisely the base-change operations and finite locally free projections needed here. Flat tensor exactness supplies invariants independently. This avoids applying preparation under hypotheses the item does not have.

The first version of the argument could have silently taken a scheme's finite locally free projection to mean that its coordinate algebra has the required finite principal-open module cover. Step 6 instead cites finite flat pushforward, projectivity of affine sections, and the finite projective standard free cover. These are generic tool uses, declared in split_report.tool_uses where off-unit; the unit route and chapter are untouched. The old searches in the item remain, and all five searches run in this sandbox are appended exactly as logged by msearch.py. Two semantic phrasings and the other three search tools find no statement of the groupoid theorem. The free-of-flat module hits presuppose finiteness and flatness over the invariant ring, which is what must be proved.

## Not duplicates

No new nodes are proposed. Reused the existing Stacks 03C1/02M9 semilocal submodule basis, 03C8 groupoid basis descent, 03BI invariant rank strata, 03BJ integral invariants and 03BL orbit-fibre nodes. Whole-blueprint searches for invariants base change and semilocal gave no equivalent blueprint statement; nearest blueprint ancestor is lem-a1-affine-hc0. Its current main-20261015 file contains only the H_c^0 statement, and the old master proof is the compact-support argument, not a quotient argument. The inherited from.place reference to a fourth paragraph was stale. I corrected that place to name the indirect via-chain and the actual Stacks 03BM proof location, retaining the ancestor and via identifiers. This provenance discrepancy does not change the mathematical statement or source route.

## Unfinished work

None in the mathematical split. No Lean writing, compiler or build was used. Server validation and direct delivery are performed after this report.

## Review by N6

I read groupoids.tex Tag 03BM, its entire proof, Tag 03BI's statement and rank-invariance proof, Tag 03BK including its flat-equalizer argument, Tag 03BL's statement and orbit argument, and Tag 03C8's statement and basis orientation. I also read algebra.tex Tag 03C3 and Tag 03C1 and morphisms.tex Tag 02KB, and the current main-20261015 ancestor blueprint. This split follows the local Stacks argument, without using the full quotient proposition to prove its own ingredient. There are no new nodes whose statements need a separate source audit.

1. Step 1 uses the existing flat-local-extension-given-residue-field statement with K=k(T), which is infinite even when k is finite. Its conclusion gives the specified local extension; flat-local-hom-faithfully-flat applies to every chosen nonzero local D. Both cited statements explicitly give the conclusions used.
2. Step 2 uses flat-over-localization in the direction from flatness over C_p to flatness over C. The exact sequence is the defining equalizer, with an injective first arrow. Flat-tensor-exact explicitly preserves both its injectivity and exactness. Thus D is embedded in E and really is its full invariant ring; this is not assumed and does not require faithful flatness of C -> D.
3. Step 3 uses only the basechanged-groupoid clause of affine-groupoid-basechange-polynomial-norm; I read that complete statement, which explicitly includes finite locally free projections for arbitrary base change. Integral-invariants applies to the resulting affine groupoid with its now identified invariant ring. Orbit-fibres explicitly states surjectivity and the existence of one arrow between two points of the same fibre, not merely an unspecified chain.
4. Step 4 checks both directions of the relation between maximal ideals and the closed fibre, using integral-maximal-contracts-maximal and integral-prime-over-maximal-maximal. Finite-closed-map-finite-fibres explicitly supplies a finite underlying source fibre. Fixing one maximal point and mapping this finite fibre by the target surjects onto all maximal points by step 3. No claim that E was already a finite D-algebra is used.
5. Step 5 uses the complete invariant-rank-strata statement, including positivity, orbit invariance, clopenness and the fibre-dimension interpretation. The remaining argument is elementary: every prime is contained in a maximal ideal and a clopen subset containing a specialization contains its generalizations. Nonzero E ensures at least one maximal point and hence r >= 1.
6. Step 6 uses the three affine module statements as stated: the pushforward of the rank-one structure module is finite locally free, its affine sections are finite projective, and a finite projective module has a finite principal-open free cover. Reducing a free chart modulo a point computes the same coordinate fibre dimension from step 5. Thus the rank in the semilocal-module hypothesis is exactly r, with no extra global freeness assumption.
7. Step 7 uses tensor-right-exact only for surjectivity. The balancing formulas for the tensor reassociation and their inverse are written explicitly, so no separate comparison theorem is hidden. The equality sigma_D(d)=tau_D(d) makes tau_D(E) a D-submodule; surjectivity gives its E-linear generation, in the correct sigma_D-module structure.
8. Step 8 applies semilocal-submodule-basis after verifying each of its hypotheses in the preceding steps. Choosing preimages of its finitely many basis vectors is elementary. Affine-groupoid-basis-descent explicitly has the tau(x_j)-basis via sigma orientation, and concludes both the D-basis and the same tensor-comparison isomorphism, so it supplies exactly the final conclusions.

I checked B1-B10: no new unsplit node, duplicate or hollow definition; citations carry precise tags and labels, and search records correspond to actual commands. For C1-C8 I read every cited statement, included all non-elementary inputs, avoided the too-strong preparation node, and declared off-unit generic tools. For D1-D5 the actual semilocality, rank and generation arguments remain in the item, rather than being renamed as new nodes. For E1-E7 the rings, module structures and hypotheses were checked as above. Every proof step is under 1000 characters, hence none exceeds the 2000-character long-step threshold.

Small cases: the identity groupoid has r=1 and the construction gives E=D; the pair groupoid of a finite product of copies of a field gives the expected rank equal to the number of points; a nontrivial finite group acting trivially has a nonsurjective tensor comparison and is correctly excluded. Starting with finite residue field causes no obstruction because k(T) is infinite. For an initial product with different source ranks, localization in the invariant ring selects one clopen rank factor, as the maximal-orbit argument confirms. The zero ring case is excluded by A != 0 and by the proved injection D -> E. No assumption of Noetherianity, reducedness or algebraically closed residue field is introduced.
