# Worker report: lem-trf-point-transport-strict-quotient

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-point-transport-strict-quotient.json`: statement, split into nine proof steps; no exact Mathlib match.
- `citations.json`: 26 verbatim statement excerpts covering every step/node citation, including separate excerpts for the structure square and finite comparison in step 1.
- `report.md`: this report.
- `searches.jsonl`: the actual msearch command log, preserved as generated.

New nodes: 0. New Mathlib leaves: 0. No Lean files, compiler calls, or repository changes.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag, strict quotient transport, and point-transport notions found no declaration asserting all the strict transition, augmentation, naturality, and tower-descent clauses. The existing abstract naturality lemmas are not an attachment for this stronger strict statement.

## WANTED

None.

## Corrections and scope

The item's statement is unchanged. Its original proof was empty. I added the explicit arguments and the three statement dependencies defining inverse systems, the ambient derived category, and the coherent reduction tower. All original metadata and searches remain. The current item has no blueprint_update field; its recorded source is the main-20261015 blueprint, which I followed.

I read the chapter sec-trace-formula and unit sk-d-weil records. This is a technical realization of clause (3) of `prop-trf-rational-frobenius-integral-model.proof.md`, not a replacement for the Frobenius route of the unit. The blueprint speaks of taking the derived limit of compatible levelwise operators; the present proof supplies the strict common-representative maps that this requires. The explicit chain and localization argument is marked agent-written, not represented as a theorem asserted verbatim by the blueprint or by Deligne.

There was no saved item or report in the sandbox when work started. Existing msearch records in the repository item are retained; the five additional searches were actually run for Q131, their returned hits read, and their exact tool/query strings appended. LeanFinder was tried with two different phrasings. Loogle's sheaf pullback presentation hits were checked in `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`, especially pullbackIso at line 106 and sheafificationCompPullback at line 118. Those are useful construction ingredients, not the strict Frobenius tower theorem. All four search services used answered successfully.

## Unfinished work

None in this one-level split. The existing cited nodes retain their current status; no proofs of other nodes were edited.

## Not duplicates

No new node was created. I searched the whole DAG and the imported blueprint with point-transport and K-flat keywords. Existing `lem-weil-point-automorphism-restriction-natural` supplies the unbounded restriction-map naturality; `lem-weil-pbc-site-derived-tensor-descent` supplies the resolving-class localization. Creating either again would duplicate the DAG. The sibling `lem-trf-point-transport-cone-comparison-descent` concerns the subsequent entire-cone comparison; it is not used to prove this item. The item remains responsible for the strict finite quotient identities, not merely a citation of its own conclusion.

## Review by Q131

I read the full statement and empty proof of the item, its parent blueprint proof in the main-20261015 snapshot (especially clause (3)), the comparison definition including both (a) and (b), the complete point-transport definition, the coefficient and integral-category definitions, and every cited node's statement. For the homological inputs I also read Stacks sites-cohomology.tex: lemma-K-flat-resolution (06YS), lemma-derived-tor-quasi-isomorphism-other-side (06YT), lemma-factor-through-K-flat (0G7D), and lemma-derived-base-change (06YY), including their proofs where the resolving class is used. I read sites-modules.tex section-tensor-product (03EK) and definition-pushforward (03D6), whose pullback clause is the sheaf tensor construction. There are no new nodes needing independent source checks.

Step 1 uses the general point-automorphism restriction-natural node, which explicitly gives a chain map and naturality on *any unbounded complex*. This avoids imposing constructibility on P or P_n and avoids an unnecessary hypothesis that E has already been embedded in a fixed algebraic closure. I checked its hypotheses: g is an automorphism, k is algebraically closed, ell differs from its characteristic, and the completed coefficient sheaf is the actual inverse limit. The comparison definition gives the finite tensor insertion and the integral structure square. The displayed scalar calculation explains why its finite linearity agrees with the integral action on the quotient, so the result is O_E-linear.

Step 2 writes the action of the actual coefficient-induced transition on a pure tensor and checks the balancing relation. The additional citation `lem-weil-proetale-isomorphism-inverse-image` clause (3) states precisely the structure-square compatibility for *any ring homomorphism*, here A_(n+1) to A_n. The tensor definition and comparison (b) specify the map being computed. This is an elementary calculation on the presheaf map followed by the sheafification unit; it makes no assertion that every section of a sheaf tensor is a globally pure tensor. Equality of the pre-sheaf maps induces equality after sheafification.

Step 3 uses the restriction-natural node's strict chain-map naturality at t_n, and then the tensor identity from step 2. The inverse-system definition states exactly that these commuting squares are a tower map. Step 4 uses the displayed definition theta_n = kappa_(P_n) g^(-1)(r_n) from comparison (b) and naturality at r_n. Both maps are R-linear after restriction; neither step treats maps between different finite coefficient categories as maps over a common finite ring.

Step 5 checks tensor insertion naturality directly on x tensor 1, and combines it with the restriction-natural node for f_n. I checked the tensor-induced maps commute with the tower transitions on both sides. This establishes strict naturality before any localization. I did not replace it by the weaker statement that the maps are merely equal in a derived category.

Step 6 uses `lem-pur-derived-change-of-rings` clause (1), whose hypothesis is K-flatness of both complexes, not flatness of the quotient coefficient. The finite pullback is exact for this scheme isomorphism as stated in comparison (a). Restriction of scalars leaves underlying abelian sheaves unchanged by its definition; kernels, cokernels and cohomology therefore remain the same underlying sheaves. The exact-sections node explicitly says termwise sections preserve quasi-isomorphisms. These are sufficient to show both tower maps of a quasi-isomorphism are levelwise quasi-isomorphisms. I checked that unbounded complexes are allowed throughout.

Step 7 retains coherent towers by choosing the derived category of *module towers* as target, rather than identifying a tower in a derived category with a coherent derived diagram. The small-module-diagrams node applies to the one-object trivial ringed site with ring O_E and the small countable index. I wrote out why kernels and cokernels are pointwise, and why the homotopies induced from h are compatible with the actual transitions. Thus the functors factor through the source homotopy category and the target has the needed quasi-isomorphisms. The ambient-derived-category definition explicitly allows the equivalent homotopy-category localization.

Step 8 cites the site-derived-tensor-descent node only for its *first assertion*, the equivalence between the localization of the exact class of K-flat complexes with flat terms and D(R). Its statement actually includes that class, not merely arbitrary K-flat or bounded-above complexes. The site uses the project's small skeleton and containing universe, so its size hypothesis is met. The localization-universal-property node includes natural transformations and uniqueness, not just functors. The proof supplies the inverse-map equation and the resulting roof naturality explicitly. Hence this step proves independence of the common representative without requiring functorial choices of resolutions.

Step 9 uses change-of-rings clause (2) for the finite derived reduction represented by P_n, the reduction-tower definition for its transitions, comparison (a),(b) for the target, the complete-integral-category definition to know N_n is bounded constructible, and the finite-coefficient point-transport definition for the exact formula for iota. This proves the evaluation clause with the specified map, not just an isomorphic object. The bounded constructibility hypothesis is only used here; no derived completeness or invertibility of completion was used in steps 1-8.

I checked B-E of delivery-errors.md against the written files: no statement-only nodes with hidden proofs, no new restatements of clauses, no unsupported source-only citations, no dropped hypotheses, and no false inference about tensors preserving arbitrary quasi-isomorphisms. The generic off-unit tools are declared in split_report.tool_uses, with the particular statements used and reasons. I checked dependency reachability of the proposed citations for cycles back to the item; none was found. Every cited node is recorded by a verbatim excerpt in citations.json. All nine proof steps are shorter than 2000 characters.

Small-case checks: for the zero complex both strict equations and naturality are zero identities; for g equal to the identity all formulas become the usual quotient tensor-insertion identities; for n=1 the transition uses A_2 to A_1 with unit sent to unit, with no division by varpi; for a shift or an unbounded flat-term K-flat complex the argument is degreewise and uses no truncation; for an acyclic K-flat complex step 6 gives acyclic reductions even though the quotient ring is not flat. These checks explain why neither a boundedness condition nor a finite Tor-dimension assumption was silently introduced.
