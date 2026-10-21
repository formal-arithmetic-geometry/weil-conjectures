# NJ stage-1 delivery: lem-sf-perfect-tensor-roos-completion

## Files written

- dag/nodes/sec-six-functors/lem-sf-perfect-tensor-roos-completion.json: statement, now split in twelve steps; no exact Mathlib match.
- citations.json: one entry per step/node citation, quoting the complete statement actually used.
- report.md: this report. searches.jsonl records searches run through msearch.py.

New nodes: 0. New Mathlib leaves: 0. The existing DAG already contains the needed proper sublemmas. The item itself is not a Mathlib leaf: ordinary adic completion equivalences do not state the derived tensor coaugmentation or its coherence diagrams.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for Roos, perfect-completion and quotient terminology. The existing PerfectTower and PerfectTowerQuotient modules address different assertions. No project declaration found states all clauses of this item.

## WANTED

None. All sources needed for this one-level split are locally available. No SGA source was used.

## Audit and corrections

The sandbox initially contained no node, report or search log, only dispatcher brief markers. The current repository node was used as the starting point; its inherited searches and all metadata were retained. No mathematical statement was changed. Definition dependencies for DVRs, projective modules and finite generation were added. The blueprint search for “tensor quotient coaugmentation” found no duplicate, and ancestor returns thm-sf-kunneth-relative through lem-sf-point-fibre-derived-tensor. Searches for complete projectives and surjective module-complex towers, together with the whole DAG concept searches, led to reuse of the generic lemmas rather than new nodes.

The imported source reference to Tag 031B needs care: that lemma assumes separatedness as well as finite generation. I did not infer separatedness from that lemma. Step 3 instead proves completeness and separatedness by embedding a finite projective module as a split summand of a finite power of the complete ring. The source reference to the ringed strict-tower theorem alone also does not supply the termwise-product model; step 6 explicitly invokes the exact-products comparison, checking exact products and the tower Grothendieck hypothesis. These repairs concern the proof, not the statement.

The use of the DVR factorization for general complete DVRs is deliberate. The existing local-field coefficient-stage node only treats finite extensions of Q_l, which would not cover this item. Step 11 uses the general DVR unit-times-uniformizer-power lemma instead, proving that the image of pi is nonzero and nonunit before applying it. No hidden local-field hypothesis enters.

## Review by NJ

I read the item and its parent route, the chapter/unit records, and the current main-20261015 relative-product node. This item realizes the ordinary module-completion ingredient in the final Spec k specialization; it does not change the unit's Kunneth argument. I read sites-cohomology.tex Tag 0941 (lemma-derived-limit-is-ok), including the actual kernel/product sequence in its proof, and algebra.tex Tag 031B (lemma-when-finite-module-complete-over-complete-ring). I also read the projective lifting/splitting argument at Tags 05CE/05CF and the finite-projective characterization in algebra.tex. There are no new nodes whose independent statements or sources need review.

For step 1 I opened def-weil-pbc-projective-module and def-weil-finitely-generated-module: together they give a finite generating surjection and its splitting. Tensoring and summing the splittings proves precisely finite projectivity of each total term; this is not an appeal to an unrecorded tensor-closure theorem. def-pc-tensor-complex-sheaves supplies the finite diagonal sums and signed differential. Step 2 checks the inverse balanced maps on generators and the differential; I added the explicit tensor-quotient identification so that M tensor A_j is not silently substituted by M/pi^j M.

For step 3 the projectivity definition supplies the same splitting, and the assumed ring completeness supplies the coordinate inverse in R^a. The idempotent equality is checked in every quotient and then lifted using injectivity of R^a into its inverse limit. It works for rank zero and needs no noetherian completeness theorem. Step 4 is the explicit countable lifting recursion for 1-t; its kernel calculation is the definition of a compatible family. This also verifies that the proposed zero-second-coordinate augmentation is a cochain map.

For step 5 I opened lem-weil-pbc-surjective-module-complex-tower-limit: it applies to varying quotient rings with scalar-linear surjective transitions, not merely split transitions. The stated limit ring is R by the item's assumption. The proof then computes cycles and boundaries in the exact coordinate convention of the item, so it proves that the prescribed augmentation is a quasi-isomorphism, rather than relying on a noncanonical cone isomorphism. The sign in d(a,b)=(da,fa-db) and the correction a-dz are both used explicitly.

For step 6 I opened every cited statement: projective-module-flat, module-bounded-flat-kflat, derived-monoidal, kflat-scalar-tower-realization, exact-products-roos-comparison, and small-module-diagrams-grothendieck. Their conclusions provide, respectively, flat terms, K-flat total models, the derived tensor identification, the exact unit/transition equations, the zero-coordinate comparison with the derived augmentation, and the needed Grothendieck module/tower categories. The site is a singleton and the tower index is countable and small. Products are exact by coordinatewise choice. A functorial free-module evaluation gives flat resolutions. I read the derived-monoidal blueprint source and checked the K-flat/base-change locations in more-algebra.tex and sites-cohomology.tex; I do not claim that Tag 0941 itself states these separate auxiliary results.

For step 7 I opened bounded-above-projective-kprojective and kprojective-derived-hom-bijection. I also read Mathlib's actual isKProjective_of_projective at HomotopyCategory/KProjective.lean:113 and Qh_map_bijective at DerivedCategory/KProjective.lean:43. These cover arbitrary derived morphisms from our bounded projective models; merely treating strict maps would not suffice. The written homotopy formula on the shifted coordinate has a minus sign, and substituting it into dH+Hd gives the correct difference. This establishes canonical naturality and model independence without assuming that every derived isomorphism was already a supplied strict isomorphism.

For steps 8 and 9 I checked the claimed equality on pure tensors in each degree, using the stated total tensor differential and the derived-monoidal constraint statement. The associator preserves the ordered three factors, the symmetry contributes exactly (-1)^(rs), both unitors multiply, and the coefficient unit is 1 in every quotient. The shifted coordinate is zero along each route. Quotient maps are ring maps, so the explicit formulas commute for every m >= n >= 1, including m=n. Thus these steps prove the diagrams as maps to the fibre and do not infer them just from projections in D(R).

For step 10 I opened compact-support-roos-cofinality and finite-free-strict-tower-transport. Their statements contain the finite-free tensor/product comparison and compatibility with the actual augmentation, as well as the canonical derived-functor normalization. The hypothesis is an actually finite free S over R. The balanced tensorator formula is verified directly, and exact scalar tensor computes the derived extension. For step 11 I opened dvr-unit-times-uniformizer-power and the cofinality statement again: the former has the general DVR hypotheses that apply to S, and the latter gives the block restriction, its quasi-isomorphism, and its zero-coordinate augmentation equation. The positive free rank shows that pi survives in S; locality forces its valuation e to be positive. Thus the pi-adic tower is exactly the subsequence ej of the sigma-adic tower. The direction of the comparison is restriction from the full tower to the subsequence; the derived square uses its inverse where needed.

For step 12 the cofinality statement explicitly includes composition, and the displayed scalar multiplication proves the identity and successive-extension tensorator equations. Products of ramification indices correspond to the same composite restriction. I replaced a potentially ambiguous composition-order notation by “two successive cofinal restrictions equal r_(ef)”. The calculation includes repeated coefficient rings and identity extensions.

I checked delivery-errors B through E against these files: no new statement-only nodes, duplicated lemmas, invented search records, or clauses repackaged as new lemmas; no use of a cited proof instead of its statement; no hypothesis of finite residue field, geometric origin, or split quotient transitions. Every citation has a full verbatim statement in citations.json. Generic cross-unit tools are declared only in split_report.tool_uses. I checked dependency reachability for the reused tools; none reaches this item. Each proof step is shorter than 2000 characters, and the algebra calculations are steps of this item's own claims rather than concealed new general lemmas.

Small-case checks included a zero complex or a zero-rank projective term, R in degree zero, two shifted copies of R (including odd/odd symmetry and characteristic two), the two-term complex [R --pi--> R] with torsion cohomology, m=n=1, identity R->R, and the ramified map k[[u]]->k[[t]], u=t^2. In the ramified example the two quotient towers have indices j and 2j and are not identified termwise; the cofinal block map is essential. None of these tests revealed a statement dispute.

## Not duplicates

No new nodes were created; no new/existing pairs require distinction.

## Unfinished work

None for the authorized one-level stage-1 split. Existing unsplit dependencies remain their own items. No Lean was written or compiled.

## Validation

Server review_split passed. The required deliver.py --no-push exited 0 and printed “OK (not pushed) deliver/NJ/lem-sf-perfect-tensor-roos-completion at a51299858ac: preflight passed”. This included the server preflight, DAG and split checks. The direct delivery runs the same gate before pushing.
