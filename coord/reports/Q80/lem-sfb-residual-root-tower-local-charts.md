# Stage-1 delivery: lem-sfb-residual-root-tower-local-charts

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-residual-root-tower-local-charts.json: statement, split into nine proof steps; no exact Mathlib match.
- citations.json: 37 verbatim statement quotations, one for every step/node citation.
- searches.jsonl: genuine msearch log for this item, retained with the sandbox.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. All mathematical dependencies already exist.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, residual-root-tower, rootTower, and the active-parameter notion found no declaration proving the item. The matching notions in Sheaf/SNCUniversalResidualCharts are not a proof of this entire algebraic chart statement.

## WANTED

None. The required geometric and ring-theoretic arguments are in the obtained Stacks source. The current blueprint supplies the higher-level motivation, not a theorem asserting this entire explicit chart construction.

## Corrections and scope

The imported statement had the ambiguous sentence “It has an affine open cover W” immediately after naming both B and B_J. The definition A_W over A/(t_j) and the displayed fibre product show that this means B_J. I replaced only that pronoun by B_J; there is no changed hypothesis or conclusion and no statement dispute. No repair note exists for this item. Its live state was unsplit; no earlier sandbox proof or report existed.

The original source place mentioned standard-etale criteria without proof steps. The split now cites the existing unit-binomial finite-etale lemma and ind-etale permanence; it does not cite a definition as if it proved flatness or etaleness. Every other former implicit comparison is written on coefficients and generators.

## Blueprint and duplicate searches

I read the chapter record, the unit record, and the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and direct-images.proof.md. This is supporting geometry for paragraph (3), open direct image. No chapter or unit route changes. The item is not a unit key statement, so no unit record is edited. The ancestor command reports null, as already recorded in this created chain; its exact existing from.place and via are retained.

Whole-DAG title/statement searches covered normal crossings, root towers, roots of units, regular intersections, parameter quotients, weakly etale permanence, and affine finiteness. Tag searches included 0BIA, 00UB and 00UC. Blueprint_refs searches for “root tower”, “strict normal crossings”, “unit roots”, “residual”, “parameter”, and “Kummer” gave no identical blueprint statement; returned weight/parameter and finite Kummer statements do not assert residual full-root charts. Existing root-local-presentation, labelled-root-geometry, boundary-parameter-criterion, unit-binomial-finite-etale, root-tower-profinite-base-change and ind-etale-stability provide the needed inputs; no new statement-only duplicate was made.

## Mathlib search assessment

I ran msearch on this item with LeanFinder, Loogle, grep and LeanSearch, including a second phrasing about splitting the compatible-root algebra over disjoint subsets. The exact queries and actual results are in searches.jsonl and were appended to mathlib_searches without changing the inherited records. All services answered. The StandardEtalePresentation and StandardEtalePair hits were inspected in Mathlib/RingTheory/Etale/StandardEtale.lean: these are presentations of a single standard-etale algebra. Mathlib/AlgebraicGeometry/Sites/Proetale.lean defines the topology and its weakly-etale covering property. Neither states the residual SNC chart or infinite-generator comparison. Polynomial.Splits.scaleRoots and scalar-tower splitting declarations concern polynomial splitting, not these quotient/filtered-colimit algebras. The second LeanFinder results concern splitting-field constructions and do not apply to general coefficient rings with zero divisors. Thus the whole item is not a Mathlib leaf.

## Not duplicates

No new nodes. Existing nodes were reused throughout; there are no new/existing same-tag pairs requiring distinction.

## Review by Q80

I checked the split against delivery-errors B through E with the node statements and source text open. For the item I read Stacks etale.tex Tag 0BIA (lemma-strict-normal-crossings), including both directions of its local-parameter argument; algebra.tex Tag 00NQ (lemma-regular-ring-CM) and Tag 00NR (lemma-regular-quotient-regular); etale-cohomology.tex Tag 03PL (lemma-kummer-sequence), especially its explicit unit-root algebra; algebra.tex Tags 00UB/00UC (definition-standard-etale and lemma-standard-etale); and proetale.tex Tags 097J through 097N (base change, composition, filtered colimits, permanence, and weak etaleness). There are no new-node sources to review. I mark proof_origin agent because the complete residual infinite-root statement and its assembly are my argument, although these individual ingredients follow Stacks.

Step 1 uses the actual quasi-compactness and etale finite-type consequences stated by qcqs-morphism-permanence and kun-etale-lfp. Affineness of B and separatedness of Y discharge the respective source/target assumptions. Affine-source-morphism-separated supplies separatedness over k. The boundary definition explicitly includes regularity of every scheme-theoretic intersection, even the empty-index intersection B, so it really gives B_J, not just its reduced support. Finite type of the quotient is checked by projecting a finite list of algebra generators.

Step 2 checks the exact hypotheses of transverse-prime-ideal-parameters(a): each singleton quotient is regular codimension one, the total intersection is regular with codimension equal to the number of branches, and all ideals are prime. Localization does not merge the distinct primes contained in the point prime, since contraction recovers each one. The regular-normal statement identifies the local ring as a domain; the explicit cancellation proves that the named equations differ by units from the supplied parameter generators. This avoids taking an unnamed-parameter conclusion as a theorem about our specific t_d.

Step 3 uses localization-at-prime-of-quotient for the correct quotient local ring, and regular-local-generators-regular-sequence for quotienting a permuted parameter system. The residual images still generate a maximal ideal with precisely the dimension number of generators. The statement of the parameter definition supplies exactly the criterion being used. No regularity of the pro-etale algebra R is presumed.

Step 4 invokes the boundary-parameter criterion only after checking regular Noetherian B_J and the residual product equation at every point. The criterion allows the unit ideal away from the boundary. The labelled-root-algebra-geometry statement explicitly allows disconnected or reducible labels; its neighbourhood clause supplies precisely the distinct integral active branches and units outside them. This is the important reason to reuse this stronger existing node rather than assume that an intersection of original components stays irreducible. That lemma does not require a connected base. It is used solely after its residual parameter-system hypothesis is proved.

Step 5 uses the affine-fibre-product statement to identify R_W as a genuine base change of the supplied affine pro-etale object. Weakly-etale-composition-base-change states the two needed permanence facts. For every inactive root the unit-binomial lemma requires exactly an invertible exponent and a unit constant; both are checked, including the Bezout computation in characteristic p. Successive finite adjunctions and their filtered colimit are handled by ind-etale-stability, whose statement includes composition, filtered colimits, and ind-etale implies weakly etale. The affine-morphism lemma applies since source and target are affine. The site convention really uses weakly etale objects, so this establishes its precise conclusion without silently imposing that the original U be ind-etale.

Steps 6 and 7 cite the root-tower base-change result for its actual full-root scalar-extension formula, the fibre-product result for the scheme being considered, and polynomial/quotient/colimit universal properties for the maps. I wrote both maps, all defining relations, all power transitions, and checked both composites on every generator and coefficient. The index is the small directed set of positive prime-to-p integers; lcm gives common indices. These two steps are elementary presentation calculations, not an uncited comparison theorem. They do not assert that base change kills residual nilpotent roots: T_J is the separately given residual tower.

Step 8 uses localization-away's actual fraction construction and basic-open-pullback's equality of inverse-image principal opens. The inactive product is already a unit, so the displayed inverse formulas prove equality of the two localizations and their open scheme structures. This is an elementary calculation, with no separate lemma hidden in the word “identifies”.

Step 9 uses the profinite clause of root-tower-profinite-base-change, which explicitly states that U[P] is affine pro-etale and identifies the tower, opens and ring base changes. Equality of the comparison squares is checked on each coefficient and named root, including each transition; this is stronger than just asserting abstract isomorphism. Weakly etale composition applies to U[P] over B. Empty P, zero coefficients, empty boundary and either empty active/inactive index set preserve these universal-property formulas. If B_J is empty the cover is empty. Empty J recovers the original chart calculation. The residual example A=k[x,y], t_1=x, t_2=y, J={1} gives the expected root tower in y over k[y]; on y invertible the active set is empty and all roots are absorbed into D_W. This checks both behaviours in a small case.

Every cited node was read in the live DAG, every citation quote was checked as a literal substring, and proof_deps is exactly the union of uses. No dependency reachable from these citations reaches this item. All nine proof steps are below 2000 characters; the generator construction is split into its forward and reverse maps for readability. No elementary new nodes, clause-restatement nodes, hidden proofs in new statements, or new source documents occur. Generic off-unit tools (regular-local parameter quotients, regular implies normal, etale finite-type, and weakly/ind-etale permanence) are declared in split_report.tool_uses with their purposes; they preserve the unit's route.

## Unfinished work

None in the stage-1 split. This delivery writes no Lean and runs no compiler, Lake, or library build. Delivery checks and push are recorded by the required delivery tool.
