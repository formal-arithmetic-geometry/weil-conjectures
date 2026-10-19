# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fibre-component-relative-associated.json`: statement, split into five steps; no full Mathlib match. The existing Mathlib leaves supply its geometric and algebraic inputs.
- `citations.json`: sixteen verbatim statement quotations, one for every citation in every step.
- `searches.jsonl`: actual search-tool log. The node retains its historical Q31 searches and appends the Q64 searches run here.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item id, relative assassin, associated point, AssociatedPoint and associatedPrimes. There is no declaration stating the item. The isolated `Associated` hit in Curve/DivisorIdealSheaf concerns associated elements and is unrelated. No upstream-master sorry declaration is used as evidence of completion.

## WANTED

None: all mathematical sources used below are available locally.

## Findings and corrections

The item statement is unchanged, including flatness and local finite type, and its six statement dependencies are unchanged. Flatness is unnecessary for this particular conclusion but has been retained. No Noetherian hypothesis on the base, global quasi-compactness, reducedness, or irreducibility has been added.

The node was unsplit and its sandbox contained no previous item or report. Its source already correctly identifies Divisors 05AT, 02OJ and 05AH. The existing definition node `def-sc-associated-points` has a correct statement but its source incorrectly calls associated points Tag 02OZ; the correct tag is 02OJ (definition-associated). I have not edited that other node. This metadata discrepancy does not affect the statement being cited, and the correct source is named in the proof and here.

The chapter, unit and inherited blueprint ancestry were read. The item is a component-closure helper in the existing specialization/nearby-cycle branch below the contracting-local-term theorem, not the unit's key node. Its blueprint location is made explicit, with the inherited ancestor and via chain retained. Whole-blueprint searches for `associated`, `associated point`, `fibre component` and `minimal prime`, and whole-DAG searches for 05AH, 05AT, 01T6 and the corresponding concepts found no blueprint duplicate of the item. No unit or chapter record is changed.

## Not duplicates

No new nodes are proposed. In particular, I reused `pqf-lem-locnoeth-lft`, `lem-weil-pbc-lft-base-change`, `lem-weil-pbc-noetherian-minimal-prime-associated`, `lem-weil-pbc-associated-prime-localization-depth-zero`, `lem-weil-pbc-affine-open-spec-points` and `lem-weil-pbc-affine-open-stalk-localization`, rather than creating scheme/fibre variants of these existing statements. The elementary generic-point/minimal-prime argument is a proof step, not a new node or a rephrasing of the item as an auxiliary lemma.

## Review by Q64

I read Divisors 05AH (lemma-minimal-support-in-ass), including its statement that generic points of components of a locally Noetherian scheme are associated, 02OJ (definition-associated), 02OK (lemma-associated-affine-open), and 05AT (definition-relative-assassin). The item's fibrewise assertion and union conclusion agree with these. I expanded the affine argument using Algebra 00ES (lemma-irreducible), 05BV (lemma-ass-minimal-prime-support) and 05BZ (lemma-localize-ass), whose hypotheses and conclusions I read. I also read Morphisms 01T4 and 01T6 and Properties 01OV. The proof is labelled agent-written because it combines these sources into an explicit affine proof rather than reproducing the short stalk-support proof of 05AH verbatim. There are no new-node sources to audit and no forbidden SGA route is used.

Step 1 uses the fibre definition's actual base-change square, the base-change lemma's local-finite-type conclusion, and the finite-type/locally-Noetherian lemma's local version. The Noetherian-ring definition, spectrum definition and locally-Noetherian definition justify the elementary field-base check: the only two ideals of a field are finitely generated. Thus the Noetherianity supplied is on the fibre, not on X or S. I opened each of these six cited statements; none is being asked for a stronger clause than it states.

Step 2 uses the locally-Noetherian definition to choose a Noetherian affine neighbourhood, the affine-open point theorem to represent y by a prime, and the generic-point, spectrum and component definitions. The argument for minimality is written out: a strict smaller prime gives an irreducible closure containing B, maximality forces equality, and membership in the affine closed set V(p) contradicts strict containment. The closure formula follows directly from the defining closed sets V(I), as in 00ES. This is a routine argument from definitions and the cited affine identification, so the step is elementary. It uses no theorem about associated points and does not conceal a replacement for the item.

Step 3 invokes exactly the existing minimal-prime associated-prime statement. Its hypotheses are a Noetherian ring and a minimal prime, both established already. Its conclusion is the element with annihilator p used in the next step. This is not merely a definition of association.

Step 4 invokes the existing associated-prime localization statement, which explicitly says that the maximal ideal of A_p is associated, and the affine-open stalk theorem's clause (c), which explicitly identifies O_(T,y) with A_p. The associated-points definition then gives exactly the first conclusion of the item. The only transport is of the equations defining an annihilator under a ring isomorphism; I wrote why this preserves both maximality and the annihilator equality. All three cited statements were opened and copied into citations.json. These geometric and algebraic inputs are existing Mathlib leaves; no off-unit non-leaf theorem or route replacement is used.

Step 5 uses the relative assassin's explicit union in the item's unchanged statement and the fibre definition's homeomorphism to f^(-1)(t). Membership in the t summand proves the final assertion. There is no appeal to an unstated theorem about flat relative associated points or to an unidentified pullback comparison.

For the B--E checks, there are no new definitions, no unsplit auxiliary proofs, no same-tag new nodes and no hidden clause moved into another node. Proof dependencies are exactly the union of the step citations. Every citation has a full verbatim statement quotation. No proof step exceeds 2000 characters. I checked small cases: the empty fibre has no such y; the identity on Spec K gives the associated prime (0); Spec K[e]/(e^2) has its unique prime associated (annihilator of e), so reducedness cannot be assumed; and the two generic points of Spec K[u,v]/(uv) each give a minimal associated prime. A non-Noetherian base still causes no problem because the fibre, not the base, is locally of finite type over a field. The proof never asserts that every point is associated or that the fibre is globally Noetherian.

The Q64 semantic searches returned generic-point topology and Jacobson-fibre results rather than this associated-point theorem. A second phrasing returned the same topology vocabulary. The corrected Loogle query `"associatedPrimes"` returned module results; the earlier unqualified query reported an unknown identifier and is preserved as such, not interpreted as evidence of absence. The targeted Mathlib grep found Localization.lean lines 40 and 128; I read both statements and reused the already-existing DAG leaves for them. No full Mathlib match is claimed.

## Unfinished work

None in the split. Validation and delivery are performed with the required server-side dry run and delivery command; no Lean, compiler, Lake, local DAG checker or git command is run by this worker.
