# Q106: lem-per-admissible-modification-completion-density

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-admissible-modification-completion-density.json: statement, split in seven steps; not a Mathlib leaf.
- citations.json: literal statement quotations for all twelve step/node citations.
- report.md: this report.

No new nodes and no new Mathlib leaves. The sandbox also retains searches.jsonl, an extracted reading copy ilo.txt, and the item-specific write_split.py used to assemble the JSON. These are working material, not delivery nodes.

## Attachments

None. I searched the actual lean/WeilConjectures library for the item id, admissible blowups, strict henselizations and completion comparisons. The available blowup and strict-henselization declarations do not state this whole item. I read the existing upstream quotient theorem Algebra.IsStrictHenselization.surjective_quotient; it belongs to the existing quotient interfaces cited in step 4, not to this item. No Lean was written or compiled.

## WANTED

None. The relevant ILO PDF and Stacks TeX sources are present.

## Findings and scope

The released stage-1 repair note of 2026-10-24 and coord/changes/20261024-Q112-strict-completion-inputs.md authorize this exact interface and the admissible-modification-system input. I reconstructed its proof rather than reviving a historical proof graph. The item statement, source, stmt_deps, original Mathlib searches and blueprint provenance are unchanged. I added only the proof, proof dependency union, provenance of the proof, new actual searches and split report.

The crucial issue was that the completion map cannot be assumed flat without Noetherianness. Also, blowup does not commute with arbitrary base change. The proof instead obtains J^d/I^nJ^d by taking kernels between quotients of A by ideals containing sufficiently high powers of I. It then applies arbitrary base change of Proj to the reduced Rees algebra. ILO 2.4.3 writes I contained in J; the finite-generation monomial argument in step 1 replaces that by I^r contained in J, exactly as needed for the full-support admissible ideals of XX 4.4. This is a proof detail, not a changed hypothesis or statement dispute.

The latest ancestor blueprint proof was read at literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md. Its Step 3 is the historical ancestor of this auxiliary completion input through the preserved via chain. Whole-blueprint searches for completion, admissible, Rees, henselization and the combined strict-henselization quotient phrase found no blueprint node stating this item. The chapter and unit records and the three-level rules in SETUP.md were read; neither record is changed. The item is not the key statement of its unit.

## Tool uses

The split_report.tool_uses entries declare generic off-unit tools: lem-weil-pbc-etale-local-ring-triples, lem-sbc-etale-triples-localized-strict-henselization, lem-sbc-strict-henselization-surjective-quotient-core, lem-weil-pbc-strict-henselization-functoriality and lemma-nagata-filtered-colimit-finite-data. Their roles are respectively the geometric/algebraic dictionary, localization of the pointed colimit, quotient strict henselization, pointed uniqueness, and descent of finite elements/equations. None replaces a step of the perverse unit's route. The Proj arbitrary-base-change node is Lean-closed; the completion-mod-power node is already a Mathlib leaf. No top-level tool_uses approval is written by the worker.

## Not duplicates

No new nodes were created. In particular, I reused the admitted lem-per-admissible-modification-system for the filtered domination index, the existing completion-mod-power node, the existing arbitrary Proj base-change node, the existing quotient strict-henselization interfaces and the existing finite-data colimit lemma. I did not create a new node restating the fibre or strict-local clauses of this item.

## Review by Q106

I read ILO Expose XX 2.4.3 on printed p.364, the proof of 2.4.4 on p.365, and the whole XX 4.4 letter on pp.373-374, including its final Note. These are the item's sources and assert the reduced Rees comparison and corresponding strict-local completions without excellence. I also read Stacks algebra.tex Tag 05GG (lemma-hathat-finitely-generated), Tag 05WS (lemma-quotient-strict-henselization), etale-cohomology.tex Tag 04HX (lemma-describe-etale-local-ring), and constructions.tex Tag 01O3 (lemma-relative-proj-base-change). There are no new-node sources to check. Incidental SGA references in ILO are not used.

For step 1 I opened lem-weil-pbc-adic-completion-mod-power: its statement gives the canonical surjection and exact kernel I^NA' for every finitely generated I over an arbitrary commutative ring. The kernel is exactly what the further quotients need. The elementary monomial bound proves I^r contained in J from V(J)=V(I), without a Noetherian radical argument. The containment I^(n+rd) contained in I^nJ^d handles all degrees, including d=0. Quotienting by the image of L gives precisely the extended ideal LA', not a falsely assumed tensor injection.

For step 2 I opened def-nagata-rees-algebra. It defines the direct sum of J^d t^d with coefficientwise multiplication, which is all that step uses. The kernel square is explicitly calculated; its restrictions give the degreewise isomorphisms and their multiplicativity. It is an elementary kernel calculation, not a newly packaged lemma.

For step 3 I opened def-nagata-affine-blowup, lemma-nagata-relative-proj-base-change-arbitrary and def-nagata-strict-transform-blowup-comparison. The first gives Rees Proj, the second has arbitrary g with no flatness restriction, and the third fixes the actual lift on chart fractions. Reducing the graded algebra is scalar extension to A/I^n, so this invokes exactly their statements. I read Stacks 01O3 to check that arbitrary, rather than flat, base change is legitimate here. The proof explicitly identifies the arrow by its fractions, not merely an abstract fibre isomorphism.

For step 4 I opened lem-weil-pbc-etale-local-ring-triples, lem-sbc-etale-triples-localized-strict-henselization, lem-sbc-strict-henselization-surjective-quotient-core and def-sc-ring-strict-henselization. They supply respectively the geometric neighbourhood/triples colimit with its structural maps, its algebraic strict-henselization property after localization, the explicit quotient as a strict henselization of the quotient local ring, and uniqueness of the colimit object. The kernel I^nR lies in the maximal ideal because the chosen point is on the closed fibre. The quotient has the same residue field; the problem supplies the same separable closures. The quotient algebra action is the one descended from the local-ring quotient, not an arbitrary action. None of these nodes assumes Noetherianness. The local-ring identification is taken at the actual corresponding points of the infinitesimal fibres from step 3.

For step 5 I read clause 3 of lem-weil-pbc-strict-henselization-functoriality in full: it asserts uniqueness of the local homomorphism over the scheme map with specified residue-field inclusion. This ensures the quotient comparison is induced by the actual map H_J to H'_J and that domination maps commute. Step 4 identifies each quotient with the geometric strict-local ring of the fibre through the pointed colimit; the common residue closure makes the residue map the identity. Thus we do not infer naturality from the mere existence of an abstract ring isomorphism.

For step 6 I opened the currently admitted lem-per-admissible-modification-system statement. It supplies the filtered preorder, which is the only part used; I did not cite its proof or ask its statement for a strict-local congruence it does not contain. I opened lemma-nagata-filtered-colimit-finite-data: it explicitly gives representatives at one common stage and descent of finitely many ring-expression equations. Nonemptiness follows from J=I, and one may quotient mutual domination to a directed set. The injectivity argument writes an actual finite sum in I^nC, descends its coefficients and equality, and applies the stage quotient injection. It does not need any unproved claim that an infinite ideal commutes with colimits. Surjectivity uses just one stage representative and a lift modulo I^n.

Step 7 is the equality of the extended ideals and their powers; it follows directly from the A-algebra map and the given principal generator. It makes no claim that I itself is principal at every individual stage.

I tested I=0 (the nilpotent-centre blowups and compatible-point requirement), nilpotent I (blowups may be empty, so no nonempty compatible-point family is asserted), J=I, an invertible principal centre, degree d=0, n=1, a zero generator, and non-Noetherian/non-separated A. When no compatible points exist the conditional local-ring assertion has no instance. For A=0 or I=A the same reasoning is vacuous on the closed fibres. The kernel proof never needs A to embed into its completion, so non-separated rings do not introduce an implicit missing hypothesis. No statement dispute was found.

I checked delivery-errors B-E: no new unsplit nodes with hidden proofs, no duplicate or clause-restatement nodes, no false Mathlib-leaf claim, no unrun query recorded, no uncited non-elementary invocation, and no off-unit route replacement. Every use has a verbatim statement quote in citations.json. All seven steps are under 2000 characters. The specific non-elementary identifications in steps 3-6 are covered by the cited statements. The statement dependency list and historical provenance are preserved as the repair order requests.

## Unfinished work

None at stage 1. The cited admitted unsplit inputs remain independent DAG work; this split does not claim they have been proved in Lean.
