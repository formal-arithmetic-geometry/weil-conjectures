# lem-trf-nonreduced-fibre-open — NW stage-1 delivery

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-nonreduced-fibre-open.json`: statement node, now split into eight steps; Mathlib searches give no exact match. Statement and statement dependencies unchanged.
- `citations.json`: one verbatim statement quotation for each of the 34 step/node citation pairs.
- `report.md`: this report. `searches.jsonl` is the search command's retained log; `write_split.py` is sandbox-only preparation code.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter file is changed.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree for the exact id and for nonreduced/nonReduced/non_reduced and generic/reduced phrases. The only broad concept hit was the relative-component-generalization discussion, not the item. The generic-freeness file was also read: its finite-module-over-a-domain theorem is not freeness of a finite type algebra as a module over the base; its algebra-over-a-base generic-flatness theorem assumes a Noetherian base and only yields flatness. Neither attaches this item. No Lean was written or compiled.

## WANTED

None. All source material needed for this split is present locally.

## What was wrong or incomplete

The item was a statement-only child of the reviewed Stacks 0577 split. It needed the proof of Stacks 0575, not an additional node restating nonreduced spreading. Its statement is correct verbatim against that lemma, including the absence of flatness, Noetherianity and reduced-base hypotheses. There is no statement dispute or correction.

The current blueprint main-20261015 local-term-locality proof is a contracting-correspondence proof. The item's existing ancestry places this commutative-algebra input below its constructibility branch, through the Stacks 0577 and 0550 nodes. I retain that ancestry and the current unit/chapter; I do not replace any unit-level step. Whole-blueprint searches for `nonreduced`, `reduced fibre`, `nilpotent generic`, `generic flatness`, `generic freeness` and `051T` found no equivalent blueprint statement. The existing ordinary versus geometric nonreducedness nodes are different: a purely inseparable field extension over an imperfect field is reduced without being geometrically reduced.

An important citation distinction: `lem-sbc-finite-type-algebra-generic-flatness` only states flatness. It does not supply the nonzero free module needed in the source's tensor argument. Likewise the existing 051S freeness node requires a finitely presented algebra and module, and the 051R node assumes a Noetherian base. I therefore use the existing 051T finite-module-presentation node on the polynomial algebra and then 051S, rather than taking an unstated stronger conclusion from any of those nodes.

## What remains unfinished

Nothing in this one-level split. Existing cited statements remain responsible for their own downstream proofs.

## Not duplicates

No new node is created, so there are no new/existing pairs requiring justification. The entire DAG was searched for the tag 0575 and its source label, and for generic freeness/flatness and flat-quotient tensor injection. Existing 051T, 051S and 00HL nodes are reused. In particular I do not add a general generic-freeness node: its needed specialization here is the explicit application of two existing statements in steps 5–6.

## Review by NW

I read `coord/brief-stage1.md`, stage 1, the three levels in SETUP, GOAL, dag-sync, the chapter and unit records, the current blueprint statement/proof of local-term-locality and the unit, and delivery-errors B–E in full. For the mathematical source I read Stacks `more-morphisms.tex`, label `lemma-nonreduced-in-neighbourhood` (Tag 0575), statement and complete proof, and `algebra.tex` at `lemma-generic-flatness` (051T), `lemma-generic-flatness-finitely-presented` (051S), and `lemma-flat-tor-zero` (00HL). No new-node source is needed because no new node is created. I checked the tag/label mapping in `tags/tags`.

Step 1 uses the actual statement of reduction-universal-homeomorphism: it says the reduction is reduced and has the same topology. Integral-scheme explicitly equates reduced irreducible with integral. I wrote the residue-field quotient calculation, so the claim that fibres agree does not assume it follows merely from a homeomorphism. The locally-finite-type and quasi-compact base-change statements each allow an arbitrary base change; finite-type-morphism supplies their conjunction. No reducedness of the original base is used. A found open descends through the reduction's identical topology.

Step 2 uses integral-function-field-affine-fraction for an arbitrary integral scheme, not just a curve: it explicitly says the generic point lies in the affine open and its stalk is a fraction field. The residue-field definition then identifies this field with kappa(xi), since a field has zero maximal ideal. Finite-type-morphism actually supplies the finite affine cover with finite type coordinate algebras. Open-fibre-product supplies the pulled-back open cover, affine-fibre-product gives its tensor coordinate rings, reduced-scheme-open-cover says reducedness is tested on that cover, and affine-scheme-reduced-iff says a nonreduced affine has a nonzero nilpotent coordinate element. Every hypothesis in these statements holds for these charts. No inverse image of an affine is presumed affine.

Step 3 is elementary and explicitly gives both inverse maps identifying the tensor ring with fractions. The localization-at-prime definition includes exactly this fibre-ring localization at the prime (0). Writing e=b/s, the nilpotence equation gives a nonzero a annihilating b^n; inverting a makes b nilpotent while b stays generically nonzero. This is the full denominator argument, not an unexpanded instruction to clear denominators. The localized finite type generators are written down. It works without bounded nilpotence in the original base.

Step 4 is elementary: the map C->B is multiplication by h, with kernel zero by the definition of Ann(h) and image hB. Both quotient algebras are generated by the images of a finite generating list. If a nonzero base scalar killed 1 in C, it would kill h generically, impossible in the fraction-field fibre. The same argument excludes C_a=0 for every nonzero a, and is why subsequent freeness has nonempty basis.

Step 5 cites precisely the finite-module-presentation statement: R is the domain A, its finite type algebra is the polynomial P, and C and D are cyclic P-modules. It gives finite presentations after a nonzero localization with no hidden Noetherian hypothesis. I checked persistence on a common principal open by the explicit localized-kernel argument and checked P_a=A_a[x] coefficientwise. This is an application to these two modules, not a hidden general comparison theorem. The localization definitions give the stated fraction relations.

Step 6 then meets every 051S hypothesis: A_a remains a domain, P_a has the finite presentation with r generators and no relations, and step 5 supplies finitely presented P_a-modules. Applying the statement successively makes both modules free over a common localized base. Further localization preserves a basis by its unique finite expansion. I explicitly convert a nonzero localized scalar c/a^j back to the original principal open D(ac); there is no silent assumption that the selected scalar lies in the original ring. The exact annihilator sequence persists by the same fraction calculation, and step 4 gives C nonzero. This follows the source's generic-flatness proof using existing nodes; it creates no node for an elementary composition of their assertions.

Step 7 checks the actual flat-quotient-tensor-injective statement: the short exact sequence is over the current A, the quotient D is flat because it is free, and the tensor module is the arbitrary residue field kappa(t), which the statement allows. I wrote why a free module is flat (direct sums of copies of an injection under a basis) rather than citing the definition for the missing theorem. Nonzero C has a basis vector and its coordinate projection, so kappa(t) is a retract of its tensor product. Thus the injected source is nonzero. The displayed formula for the injected map is multiplication by h after tensoring; its nonzero image forces h tensor 1 nonzero. Nilpotence follows from h^n=0. This establishes ordinary nonreducedness, not only a failure of geometric reducedness.

Step 8 uses the affine-fibre-product coordinate description and affine-reducedness equivalence exactly as stated. Open-fibre-product identifies U_t as an open in Z_t. The reduced-scheme definition uses local rings, which are unchanged on an open, so a reduced Z_t would make U_t reduced. All inverted scalars are nonzero, so the final open contains the generic point; step 1 transports it and the fibres back to the original base.

I checked delivery-errors B1–B10, C1–C8, D1–D5 and E1–E7 against these steps. There are no new statements to hide hypotheses or restate the item. Every node used was opened and its statement read; citations.json contains verbatim quotations of those statements. The proof dependencies are exactly the union of uses. The 114-node read-only dependency closure does not return to the item. All eight steps are below 1,000 characters, so none triggers the long-step review threshold. The non-elementary claims are cited; elementary fraction, quotient, basis and tensor formulas are spelled out. Off-unit generic scheme and algebra tools are declared in split_report.tool_uses, with the reason for each; none changes the contracting-correspondence route. No SGA source is used.

Small cases checked: T=Spec k and Z=Spec k[epsilon]/epsilon^2 (C is one-dimensional and h survives); A=k[t], B=A[epsilon]/epsilon^2 (every fibre is nonreduced); A=k[t], B=A[x]/(x^2,tx) (the generic fibre is reduced, so the hypothesis correctly fails); B=0 or empty generic fibre (also reduced, hence excluded); a nonreduced irreducible base k[delta]/delta^2 (its reduction has identical residue fibres); disconnected Z; and infinitely many base nilpotents. No irreducibility or flatness is assumed for Z, and generic freeness is applied only after reducing the base. Infinite rank free modules are permitted in 051S, so polynomial examples are not accidentally forced to be finite over the base.

Mathlib queries were run only through msearch.py and their exact texts and returned digests are retained. I read the candidate reducedness and open-cover statements, the finite-free fibre-polynomial nilpotence test, and the finite-presentation localization-free theorem. Those require finite free algebras, finite presentation over the base, or only concern reducedness/open restriction. They do not state this spreading theorem. The second phrasing searched the nilpotent-section algebraic formulation. Inherited search records in the item were retained rather than rewritten as newly performed searches.
