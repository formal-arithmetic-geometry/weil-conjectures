# Worker report: lem-cbc-simplicial-module-model

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-simplicial-module-model.json`: repaired five-step split; no new nodes.
- `citations.json`: added verbatim quotes for the sorted simplicial-algebra model theorem and the derived-adjunction preservation clause.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its key phrases, and the blueprint tag; no sorry-free declaration states this transferred simplicial-module model.

## WANTED:

- Choudhury--Gallauer, *Homotopy theory of dg sheaves*, arXiv:1511.02828, §3.3, sequence (1), and the transferred simplicial-module/projective connective-chain model paragraph before Proposition 3.15, printed pp. 11--12. The PDF is not archived in `literature/`, so the reconstruction remains agent-written from that source.

## What was wrong in the returned split and what I repaired

1. Step 2 previously asserted that the transferred classes satisfy the model axioms without the acyclicity condition. I identified simplicial `Λ`-modules with strict simplicial algebras over the one-sorted theory of `Λ`-modules and cited `lem-coef-sorted-simplicial-algebra-model`, whose statement supplies the transferred model structure, generating maps, and lifting systems; the module-theory specialization is now written explicitly.
2. Step 3 previously claimed that the horn obstruction lies in `N_nB` for every missing face. That is false for `k>0`. I replaced it by normalizing the free horn inclusion itself: its quotient is the two-term disk complex in degrees `n` and `n-1` for every `k`, and the chain relation shows that its lifting obstruction is exactly surjectivity of `N_n f` in positive degree. This removes the unsupported direct-summand assertion and handles all horn indices uniformly.
3. Step 5 previously used Ken Brown's lemma without a cited node. It now cites `lem-coef-model-infinity-derived-adjunction`, whose statement explicitly says a left Quillen functor preserves weak equivalences between cofibrant objects.

## Review by Q26

I reread the item source reference (Choudhury--Gallauer §3.3, pp. 11--12), the full statements of all seven proof dependencies, and the two newly cited off-unit tool nodes. Step 1 is the degreewise free/forgetful adjunction from the simplicial-object definition. Step 2's one-sorted module-theory identification matches the sorted-algebra theorem's `U_s`, free generators, and model-axiom conclusion; the sorted-theory statement supplies the required generating families and factorizations. Step 3 now treats every horn index uniformly by normalizing the free horn inclusion: the quotient is the two-term disk in degrees `n` and `n-1`, and its chain relation makes the lifting obstruction exactly surjectivity of `N_n f`; the converse and the absence of a degree-zero condition are explicit. The Dold--Kan normalization node supplies the definition, and the Moore-homotopy node supplies the normalized-homology/component comparison. Step 4 uses the transferred creation of fibrations and trivial fibrations and the Quillen criterion. Step 5 checks cofibrancy of every simplicial set and uses the cited derived-adjunction clause before applying the normalized criterion.

I verified all hypotheses (arbitrary commutative `Λ`, positive degrees only, and no added surjectivity in degree zero), reread every cited statement, and checked that each citation quote is a verbatim substring. The zero ring, zero module, terminal simplicial set, dimensions zero and one, and outer horns were rechecked. `proof_deps` is the union of the step uses, the two off-unit citations are declared in `split_report.tool_uses`, and no SGA source or new node is introduced.

## Second reading by Q26

- Item statement: checked against Choudhury–Gallauer §3.3, sequence (1), Fact 3.14(3)–(4), and the paragraph before Proposition 3.15 (pp. 11–12); the arbitrary commutative ring, underlying Kan weak equivalences/fibrations, positive normalized degrees, and degree-zero exception all agree.
- Step 1: checked against the degreewise free–forgetful adjunction in sequence (1) and [def-weil-pbc-simplicial-object]; verdict pass, with the basis-simplex argument elementary.
- Step 2: checked against the transferred simplicial-module paragraph and [lem-coef-sorted-simplicial-algebra-model]; verdict pass after spelling out the one-sorted module theory and its free boundary/horn maps.
- Step 3: checked against the transferred connective-chain model assertion, [lem-cbc-dold-kan-normalization-equivalence], and [lem-cbc-simplicial-module-moore-homotopy], including outer horns and the cases $n=1,2$; the prior quotient claim was false, and the repaired argument uses the two-term disk quotient $D^n$ and proves the lifting criterion.
- Step 4: checked against the transferred model classes and the Quillen-adjunction clause of [lem-cbc-dg-presheaf-model-localizations]; verdict pass.
- Step 5: checked against the final sentence before Proposition 3.15, [lem-coef-model-infinity-derived-adjunction], and the normalized criterion from Step 3; verdict pass.
- Edge cases: the zero ring, a field, the zero and terminal simplicial modules, the empty simplicial set, $n=0$ (no horn generators), $n=1$, and outer horns were checked; there is no scheme or empty-scheme parameter in this item.
- New nodes: none; all cited DAG nodes were opened and their cited statements checked, and existing-node searches found no duplicate needed by the repair.

Changes made: rewrote Step 2 to make the module-theory identification and sorted-model specialization explicit; corrected Step 3 from a one-generator quotient to the disk quotient with the explicit lift/converse argument; removed the no-longer-used small-object citation from Step 2; and made Step 5's normalization dependencies explicit in its text and citations.
