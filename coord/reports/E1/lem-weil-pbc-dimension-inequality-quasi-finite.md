# lem-weil-pbc-dimension-inequality-quasi-finite

## Worker result

- Changed only `dag/nodes/sec-proper-base-change/lem-weil-pbc-dimension-inequality-quasi-finite.json`; no new nodes.
- No Lean attachment: searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` for the node id, quasi-finite local dimension, and the relevant dimension/QuasiFinite declarations. `Scheme.Hom.topologicalKrullDim_eq_of_surjective` and `Scheme.Hom.coheight_apply_of_flat` require extra hypotheses and do not state the item.
- No wanted source. Stacks Algebra 00QF, 00Q9, 00OJ and 00GT were read in `literature/stacks-project/algebra.tex` from the F2 checkout. The statement is unchanged.
- The split uses existing nodes for pointwise Zariski Main Theorem, integral incomparability, localization at a prime, and local dimension as prime-chain height. It follows the general-case argument of 00QF; the Noetherian shortcut is unnecessary.
- No source or blueprint error found. The blueprint index search for "dimension inequality quasi finite" found no duplicate imported node.
- Nothing left unfinished in this item. `review_split.py` passes with zero new nodes. `check_dag.py` reports 7 pre-existing unreachable nodes and 11 pre-existing route errors for other items; it reports no error for this item.

## Review by E1

I read Stacks Algebra 00QF (lemma-dimension-inequality-quasi-finite), its general-case proof, 00Q9 (theorem-main-theorem), and 00OJ/00GT for integral prime chains. The item's finite-type, prime-over-prime and pointwise quasi-finite hypotheses are exactly 00QF's. There is no new node; whole-DAG, blueprint and read-only Lean searches found no exact replacement. The fresh-base reconstruction changes only the item's proof fields and report, preserving the current origin audit and blueprint metadata.

Step 1 applies the cited pointwise Zariski Main node to the integral closure T of R in S, obtaining an isomorphism T_g -> S_g away from q. The cited localization-prime-isomorphism node then identifies S_q with T_q'; the contraction of q' is p. Step 2 applies the cited integral-incomparability statement to every strict chain of primes below q', so contractions form a strict chain below p. Step 3 uses the cited localization-dimension-chain statement for both local rings and compares those chain lengths, including an infinite supremum. The source's proof localizes R at p first, but the cited 00Q9 theorem over R gives the same local comparison directly; no Noetherian shortcut is assumed. The zero-dimensional local base case permits only chains of length zero and is covered. I found no A-E defect requiring worker repair.
