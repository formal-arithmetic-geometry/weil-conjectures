# Q60 maintenance, 2026-10-17: current instructions

This replaces the earlier maintenance note that called all seven inherited steps
supported. The return at 1cd6cafd35 is still mathematically valid: the end of step 6
does not follow from the statement of space-transport-classification. A mechanical
preflight pass does not establish that inference. Keep the checked quotient,
adjunction, counit, cylinder and horn calculations, and repair the comparison.

Maintenance reopened the circular splits of
`lem-coef-infinity-hom-bifunctor-functoriality` and
`lem-coef-space-geometric-descent` in BOTH server DAGs. Their complete statements
and Lean interfaces are retained. Their old proofs and reviews are archived under
`coord/maintenance/Q60-straightening-1792207711/`; they are independent proof tasks,
not accepted prerequisites with circular proofs. Refresh the shared snapshot/base
before checking the candidate. Earlier 34/75/78-node cycle reports are historical;
report a fresh concrete return path if a later split reintroduces one.

For the missing comparison, a technical comparison of concrete constructions is
permitted. HTT Remark 3.2.5.10 and Lemma 3.2.5.17(1) compare the cone-defined
straightening of X-op along C[N(C)-op] -> C-op with the opposite of the explicit
quotient diagram F_X(C), for EVERY simplicial X over N(C), by a natural map that is
an objectwise weak homotopy equivalence. This is a possible statement-only
technical input after the normal duplicate/source/Mathlib searches. Specify its
map and both constructions precisely, using the existing unmarked cone
straightening/presentation nodes; check that their full prerequisite closures do
not return to this item. It compares two concrete constructions and is not the
forbidden new node saying merely "R_C D is classified by N_hc(D)". If you use it,
write out how the normalized derived straightening and enriched evaluation give
the desired coherent functor, with an actual cited statement for every comparison.
Do not infer that normalization from fibers or strict edge transport alone.

The source extract for Lemma 3.2.5.17 is already in the sandbox. Reuse the checked
calculations and real search logs. Do not restore the dependency-erasing helper
or claim that ordinary-base subset formulas construct general straightening on
an arbitrary quasicategory. Do not borrow the parent's classification clause or
the Cat-infinity analogue: their proofs depend on this item. The full item
statement stays intact. The next worker must repair the mathematics and obtain
a fresh dry-run OK before READY; maintenance has not delivered or certified it.
