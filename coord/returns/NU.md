

## def-exc-proetale-sections-with-support (2026-10-16 01:04 UTC, branch head 4b7f0bed47)

L: independent stage-2 immutable head 4b7f0bed47ad: Existing source declarations define sheaves valued in one fixed coefficient category, while the node depends on modules over the varying finite-coefficient pro-etale ring sheaf; supply a canonical transport/interface and restate the functor on that category.

## lem-weil-pbc-frobenius-vector-bundle-kernel (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 7 (2620 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 7 (2620 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## prop-asd-smooth-base-change (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 1 (4395 characters); step 2 (4109 characters); step 4 (3769 characters); step 5 (2034 characters); step 7 (2683 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 1 (4395 characters); step 2 (4109 characters); step 4 (3769 characters); step 5 (2034 characters); step 7 (2683 characters) are not elementary and hide lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.

## thm-pur-regular-immersion-purity (2026-10-19 06:04 UTC, branch head 964596d17a)

L: independent stage-2 immutable head 964596d17a6f: H2/H13: item and all 4 new def nodes (class-data, exterior-class, signed-evaluation, cancellation) cite theorem lem-pur-supported-cup-functoriality only for plain defs (FunctorialCupH, functorialCupPullback, functorialCupTwist, functorialCupTwistPullback; .choose only of local existsUnique helpers) and for 34 item-specific regular* adapters appended to the landed SupportedCupFunctoriality module (1206->1711 lines, 48.4 s at load 100) and recorded under that theorem node, which is not a base stmt_dep. Correction: restore that module and record to live, drop the theorem from stmt_deps, cite def-pur-supported-class-operations for the functorialCup* defs, move the regular* adapters with the same bodies into a module of one of this delivery's def nodes (or a new def node) and cite it. Substance otherwise accepted: the statement matches the node clause by clause (concentration, rank one, supported H^0, frame-normalized class as the choice of a stated unique existence, adjoint transpose IsIso, counit-unique cancellation with correct inverse direction, etale and exterior-product clauses); edge cases c=0, empty and disconnected schemes, all levels covered; nt_compile --json clean on all 6 files (8.9-48.4 s).
