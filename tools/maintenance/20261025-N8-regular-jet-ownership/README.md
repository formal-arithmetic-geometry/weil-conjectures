# N8 regular-jet ownership maintenance

Repeated stage-2 repair attempts compile, then fail because stage2_delivery.py
excludes the explicitly requested downstream FormalHilbertStratumMinors node
at its prerequisite-closure check. Although that scope finding is advisory,
the early continue drops the owner and makes the later no-owner finding fatal.
The H2 return of 73da211d444b explicitly requested this extraction.

Concurrent Q02 maintenance 607ca9bd142 already moved jetExponents, multiFactorial
and finiteMinorIdeal to FormalTaylorJetMatrices. Preserve that owner and reuse
its public definitions. Extract only regularIteratedPartial, regularJetMatrix
and regularJetMinorIdeal into RegularJetMatrix and its definition node. Their
signatures, bodies and docstrings are verbatim. FormalHilbertStratumMinors publicly imports that module;
all its remaining declarations, proofs and docstrings are unchanged. Its node
records the new statement dependency and stops claiming the three moved names.
The dispatched item's node gains the definition edge so the owner is reachable
immediately; its theorem module and Lean record remain for normal worker review.

The new definition and repaired consumer compile one at a time using
SHEAF_GROUP=M-N8-maint tools/lean_file.sh, with the existing 60-second limit.
The interface change is registered through the unchanged landing API. Adjacent
.maint-N8-1792869320.bak files preserve preimages (absent markers for new files).

Next worker: preserve the item theorem, use the current base versions of
RegularJetMatrix and FormalHilbertStratumMinors and their nodes in the sandbox,
and rerun deliver2.py N8 lem-trf-regular-taylor-minor-equality-germ --no-push.
The shared extraction then contributes no packet delta. The proof-only import
of RegularTaylorMinorEqualityGerm into FormalHilbertStratumMinors belongs to the
normal post-landing import update; do not reintroduce it in this packet.
Do not add the downstream theorem as an item prerequisite: that recreates a cycle.

No dispatcher, admission, review-service, preflight or landing tool was changed.
The protected stage2_delivery.py needs a separate tool-owner repair: retain
supplied existing owners after an advisory scope finding rather than skipping
their classification, while retaining module ownership and DAG cycle checks.
