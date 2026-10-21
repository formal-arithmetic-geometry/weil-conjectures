

## lem-weil-finite-compact-projection-formula (2026-10-15 23:51 UTC, branch head 77721ecfa9)

L: approved by the reader, but the landing refused it: NOT MERGED lem-weil-finite-compact-projection-formula: coord/.merge.lock held for 120 s by pid 3467334: /usr/bin/python3 tools/merge_delivery.py Q37 cor-pur-smooth-admissibility --stage 1 --reviewer NT-Codex-Q37-94d928c3b --head 94d928c3b817abe3f65d75f31f81ab670bb83b77 --spot-checked Read the item, all cited statements, sources and unit/chapter route; checked all eight steps, edge cases, duplicates and dependency cycles. Mathematics accepted. Corrected only proof_origin.by from document to agent, as required for blueprint-based proofs. Whole corrected JSON and detailed review.md written; all 1 Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-weil-constant-coefficient-objects-constructible (2026-10-16 02:30 UTC, branch head a2a684eee5)

L: independent stage-2 immutable head a2a684eee5d4: stage-2 checks: (b) the item's stmt_deps gained lem-weil-integral-scalar-extension-constructible, which are neither new nodes of the delivery nor nodes landed on the base with a lean record (only those may be added, or a statement correction with statement_change)

## lem-sf-finite-cd-derived-upper-bound (2026-10-16 05:28 UTC, branch head d35074b9b1)

L: approved by the reader, but the landing refused it: NOT MERGED lem-sf-finite-cd-derived-upper-bound: lem-sf-finite-cd-derived-upper-bound: no longer stage-1-open; live completion takes priority Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-pur-support-exact (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 1 (2182 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 1 (2182 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## lem-weil-verdier-preservation-strata (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 3 (2083 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 3 (2083 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.

## lem-per-smooth-pullback-support-dimension (2026-10-17 20:30 UTC, branch head 84c88221dc)

L: independent stage-2 immutable head 84c88221dc47: H3: the Lean conclusion provides only an unrelated Nonempty isomorphism, without tying it to the normalized truncation comparisons, so it does not state the node’s canonical cohomology identification. Review written in review.md; both files compile via scompile.py.

## sk-def-localizing-closure (2026-10-18 02:36 UTC, branch head 13075641de)

L: independent stage-2 immutable head 13075641def3: H3/H7 (§1(C)): the item renders Λ=Q̄_ℓ as Profinite.continuousMapRingObj (PadicAlgCl ℓ) = C(−,Q̄_ℓ), following a stage-1 node fault. The source's condensed Q̄_ℓ is sk-def-sfb-qlbar-condensed (padicAlgClRingObj, finite-subextension-valued, explicitly not C(−,Q̄_ℓ)). The sibling det-def-localizing-closure-ctf-equals-bc and at least 12 of the 66 citers use that ring, and all landed project Lean uses padicAlgClRingObj; with the delivered hΛ these citers cannot instantiate at Q̄_ℓ. Required: correct the item statement under §1(C) (Q̄_ℓ = condensed ring of [sk-def-sfb-qlbar-condensed]; add it to stmt_deps; statement_change with all 66 citers; ## Statement corrected), replace the sixth set entry in both declarations with Mon.mk (Profinite.padicAlgClRingObj ℓ) (variant checked: compiles clean, 2.5 s), update the docstrings and lean.note, and supply an independent second reading (the current one is an author self-check). All else verified: every other clause, edge cases (empty scheme, zero ring, empty coproduct, E=Q_ℓ), recorded ConstantModelConstructibleFiniteTor and condensedRingObj, ambient DerivedCategory of Mod, IsTriangulated + IsClosedUnderIsomorphisms + coproduct closure over Type w with universes {w,u}, nonvacuity probe, no hollow def, no sorry, docstrings, no duplicate notion; delivered file compiles clean with nt_compile (2.9 s).

## lem-per-algebraic-valuation-coarsening-correspondence (2026-10-19 01:47 UTC, branch head 71c3c35abfc)

L: approved by the reader, but the landing refused it: NOT MERGED lem-per-algebraic-valuation-coarsening-correspondence: lem-per-algebraic-valuation-coarsening-correspondence: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-fix-operation-reduction (2026-10-21 04:02 UTC, branch head 54f9574793)

L: approved by the reader, but the landing refused it: NOT MERGED lem-fix-operation-reduction: cited node def-weil-integral-scalar-extension: statement changed since the reviewed delivery; rebase and revalidate the citation Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-sfb-adic-perfect-model-complete-reduction (2026-10-21 04:06 UTC, branch head 83b51364a1)

L: independent stage-2 immutable head 83b51364a1e0: H2 (mechanical finding upheld): stmt_dep lem-weil-pbc-constant-completion-equivalence supplies only plain defs of Sheaf.Paper.ConstantCompletionEquivalence (finite, completed, projection, coefficientMap, Mod/Cx/D/Q, change, extend/extendComparison via derivedExtension = Classical.choice of a module-local helper, tensorSection, IsComplete); none is .choose of the theorem's conclusion (equivalence/flat_and_quotients). Correction: state a definition node, existing:true on Sheaf.Paper.ConstantCompletionEquivalence, listing finite, completed, projection, coefficientMap, Mod, Cx, D, Q, change, DerivedExtension, derivedExtension, extend, extendComparison, tensorSection; cite it and def-sfb-quotient-kernel-completeness (IsComplete/kernelIdeal) in the item's stmt_deps in place of the theorem, keep the theorem in proof_deps, Lean statement unchanged. Otherwise faithful: every clause matches (IB-completeness via projection kernel, canonical residue iso normalized by tensor formula plus universal extendComparison, finite-dim constant cohomology, [a,b] vanishing, all slices); no extra hypotheses; edge cases fine; nt_compile --json clean 5.7 s.

## lem-pur-scalar-hom-comparison-tower (2026-10-21 04:11 UTC, branch head e85e0a80dc)

L: independent stage-2 immutable head e85e0a80dc1b: stmt_deps cite theorem node lem-coef-derived-system-evaluation-calculus only for the plain def WeilConjectures.coefficientBaseChangeHom (CoefDerivedSystemEvaluationCalculus.lean:195; not a .choose, the theorem's conclusion is unused). Required: add a definition node owning a module with that def (e.g. existing:true def node listing coefficientBaseChangeHom), cite it in place of the theorem, keep the theorem in proof_deps only if needed; the Lean statement itself is correct and should stay unchanged. Checked: htower/hid identical to scalarHomTensorCoherence; μ normalized ScalarHomTensorComparison; α/u canonical leftAdjointUniq; c = transpose of μ⁻¹ then T(ev), H⊗P convention allowed by node's symmetry clause; naturality/tower/identity variance and endpoints match node Steps 3,6,7; no extra hypotheses; edge cases P=0, identity legs, Z→F2 fine; docstrings/sorry/verbatim OK. nt_compile unavailable (live library unavailable, twice); delivery records clean 9.5 s compile.
