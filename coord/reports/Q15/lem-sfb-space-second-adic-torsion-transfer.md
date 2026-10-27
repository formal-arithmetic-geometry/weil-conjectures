## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-second-adic-torsion-transfer.json`: statement, split into six steps using existing nodes; Mathlib verdict: no match. The statement and statement dependencies are retained.
- No new nodes and no new Mathlib leaves.
- `citations.json`: twelve step/node entries, each checked as a verbatim substring of the cited statement.
- `searches.jsonl` and `search-results-0.txt` through `search-results-4.txt`: the five actual Mathlib searches and their full returned results. The item's inherited searches are retained as prior evidence.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, second-adic terminology and torsion-transfer names. The tag has no declaration. `AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_torsion` in `GrothendieckDevissageSecondAdicSystemTorsion.lean:72` is a scheme theorem, using scheme ideal-sheaf data and completion of all coherent modules; it does not state this algebraic-space proper-support theorem. Its kernel and cokernel helpers have the same scheme restriction. They are not attachments for this item.

## Wanted literature

None. The source arguments needed here are present in `literature/stacks-project/`.

## Problems found and changes made

The item was unsplit with an empty proof. Its statement is correct; no STATEMENT-DISPUTED correction is needed. The two estimates in Stacks 08BC have “details omitted,” so merely quoting that passage would not split this item. The new proof supplies the quotient estimate using the existing ring-module scalar-lifting theorem. It supplies the reflection argument directly by faithfulness of the given completion equivalence on a fixed closed thickening.

In particular, the proof never assumes the completion on an arbitrary affine chart is faithful, never identifies categorical adic kernels with ordinary component kernels, and never assumes tensor quotient is left exact. For the fixed thickening, the completed inclusions of the ideal-product kernel and cokernel into proper-support coherent modules are zero; faithfulness forces those inclusions to be zero. This actually gives exponent 2t; the statement's exponent 4t follows by containment of ideal powers and is unchanged.

The supplied equivalences are on proper-support categories, so proper support of every auxiliary source and target is essential. Step 3 proves it, including proper support of N_e from N_1 using the finite nilpotent filtration. It does not infer proper support of N_e from an arbitrary inverse limit.

Read the three blueprint levels in SETUP.md, the chapter and unit records, and the latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`. This is an inherited supporting existence argument for paragraph (3)'s compactification/direct-image prerequisites. The item's chapter and unit remain fixed. The historical unit record's chapter differs from the current latest path; it is not changed here. The ancestor command returns None, as for the previously accepted supporting nodes: the inherited null ancestor and full via chain are retained, with a more precise place. Whole-blueprint searches for “second adic,” “torsion kernel,” “kernel cokernel annihilated,” “0888,” “faithful completion” and related phrases found no equivalent imported node. The existing scheme torsion nodes and general scalar node were opened and compared rather than duplicated.

## Unfinished work

None in stage 1. No Lean was written, and no compiler, Lake command or local DAG/preflight checker was run. The required server checks and delivery are run through the provided tools.

## Not duplicates

No new nodes. The existing scheme second-adic torsion theorem is not applicable to arbitrary algebraic spaces; the generic ring-module scalar theorem is reused on etale charts instead. The closed-adic dictionary and the algebraic-space coherence/support nodes are reused directly.

## Review by Q15

I read Stacks `spaces-more-morphisms.tex`, Tag 08BC (`lemma-existence-tricky`), including the two omitted torsion-bound arguments, and Tag 08BA (`remark-inverse-systems-kernel-cokernel-annihilated-by`). I also read the full commutative-algebra argument in `coherent.tex`, Tag 0888 (same remark label, lines 6887–6936), and the project ring-module theorem's statement and proof. My proof follows the first estimate in that argument; for reflection it uses the supplied global equivalence by an explicit vanishing-of-inclusions argument. Accordingly `proof_origin.by` is agent, not a claim that the source writes out this argument. There are no new-node sources to review.

For step 1 I opened `lem-sfb-space-qcoh-affine-chart-calculus` and `lem-weil-pbc-kernel-cokernel-annihilated-mod-ideal`. The first states that restriction and sections on every affine etale chart compute kernels, cokernels, images and tensor products. The second's clause (c) states exactly the exponent-2t quotient estimate for every quotient ideal. Apply it to the R-module map a_n(U), with annihilating ideal K(U) and quotient ideal K(U)^e. All its assumptions (commutative ring, t positive, both errors annihilated) are present; it needs neither completeness nor flatness. The existing node is Lean-closed. This is a generic off-unit tool use, declared in `split_report.tool_uses`, not a replacement for any unit route.

For step 2 I checked the direction of the supplied square: v sigma = theta u, so sigma identifies kernels and theta identifies cokernels. Both are O-linear, hence commute with every local ideal section. This is a short consequence of the given isomorphisms, not an additional comparison theorem. No declaration concerning schemes is used for this transfer.

For step 3 I read every cited statement: `def-sfb-space-coherent-adic-system` supplies K^e N_e = 0 and the adjacent quotient isomorphisms; `lem-sfb-space-qcoh-affine-chart-calculus` supplies the ordinary quasi-coherent kernel, cokernel, tensor and image calculus; `lem-sfb-space-noetherian-coherent-support` supplies coherent submodule/quotient closure and closed supports; `lem-sfb-space-noetherian-coherent-acc` supplies coherence iff quasi-coherence of finite type; `lem-sfb-space-proper-support-closed-operations` supplies closed-subset preservation and equivalence between proper closed structures with the same support; and `lem-sfb-space-module-proper-carrier-support` supplies the equivalence with an actual proper closed carrier. Thus all terms and the two ideal products lie in the proper-support category. I explicitly checked the positive indices: reducing each adjacent quotient identity modulo K identifies N_e/K N_e with N_1, even for e=1; if that stalk is zero, iterating F=KF exactly e times gives F=0 because K^eF=0. This needs no unstated Nakayama lemma.

For step 4 the cited adic definition defines ideal products by local sums and completion on maps by the induced quotient maps. A kernel section of u maps to a kernel section of u modulo J^n, so its K^(2t) multiples land in J^nF. That directly proves that every component of the completion of B -> F is zero. I did not infer that B/J^nB embeds in F/J^nF.

For step 5 the cited chart calculus computes cokernels. On a chart the cokernel of the reduced map is G/(u(F)+J^nG), which is Q/J^nQ by the quotient definition. Thus K^(2t)Q lies in J^nQ, and the cited adic definition gives zero completion of D -> Q. This is an explicit quotient computation, not an assertion of left exactness or of exactness of completion.

For step 6 I read `lem-sfb-space-closed-adic-dictionary` in full. It states the coherent equivalence for modules killed by the closed ideal, natural compatibility with all quotient projections and completion, and preservation/reflection of proper support. Apply it to the ideal K^e, not K. The given equivalence on X_e^K therefore makes completion faithful on precisely the coherent proper-support modules killed by K^e on X. All four objects B,F,D,Q satisfy those conditions by step 3. Zero completion of the two inclusions makes both inclusions zero by faithfulness; their sources are zero because the maps are inclusions. The final passage 2t -> 4t is the elementary containment K^(4t) subset K^(2t). No exactness property of the equivalence is used.

I checked delivery-errors B–E individually. There are no new statement-only nodes to disguise clauses of the item, no unsupported literature facts, no cycle-inducing new citation to a dependent theorem, and no illicit source route. Every cited result is used only for its stated conclusion. All six steps are below 2000 characters (the longest is 1107), and none contains an unexposed standard comparison lemma. The elementary steps consist only of linear isomorphism conjugation or the displayed two-line quotient/inclusion calculations. The non-elementary coherence, carrier, chart and closed-immersion comparisons all cite existing nodes.

Small cases checked directly: empty X and zero modules; t=e=n=1; K=0 (all target annihilations hold tautologically), K=O_X (the K-adic system and H/K^eH are zero); J=0 (completion is the constant diagram and faithfulness is immediate); nilpotent J (quotients eventually stabilize); and J=O_X, where the completion target is zero and the assumed equivalence forces every proper-support coherent object on each thickening to be zero. As a check that faithfulness is necessary, on Spec k[x] with J=(x), K=0 and F=k[x]/(x-1), all completions of F vanish but F is nonzero; the completion-equivalence hypothesis on the thickening fails, so this does not contradict the item. This tests exactly the step where a false affine faithfulness shortcut could otherwise enter.

The Mathlib searches were run through msearch.py and their outputs were read. Both semantic phrasings returned individual module completion maps and their exactness or injectivity, not this assertion about coherent algebraic-space diagrams. Loogle's seven hits concern individual module evaluations and projections; the grep had no hits. LeanSearch returned forgetful sheaf functors and dense-subsite results, not coherent adic completion. No returned theorem specializes in one line to the item. Every added search entry records the exact executed tool and query and preserves the actual returned text.
