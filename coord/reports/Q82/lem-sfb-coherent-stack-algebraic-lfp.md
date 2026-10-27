# Q82 stage-1 delivery: lem-sfb-coherent-stack-algebraic-lfp

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-coherent-stack-algebraic-lfp.json: statement, split in three steps; no Mathlib match. Statement and statement dependencies unchanged.
- citations.json: verbatim statement quotes for every citation in all three steps.
- report.md: this report. No new DAG nodes and no Mathlib leaves.

## Attachments

None. The exact blueprint tag and coherent-stack terminology were searched in lean/WeilConjectures; no sorry-free project declaration gives the complete result. The Sheaf Artin criterion is not an attachment.

## WANTED

None.

## Corrections and scope

The imported node had no proof. The live DAG has lem-sfb-space-coherent-stack-general, which explicitly proves both required clauses in greater generality. Reuse it rather than introduce another algebraicity theorem. This is an existing independent node, not a new clause of this item. Its statement allows nonflat ambient spaces and arbitrary scheme bases. The three steps perform the actual scheme specialization and module comparison.

The interrupted earlier attempt completed an eight-input Artin split. Its complete proof, nodes, report and citations are retained in prior-artin-split/; all search logs, actual results and scripts remain in the sandbox. Only the three-step proof is submitted. The initial dry run completed and rejected the phrase “the item's” for lack of standalone context; the submitted proof introduces all its objects directly. The supporting inputs of the earlier attempt are unnecessary given the existing general theorem, so none is delivered as a new node. No previously executed search is invented or rerun. The item's existing and fresh actual Mathlib searches are preserved in full. Hits give scheme morphism properties and module finite-presentation predicates, not the smooth atlas theorem.

## Unfinished work

No stage-1 work remains. No Lean was written and no compiler, Lake or build was run. The existing general theorem is an unsplit DAG input, as permitted for a one-level split; it is not claimed to have a finished Lean proof.

## Review by Q82

I read the statements of every node cited in the three steps, with the Stacks source open. For the main input I read quot.tex Situation 08KB and Theorem 09DS (theorem-coherent-algebraic-general), as well as the flat-case 08WC proof. The existing node additionally states the scheme-base local-finite-presentation clause and identifies 08KD plus the full stack limit criterion as its sources; I checked those statements and the local finite presentation assertion in moduli.tex 0DLZ. Thus step 3 takes both conclusions from the cited statement itself, not an unstated property inferred from its proof. Taking B=S satisfies its scheme-base hypothesis, and no Noetherian or properness-of-all-X hypothesis is added.

For step 1 I checked def-trf-scheme-algebraic-space gives the actual Yoneda representable sheaf and identity atlas. I checked def-sfb-space-morphism-properties defines separatedness by its representable closed diagonal and agrees with scheme properness. The local-properties chart-test node expressly agrees with the scheme finite-presentation locality notion for schemes. With identity charts, the underlying quasi-compactness and quasi-separatedness do not change. The scheme diagonal represents the sheaf diagonal by the definition of the representable sheaf, so no nontrivial representability theorem is hidden here.

For step 2 I read the Zariski/etale quasi-coherent equivalence and its canonical pullback and closed-pushforward comparisons, and the finiteness comparison (descent.tex Tags 03DX, 03LC, 05VG and 06VE). The latter really preserves and reflects both finite type and finite presentation without a Noetherian assumption. For relative flatness I read the pointwise equivalence in lem-trf-relative-flatness-source-cover (morphisms.tex 02JZ): it applies to any flat source chart and arbitrary base, exactly the situation here. The definition of etale explicitly includes flatness. Restriction to identity charts gives the converse. The closed support presentation is the same i_*G condition in the existing general theorem, and the equivalence compares that direct image and finite type G. Thus no support-annihilator theorem is needed. The comparison of tensor pullbacks includes arrows, making this an equivalence of fibred groupoids rather than a bijection on isomorphism classes.

For step 3 the atlas and diagonal transported across this equivalence have the same scheme base changes. The atlas structural map to S remains the same map, so its local finite presentation is exactly the stated conclusion. I checked that the map T to B in the general theorem is unique with B=S over S, not extra object data. This supplies all clauses including a smooth surjective scheme atlas. No new node restates a conclusion of the item.

I checked delivery-errors B--E against the final files, including C1 and C4: each non-elementary comparison is cited and every use is supported by the quoted statement; definitions are used only to unfold the actual notions. No new source or Mathlib claim is asserted. Each step is below 2000 characters and hides no separate representability or approximation argument. I tested empty S and empty X, zero modules, X=S with finite locally free modules of arbitrary rank, nonproper X with proper supported modules, and non-Noetherian and disconnected bases. The zero-support and rank-zero cases survive the equivalence; neither ambient properness nor a fixed rank is imposed. The current latest blueprint direct-images proof (3) and inherited supporting Picard-stack provenance remain intact.

On resumption I ran the existing split through the required dry run first; it exited successfully at 6dc82de359c. I then reread all cited statements and the actual Stacks statements 08KB, 08KD, 08WC, 09DS, 0DLZ, 03DX, 03LC, 05VG and 02JZ, and read the retained item-search results and search log rather than repeat them. I made explicit the scheme nature of a closed subspace of $X_T$: representability of the closed immersion applied to the identity scheme chart gives it immediately, using def-sfb-space-proper-quot-functor. I also cited def-weil-closed-immersion for the affine-quotient description: preimages of affine opens are affine and the diagonal of an immersion is an isomorphism, giving the quasi-compact separated hypothesis used by the direct-image comparison. Finally I spelled out transfer of effective descent data and cited def-sfb-algebraic-moduli-stack. These are definitions and short deductions, not new lemmas. The statement, its hypotheses and provenance remain unchanged. The extra citations have verbatim quotes in citations.json.

## Not duplicates

No new nodes. The stronger existing lem-sfb-space-coherent-stack-general is cited directly.
