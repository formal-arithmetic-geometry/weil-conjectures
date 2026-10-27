# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-norm-algcl-evaluated-bar-augmentation.json: item, split; original statement retained verbatim, five assembly steps, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-evaluated-positive-bar-row-transfer.json: statement-only node, unsplit; no Mathlib match. Finite-index restriction/transfer on vertical-cohomology rows, for arbitrary condensed rational coefficients.
- dag/nodes/sec-six-functors-basics/lem-sfb-evaluated-positive-bar-row-local-effacement.json: statement-only node, unsplit; no Mathlib match. A positive-resolution-degree row cocycle becomes a boundary on an open subgroup, for the finite-rank all-continuous norm-algebraic-closure coefficient sheaf.
- citations.json: every proof-step citation, quoted verbatim from its statement.

## Attachments

None. Searches in lean/WeilConjectures for the blueprint tag, evaluated-bar augmentation, norm algebraic closure, positive bar rows and local effacement found no declaration stating this item or either new node. The existing continuous topological cohomology declarations do not identify that complex with ordinary internal condensed derived invariants.

## WANTED

WANTED: an exact reference proving open-subgroup local effacement of positive vertical-cohomology bar rows for all-continuous, incomplete norm-topological algebraic p-adic coefficients, for lem-sfb-evaluated-positive-bar-row-local-effacement.

WANTED: an exact internal-condensed reference for finite coset restriction/transfer and its homotopy on evaluated vertical-cohomology bar rows, for lem-sfb-evaluated-positive-bar-row-transfer. This is a formal extension of the finite coset construction, not a claim that the existing continuous-cochain transfer node already proves it.

## Corrections and scope

The item was unsplit, with no sandbox predecessor or released repair note of its own. Its original statement and all imported metadata are retained. The blueprint's paragraph (3) gives the direct-image motivation, but states neither this particular evaluated augmentation nor the new analytic input. The proof is therefore explicitly agent-written. Stacks homology.tex, lemma-ss-double-complex (0130) and lemma-first-quadrant-ss (0132), provide the formal spectral-sequence part, not the analytic local-effacement claim. No SGA source was used.

The nearby split lem-sfb-norm-algcl-bar-augmentation is not evidence for the item: its proof uses global positive Cech exactness for Omega, whereas the current statement of lem-sfb-norm-algcl-profinite-cech-exact explicitly supplies a counterexample. Nor can lem-sfb-normed-scalar-profinite-hom-acyclic be specialized: its coefficient field is finite and complete. I read both statements and avoided both in the proof. The upstream comparison lem-sfb-profinite-algcl-derived-invariants-comparison depends on this item, so invoking it would be circular; it is not cited.

## Not duplicates

lem-sfb-evaluated-positive-bar-row-transfer vs lem-sfb-continuous-cochain-finite-index-transfer: the existing node acts on explicit continuous cochains valued in a topological vector space; the new node acts on cohomology of section-evaluated injective-resolution columns. Those groups are not asserted to be continuous-function spaces, so the existing transfer statement does not specialize.

lem-sfb-evaluated-positive-bar-row-transfer vs lem-sfb-condensed-split-coset-induction: the existing node gives exact induction left adjoint to restriction, not the transfer map or its index homotopy on the vertical-cohomology bar rows.

lem-sfb-evaluated-positive-bar-row-local-effacement vs lem-sfb-local-norm-algcl-cocycle-descent: the existing node descends an actual continuous Omega-valued group cocycle modulo coboundaries to a finite subfield on an open subgroup; the new cocycles lie in positive sheaf-resolution cohomology of profinite group powers. It asserts no descent or finite-field representative for an ordinary continuous group cocycle.

lem-sfb-evaluated-positive-bar-row-local-effacement vs lem-sfb-norm-algcl-profinite-cech-exact: the existing node concerns one covering Cech complex and contains both a counterexample to global exactness and a split-base-change primitive; the new node concerns horizontal cohomology classes in positive vertical resolution rows of the group nerve, and restriction to open subgroups. A split base change of a cover is not an open subgroup restriction.

lem-sfb-evaluated-positive-bar-row-local-effacement vs lem-sfb-norm-algcl-evaluated-bar-augmentation: local vanishing of a positive-row cocycle after subgroup restriction is an intermediate analytic claim; it does not assert any total comparison, comparison-map normalization, naturality, or resolution independence. Its use still needs the separate transfer argument and a convergent spectral sequence.

The whole-DAG concept searches and blueprint_refs searches (derived invariants, bar, coinduced, effacement, finite index, positive bar, resolution cohomology) found no blueprint duplicate. The two new nodes share only the blueprint motivation document, not a Stacks theorem tag purported to state them. No identical-tag existing node is being duplicated.

## Review by Q69

I read the chapter and unit records, the current main-20261015 direct-images proof paragraph (3), and the item's statement. The route remains the norm-coefficient analytic comparison used below the direct-image claim. I also read the old scalar bar argument and the corrected Cech counterexample node, to check that completeness was not silently restored. Neither new node is attributed as a theorem of the blueprint. For the transfer node I read the existing continuous finite-index transfer statement and the split-coset induction statement; their interfaces do not cover vertical resolution cohomology, which is why the new formal obligation is needed. For the effacement node I read the local norm cocycle descent and parameter completion-boundary descent statements: they concern actual continuous functions, not positive derived section groups, and are not sufficient substitutes. The report retains the precise missing reference instead of suggesting that these statements follow from them.

Step 1 uses the statement of lem-sfb-condensed-derived-invariant-bar to choose the simultaneous nonnegative bar model. I read lem-sfb-profinite-free-hom-resolution-evaluation: it gives exactly H_P(I)(S)=I(S times P), its resolution augmentation, and naturality in both parameter maps and coefficient maps. It does not claim acyclicity. I read lem-zl-contractible-derived-sections-tensor: its extremally disconnected profinite-set case gives exact evaluation for any ring sheaf, so applies to the one-point set and this B, without any completeness hypothesis. Left exactness of sections identifies the degree-zero vertical kernel with N(G^p); finite products and finite sums commute with additive evaluation, so the evaluated total is the indicated finite-diagonal total.

Step 2 cites both new statements. Effacement gives an open H and a boundary for the restricted horizontal cocycle in the fixed q>0 vertical row. Transfer supplies cor res equal to [G:H] on that same row cohomology; it is not borrowed from ordinary continuous group cohomology. Compactness makes the index finite, openness makes it positive, and Q-linearity permits division by that integer. This proves E2 vanishing, without identifying or killing each individual positive column group. The group H need not be normal; neither new statement assumes normality. Each row uses the restriction of the same equivariant resolution, exactly as both statements specify.

Step 3 uses the statement of thm-sp-double-complex-spectral-sequences for the E1/E2 formulas, functoriality and finite-filtration convergence, and lem-weil-pbc-first-quadrant-row-collapse for the edge isomorphism. I read both statements and the Stacks source for 0130 and 0132. The double complex is first quadrant because both bar degree and injective-resolution degree are nonnegative. Each total diagonal has n+1 terms; no unbounded convergence or infinite-totalization interchange is hidden. The edge is the actual bottom-kernel augmentation: its representative in column p is the inclusion ker(dv^{p,0}) into D^{p,0}. Thus the isomorphism is induced by the very augmentation in the item. Localization at quasi-isomorphisms uses def-weil-abstract-derived-category, whose statement was also read.

Step 4 uses the normalized isomorphism and its module-map naturality from lem-sfb-condensed-derived-invariant-bar, and the resolution comparison/lift/homotopy claims actually stated by lem-sfb-condensed-bar-total-naturality. I read the latter's complete statement: it gives the signed total homotopy (-1)^p h, identity/composition compatibility and resolution independence. The extra commutative square with underived functions is direct postcomposition: a lift f with f a=a' sends the generator's image a(v) to a'(v); it remains the same equality in every bar degree. This establishes independence for this actual augmentation and naturality for continuous E-linear equivariant maps of any finite ranks.

Step 5 uses the degree-zero invariant-inclusion normalization explicitly stated by the bar node. Its kernel formula follows immediately from d(v)(g)=rho(g)v-v. Small cases checked: d=0 gives zero throughout; G=1 gives the alternating constant complex, with d=0 in even degrees and d=identity in odd positive degrees, so only H0 survives; in the effacement node p=0 requires a zero restriction, with y forced zero, while q=0 is deliberately excluded. The transfer node permits q=0 and H=G and does not assert positive-degree vanishing. Empty parameter sets give zero sections. The incomplete topology on Omega and all continuous maps remain present everywhere.

For B–E, the new files have statements only and explicit objects, hypotheses, notion dependencies and blueprint origins. Their search records reproduce actual msearch results; each was queried with LeanFinder twice, Loogle, LeanSearch and grep, and the closest results were read. The Rep Shapiro theorem is for abstract representations, GroupTheory.Transfer is a group homomorphism construction, and continuousCohomology.zeroIso proves only degree zero. None is a match for a new node. Proof-step citations were read as statements and copied into citations.json. The two hard inputs are distinct arguments and neither simply restates the total augmentation theorem. No elementary rearrangement was made a node. Every proof step is under 2000 characters; the assembly is under 3000 characters. Statement/proof dependency cycles are left to the required server check as well as the explicit ancestor audit above.

## Unfinished work

This stage-1 split leaves the two new statement-only obligations for later workers, especially the analytic local-effacement input with the exact WANTED reference above. No Lean was written, compiled, or built. No file in the shared repository or launcher was modified.
