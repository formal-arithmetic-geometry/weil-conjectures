## Worker report

Group NS, item lem-sf-native-adic-lisse-kernel-strata, 2026-10-22. Stage 1 only; no Lean file was written and no compiler, Lake, or build command was run. All writes are in this item's sandbox.

Files delivered:

- dag/nodes/sec-six-functors/lem-sf-native-adic-lisse-kernel-strata.json: full unchanged statement, now split into six steps.
- dag/nodes/sec-six-functors/lem-sf-native-adic-generic-lisse-kernel.json: new statement-only supporting lemma. A morphism of native lisse sheaves on a nonempty quasi-compact scheme has lisse kernel and cokernel after restriction to some nonempty open. Mathlib verdict: no match after five logged searches, two semantic phrasings, Loogle and source grep. Zero new Mathlib leaves.
- citations.json: every step/node citation has a verbatim quotation of the cited statement, with both exactness and composition quotations for the inverse-image node.

Attachments: no attachment delivery is requested. The previous attempted attachment of the item is explicitly superseded by this split, as instructed. The source declaration AlgebraicGeometry.ProEtale.exists_nonempty_isAdicLisseSheaf_kernel_cokernel belongs to the new supporting node (Abelian.lean:232-327); its statement matches the new node, and its body contains no sorry. This is recorded as a Lean candidate, not a claim of an independently certified transitive axiom audit. No source declaration is used as an uncited proof step.

WANTED: none. The relevant native source, Bhatt-Scholze paper and Stacks sources are present.

The original item had a correct, self-contained statement but no proof. Its Mathlib searches and Lean candidates were retained without alteration. The sandbox had no item, report, split, or search log when this worker began, so there was no completed split to dry-run or prior search result to reuse. There is no statement dispute or change. Nothing remains unfinished in the one-level split; the new lemma intentionally has no proof and remains a queue item.

## Sources and searches

I read AGENTS.md, GOAL.md, the stage-1 brief and stage document, the worker role, SETUP's chapter/unit/node rules, the item's chapter and unit records, and delivery-errors B through E (both copies in the merged file). The item is a native coefficient support calculation under the seeded localization/constructible-abelian chain; blueprint_refs.py ancestor returns None. I retained the seeded ancestor convention rather than inventing an imported blueprint ancestor, and prepended this item to the new node's via chain.

For the item I read lean/WeilConjectures/SixFunctors/ProEtale/Adic/Abelian.lean:333-436, especially the closed-support induction and the final choice of the top closed subset. For the new lemma I read lines 228-327 and the earlier helpers: openness of rank superlevel sets (55-67), the constant-rank normal form argument (94-134), and rank descent through two trivializing covers (177-210). These supply exactly a nonempty open, without assuming irreducibility, reducedness, normality, constant global rank, or Noetherian local rings. The finite-subcover argument bounds rank on a quasi-compact base; the maximum-rank open is nonempty and has constant rank. The new node states this supporting result only; its proof is not embedded in its statement.

I also read Bhatt-Scholze Section 6.8, Definitions 6.8.1 and 6.8.3, Proposition 6.8.4, Corollary 6.8.5, and Lemma 6.8.7. Corollary 6.8.5 asserts a stronger global-lisse conclusion for that paper's coefficient construction. No identification of that coefficient sheaf with the present locally finite-function sheaf has been assumed. The proof_origin is therefore agent, following the native source argument, rather than falsely attributing a native comparison to the paper. No SGA source is used.

DAG searches used both ids/declaration names and concepts: generic lisseness, constant rank, locally finite continuous coefficients, lisse kernels, and generic opens. Blueprint searches included 'generic lisseness', 'constant rank', 'kernel and cokernel', 'lisse kernel', 'kernel', 'nonempty open', and 'locally finite continuous'. No existing blueprint or DAG node states the new generic-open assertion in these coefficients. The Mathlib results are preserved as the unmodified msearch stdout in the new node and search-generic-1.txt through search-generic-5.txt. The hits concern ordinary structure-sheaf modules, ideal-sheaf kernels, or generators/relations of arbitrary sheaf modules. Neither those results nor their one-line specializations imply the generic local-system assertion here.

For the geometric steps I read Stacks schemes.tex, Tag 01J3, label lemma-reduced-closed-subscheme; topology.tex, Tag 04ZA, label lemma-Noetherian-quasi-compact, together with the Noetherian definition; and topology.tex, Tag 005L, label lemma-constructible-Noetherian-space. Those facts are already stated in existing nodes and are reused. No new node cites a Stacks tag already carried by an existing node.

## Not duplicates

lem-sf-native-adic-generic-lisse-kernel vs lem-sf-native-adic-lisse-kernel-strata: the new lemma requires only a nonempty quasi-compact scheme and produces one nonempty open. It makes no finite stratification assertion. The item proves the finite partition by induction on closed supports, including the boundary where successive generic opens must be removed.

lem-sf-native-adic-generic-lisse-kernel vs lem-weil-pbc-lisse-generic-kernel: the existing lemma concerns a locally constant abelian etale source and a generic-stalk zero criterion, not native continuous-coefficient module kernels and cokernels on an open.

lem-sf-native-adic-generic-lisse-kernel vs lem-zl-weil-generic-lissity: that node concerns a constructible Weil sheaf on finite-type finite-field schemes in the finite-extension adic convention. It does not give the generic kernel/cokernel assertion for the specified native sheaf on arbitrary quasi-compact schemes.

lem-sf-native-adic-generic-lisse-kernel vs lem-sf-native-adic-pullback-exact-lisse: exactness and preservation of lisse objects under pullback do not say that the kernel or cokernel of a lisse morphism is lisse on an open.

## Review by NS

I checked each step against the statements of its cited nodes, not their internal proofs.

Step 1 uses lem-sf-native-adic-pullback-exact-lisse for exactness, lisse preservation and the inverse-image composition comparison. Its statement explicitly contains all three. Applying exactness to the two displayed sequences identifies the actual pullbacks of the original kernel and cokernel; this avoids assuming that a restriction of a kernel is a kernel without justification.

Step 2 states the induction predicate for closed subsets of the original X, so the induction hypothesis already produces subschemes of X. The empty family is the base. Minimal-counterexample induction follows directly from the assumed descending-chain condition; it introduces no assumption of algebraic Noetherianity or finite dimension.

Step 3 uses lem-weil-pbc-closed-subset-closed-subscheme for exactly the existence of a closed immersion with prescribed image. Its statement says that for any scheme and any closed subset. The closed-immersion definition gives the homeomorphism onto Z. The compact-subsets node assumes precisely descending chains of closed subsets stabilize, rather than Noetherian coordinate rings, and gives a finite subcover for Z. Thus its application really makes T quasi-compact. Native exact-pullback gives lisse i^*M and i^*N. The nonemptiness and quasi-compactness hypotheses of the new generic-open node are both checked before applying it.

Step 4 applies the new node to the pulled-back morphism. It concludes lisseness for kernel and cokernel of j^*i^*u, exactly as the new statement says. The inverse-image node then identifies these with (i composed with j)^*K and (i composed with j)^*C. The source has the same order of pullback and the same native coefficient map.

Step 5 proves the geometric facts rather than making a node for them. I wrote the ambient open O with S=Z intersect O and the proper closed remainder Z_0. The immersion factorization is in the closed-immersion node's definition: U is closed in O, then O is open in X. Its closedness and sheaf surjection are restrictions of i's own defining data. This avoids confusing open-then-closed with the definition's required closed-then-open order. The locally closed and open-immersion definitions justify the topology, and the constructible-subset node explicitly says that finite unions of locally closed subsets are constructible in a Noetherian topological space (005L). Thus no constructibility theorem is taken merely from a definition that omits it.

Step 6 invokes the induction hypothesis only on the proper closed remainder. The images are disjoint and cover Z, and adjoining one stratum preserves finiteness. Old strata were already subschemes of X, so no unproved composition-of-immersions lemma is hidden. The constructible-subset node again supplies constructibility for their locally closed images. Taking the top closed subset gives one common partition, which is stronger than the requested pair of possibly different partitions, with no change in statement.

I tested X empty (empty partition), Z empty, a one-point nonreduced scheme, the zero morphism, ranks zero on covering members, an isomorphism, and a rank jump between a generic open and its closed complement. The generic lemma does not claim the chosen open is dense, which is unnecessary: it need only remove a nonempty relative open from each closed support. Variable ranks on covering members do not invalidate the quasi-compact finite-subcover bound in its source. The full Noetherian induction is still necessary to control the remainder; the new node does not restate either finite-partition clause.

Against delivery-errors B, the new node is self-contained, statement-only, uses definition nodes for its notions, preserves exact search queries/results, and has a specific source and blueprint place. Against C, every non-elementary input is a cited statement with a verbatim quote in citations.json; all dependencies have been opened, and none has a dependency on the item. Against D, the induction and construction remain in the item; the new result is a strictly smaller generic-open input. Against E, hypotheses and coefficient categories were checked at each application, and the original kernel/cokernel restriction comparison is written explicitly. All six steps are shorter than 2000 characters, so no long-step lemma is hidden. No unit or chapter file was changed.
