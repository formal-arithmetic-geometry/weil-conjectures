# Stage-1 delivery: lem-sfb-finite-p-group-normal-index-p

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-p-group-normal-index-p.json`: item, statement preserved, split into four steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-subgroup-prime-power-order.json`: statement, Mathlib leaf `Sylow.exists_subgroup_card_pow_prime`, `Mathlib/GroupTheory/Sylow.lean:699` (lines 697–703 read).
- `dag/nodes/sec-six-functors-basics/lem-sfb-least-prime-index-normal.json`: statement, Mathlib leaf `Subgroup.normal_of_index_eq_minFac_card`, `Mathlib/GroupTheory/IndexNormal.lean:45` (lines 42–70 read).
- `citations.json`: verbatim statement quotations for every proof-step citation.
- `searches.jsonl`: actual msearch.py output records; searches in both new nodes reproduce their tool/query and digest.
- `report.md`: this report and the author's review.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item id, its blueprint docstring tag, finite p-groups, normal subgroups of index p, the candidate normality declaration, and prime-power subgroup existence. No project declaration states the item. Related uses of the order-index formula in TateModuleDual, StrictLocalRootInvariants, RootPowerMapInvariants, and TorsorMonodromyHom do not prove it. Mathlib declarations are leaves, not project attachments.

## WANTED

None for this split: the two mathematical tools are available in the pinned Mathlib source, and the ambient Stacks source is available locally. The item proof is explicitly agent-written rather than attributed to an unavailable group-theory textbook or to a proof absent from Stacks.

## Corrections and provenance

The mathematical statement needed no correction. The imported node has no proof, and its source describes an independent induction proof in an earlier delivery report. That report is not in this item's sandbox. I replaced that prospective proof with a short argument using two verified Mathlib results; no prior sandbox proof, report or searches existed to overwrite. Original source and blueprint fields were preserved. The new proof_origin explicitly describes the actual argument.

I read Stacks Tag 09F8, `more-algebra.tex`, `lemma-special-case`, especially the paragraph giving the four types of finite field extensions, and Tag 09EE, `lemma-galois-inertia`, including its normal wild p-subgroup assertion. These are the application context, not statements of either new group-theoretic tool. Each new node gives its true Mathlib source and explains the tag's contextual role. No SGA source is used.

I also read the chapter/unit records and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit and direct-image proof. The current paragraph (3) does not contain the historical Epp auxiliary argument; the existing blueprint provenance already says so. `blueprint_refs.py ancestor` returns null for this historical supporting chain. The new nodes inherit that null ancestor and prepend the item to its via list, rather than inventing a blueprint ancestor. `blueprint_refs.py search` found no equivalent imported node for “p-group”, “subgroup of order”, “smallest prime”, or “normal subgroup of index”; “Sylow” found sheaf-filtration nodes with different statements. `same_as` remains []. No chapter or unit record was changed; this item is not the unit key node.

The online Loogle service finds `IsPGroup.isCoatom_iff_index_eq_prime`, but the pinned source does not contain it. It cannot certify a leaf for this item. Generalized Sylow, index cancellation, and the least-prime-index criterion together require an argument, so the item remains split. Both new tools individually are exact/general Mathlib leaves, have no proof steps, and do not merely restate a clause of the item: the first applies to every finite group and every dividing prime power, and the second starts with a specified subgroup of any finite group at its least prime index.

## Not duplicates

The following comparisons cover every live unmerged node carrying 09F8 in its source when I searched the DAG. I opened their statements. For each pair, the shared tag records the application context, not equality of statements.

lem-sfb-finite-subgroup-prime-power-order vs lem-sfb-finite-p-group-normal-index-p: the new tool asserts existence of a subgroup of order p^n for any prime power dividing any finite group order, without normality; the item requires a normal index-p subgroup of a nontrivial p-group; the new tool below has the different hypotheses and conclusion just specified.

lem-sfb-finite-subgroup-prime-power-order vs lem-sfb-epp-compatible-coefficient-dvrs: the new tool asserts existence of a subgroup of order p^n for any prime power dividing any finite group order, without normality; the existing node constructs compatible coefficient DVRs with residue-field and module-finiteness properties.

lem-sfb-finite-subgroup-prime-power-order vs lem-sfb-epp-finite-coefficient-triple: the new tool asserts existence of a subgroup of order p^n for any prime power dividing any finite group order, without normality; the existing node asserts a weak solution of a tower of complete DVRs by a finite field extension.

lem-sfb-finite-subgroup-prime-power-order vs lem-sfb-epp-normal-ramification-filtration: the new tool asserts existence of a subgroup of order p^n for any prime power dividing any finite group order, without normality; the existing node asserts a finite normal extension and a field tower of four ramification types, with base-change stability; it uses the item, so citing it here would be circular.

lem-sfb-finite-subgroup-prime-power-order vs lem-sfb-epp-complete-coefficient-field-arithmetic: the new tool asserts existence of a subgroup of order p^n for any prime power dividing any finite group order, without normality; the existing node concerns residue fields, total ramification and normal closures over a complete DVR.

lem-sfb-finite-subgroup-prime-power-order vs lem-per-complete-dvr-finite-normalization: the new tool asserts existence of a subgroup of order p^n for any prime power dividing any finite group order, without normality; the existing node concerns finiteness, completeness and uniqueness of the integral closure of a complete DVR in a finite extension.

lem-sfb-least-prime-index-normal vs lem-sfb-finite-p-group-normal-index-p: the new tool asserts normality of a specified subgroup whose index is the least prime divisor of an arbitrary finite group order, without constructing a subgroup; the item requires a normal index-p subgroup of a nontrivial p-group; the new tool below has the different hypotheses and conclusion just specified.

lem-sfb-least-prime-index-normal vs lem-sfb-epp-compatible-coefficient-dvrs: the new tool asserts normality of a specified subgroup whose index is the least prime divisor of an arbitrary finite group order, without constructing a subgroup; the existing node constructs compatible coefficient DVRs with residue-field and module-finiteness properties.

lem-sfb-least-prime-index-normal vs lem-sfb-epp-finite-coefficient-triple: the new tool asserts normality of a specified subgroup whose index is the least prime divisor of an arbitrary finite group order, without constructing a subgroup; the existing node asserts a weak solution of a tower of complete DVRs by a finite field extension.

lem-sfb-least-prime-index-normal vs lem-sfb-epp-normal-ramification-filtration: the new tool asserts normality of a specified subgroup whose index is the least prime divisor of an arbitrary finite group order, without constructing a subgroup; the existing node asserts a finite normal extension and a field tower of four ramification types, with base-change stability; it uses the item, so citing it here would be circular.

lem-sfb-least-prime-index-normal vs lem-sfb-epp-complete-coefficient-field-arithmetic: the new tool asserts normality of a specified subgroup whose index is the least prime divisor of an arbitrary finite group order, without constructing a subgroup; the existing node concerns residue fields, total ramification and normal closures over a complete DVR.

lem-sfb-least-prime-index-normal vs lem-per-complete-dvr-finite-normalization: the new tool asserts normality of a specified subgroup whose index is the least prime divisor of an arbitrary finite group order, without constructing a subgroup; the existing node concerns finiteness, completeness and uniqueness of the integral closure of a complete DVR in a finite extension.

I also compared the conceptually closest nodes without the same tag. `lem-sfb-sylow-subgroup-cardinality` computes the size of a subgroup already assumed maximal among p-subgroups; it does not supply subgroups of arbitrary dividing prime-power order. `lem-weil-pbc-sylow-subgroup-prime-index` supplies only a Sylow subgroup, whose index is prime to p, so for a p-group it supplies the whole group, not a subgroup of order p^(a-1). `lem-per-finite-prime-power-central-series` supplies a central series and does not state either general tool. `lem-sfb-surjective-subgroup-image-index` does state the needed order-index identity, so I reuse it rather than creating a Lagrange node.

## Unfinished work

No unresolved mathematical issue. This is stage 1 only: no Lean source was written and no compiler, Lake or build tool was run. The two new leaves have empty proofs as required. No nodes or imports were removed; the item had no proof dependencies before this split. Delivery and dry-run outcomes are reported by the required delivery command.

## Review by Q100

I checked the statements and proof with delivery-errors B–E open. For the item I read 09F8's filtration paragraph and 09EE's inertia statement, and distinguished their role from a proof of the auxiliary abstract group theorem. For the first new node I read the exact source signature at Sylow.lean:699–700: its assumptions are precisely finite G, prime p and p^n dividing Nat.card G, and its conclusion is a subgroup of that cardinality. For the second I read IndexNormal.lean:45–70: equality of subgroup index with minFac of the group cardinality gives Normal. For |G|>1, minFac is the least prime divisor; Normal's conjugation inclusion is equivalent to equality by applying it also to g inverse. These are actual matches in the pinned checkout, unlike the newer online maximal-subgroup characterization.

Step 1 cites `lem-sfb-finite-subgroup-prime-power-order`. Its statement expressly gives a subgroup of the requested cardinality under divisibility. I checked b=a-1 is nonnegative, P is finite, p is prime, and p^b divides |P| with witness p. There is no need to assume P abelian or supply an elementwise p-group equivalence.

Step 2 cites `lem-sfb-surjective-subgroup-image-index`. I opened its statement, not its proof: it explicitly concludes |J|[H:J]=|H| for a surjection onto the finite group named H there. Instantiate both its groups with P and its homomorphism with the identity, which is surjective. Its image of our H is H itself. Thus the cited formula is exactly |H|[P:H]=|P|. I also read its pinned source `Subgroup.card_mul_index`, Index.lean:290–292. Cancellation is valid because p>=2 implies p^b>0, including b=0. The cited lemma is already a Mathlib leaf in the same unit; no route exception is needed.

Step 3 is elementary integer arithmetic and cites no node. I checked the exponent is positive; p divides p^(b+1), and repeated prime-divides-product gives that every prime divisor q of p^(b+1) divides p and hence is p. This also shows |P|>1 and justifies the precise hypothesis of the next tool. It makes no group-theoretic assertion or hidden normality claim.

Step 4 cites `lem-sfb-least-prime-index-normal`. Its statement says exactly that a specified subgroup at the least prime index is invariant under all conjugations. We have the same H constructed in step 1, its index from step 2, and the least-prime and nontriviality hypotheses from step 3. The conclusion contains both clauses of the item for that one H, without invoking a new node that restates the item.

I checked edge cases explicitly: a=1 gives b=0 and the trivial subgroup, with index p and automatic normality; p=2 gives the usual index-two situation; for C_p x C_p the construction gives a subgroup of order p; for a nonabelian order-eight group it gives a subgroup of order four and the normality criterion still applies. For the general existence leaf n=0 gives the trivial subgroup even when G is trivial, and n equal to the full p-exponent gives a Sylow subgroup. The normality leaf requires |G|>1, so the undefined “least prime divisor of 1” case is excluded; in S_3 its index-two subgroups are normal, whereas index-three subgroups are outside its hypotheses. No commutativity or cyclicity has entered the proof.

Every non-elementary input is a cited node; citations.json quotes verbatim text from each actual statement. The new statements introduce their objects and define subgroup, cardinality and index in words. The statement-only nodes contain no argument. I searched all DAG/blueprint nodes and project Lean declarations before creating them and compared every same-tag pair above. All Mathlib records correspond to actual msearch.py calls in searches.jsonl; two initial file-target grep calls produced malformed displayed paths, so I repeated those patterns against the GroupTheory directory and recorded the correct path-and-line hits instead. No fabricated searches or service-unavailable-as-no-match records were added. The longest non-elementary step is well below 2000 characters, and the entire assembly proof is under 3000 characters. No outstanding correction or disputed statement remains.
