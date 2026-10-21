# Stage-1 delivery: def-trf-trace-class-source

## Files written

- dag/nodes/sec-trace-formula/def-trf-trace-class-source.json — definition, split; no whole-item Mathlib match.
- citations.json — empty list, since this definition has no proof steps.
- report.md — this report.

No new nodes and no Mathlib leaves. searches.jsonl is the unmodified log produced by msearch.py.

## Attachments

None in the current source. The inherited lean field records a Q65 attachment from 2026-10-16 of AlgebraicGeometry.ProEtale.Correspondence.traceClassSource, mate and uncurry'_mate. Searches of the live lean/WeilConjectures tree for those names, the blueprint tag, and trace-class notions did not find these declarations. The present TraceFormula/Slop/Correspondence.lean has a different condensed-coefficient correspondence and a sorried traceClass definition, not this finite-coefficient source and mate. I preserved the historical field rather than treating it as evidence of a current proof.

## WANTED

None. Both the blueprint and the Stacks source used here are present locally.

## What was wrong and what changed

The imported object formula is valid and unchanged in meaning. Its statement dependencies omitted the theorem that supplies the tensor–internal-Hom adjunction; the operation definition constructs internal Hom but does not itself assert this adjunction. I added the existing lem-sf-ringed-derived-closed-symmetric-monoidal, which states the needed bijection, evaluation counit and coefficient-sheaf unit. I spelled out the mate as the adjunction unit followed by internal Hom applied to u composed with the left unitor. This replaces an implicit choice by its specified construction. The finite coefficient setting is explicitly bound, without strengthening the original admissibility assumption or making any new constructibility assertion for the source.

The current main-20261015 item is textually the same mathematical definition as the older imported item. Its current source path/order is recorded. The unit sk-d-corr introduces ordinary leg c_2 and exceptional leg c_1; these are preserved. This item is not the unit key node, so no unit realization fields are touched.

## Mathlib searches and blueprint reuse

Every query recorded in the node was actually run with the required msearch.py command and its output read. Two conceptual phrasings were used. LeanSearch and LeanFinder found MonoidalClosed.curryHomEquiv', curry' and uncurry'. I read Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean:460–487: these implement exactly the abstract currying operation once its category is closed monoidal. They do not construct the specified derived category, its internal Hom, or the exceptional inverse image. Consequently this concrete definition remains split, with the formal candidate recorded. One Loogle query used an unknown leftUnitor name; its exact diagnostic is retained and it was followed by the valid curry query. It is not counted as evidence of absence. The grep search in Monoidal/Closed located curry', uncurry' and their inverse identity; curryHomEquiv' at line 481 was then read in the same source.

The whole-DAG/blueprint searches by internal Hom, mate and trace-class source returned existing objects rather than any exact duplicate of this definition. The existing derived closed symmetric monoidal theorem is strictly more general than the adjunction used here, so no new node is justified. No same_as entry is warranted: the final trace-class definition and the trace-source-exchange lemma construct different objects or maps.

## Not duplicates

No new nodes; there are no new/existing same-tag pairs.

## Review by NI

I read the item in literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-d-corr/def-trf-trace-class-source.md, the current chapter and unit texts, and their DAG records. For the tensor–Hom ingredient I read Stacks sites-cohomology.tex Section 08J7, Lemma 08J9 (lemma-internal-hom, including its proof and the equation-internal-hom it recovers on H^0), and Lemma 0FPT (lemma-symmetric-monoidal-derived). There are no new nodes needing additional source review.

There are no numbered proof steps: this item defines data, and proof/proof_deps remain empty. I checked each defining clause against the statements of every dependency. def-trf-correspondence supplies the finite A=A_{E,n}, the separated finite-type schemes, the admissible c_1, and u:Lc_2^*K -> Rc_1^!K. def-weil-finite-tor-amplitude defines D^b_ctf and def-weil-finite-torsion-constructibility defines D^b_c and its coefficient/site setting. def-weil-derived-pullback-tensor-hom explicitly supplies finite-level pullback and ambient derived internal Hom, computed with a K-injective resolution of the second argument. These definitions suffice for M, N and H_c(K), but do not themselves prove the adjunction. The added lem-sf-ringed-derived-closed-symmetric-monoidal explicitly supplies the unit O in degree zero and Hom(P tensor^L M,N) = Hom(P,RHom(M,N)), for arbitrary derived objects on a small ringed site. Apply it to the chosen small pro-etale site of C, with O=A_C. The coefficient ring is commutative; no perfectness or extra boundedness hypothesis is needed for this ambient statement. No off-unit proof route is substituted, since this is a definition whose prerequisite identifies the structure used to define its data.

For the mate formula I checked types: lambda_M has source A_C tensor^L M and target M; u lambda_M has target N; eta^M at A_C lands in RHom(M,A_C tensor^L M); the internal-Hom map then lands in RHom(M,N). Uncurrying and precomposing with lambda_M inverse recovers u by the adjunction identity and cancellation of the unitor. This uses precisely the cited theorem, not a claim hidden in a definition. The formula fixes the same mate as the blueprint, and does not replace the source by a supported pushforward class or reverse the legs. The reused theorem has no dependency path back to the item (255 prerequisite nodes inspected), so the new edge is acyclic.

I checked delivery-errors B–E against the file: no new node can duplicate a definition, an elementary step, a clause of the item, or a Mathlib statement; every notation is introduced or supplied by a named definition; no non-elementary theorem is inferred from a mere definition; no claims of constructibility of RHom are added; and no hidden proof, circularity, missing hypothesis or prohibited source route is used. Because there are no proof steps, citations.json is correctly empty and there are no long steps. The unit and chapter routes are preserved.

I tested zero and identity inputs: for K=0 both inputs are zero and there is the unique mate, with no dualizability issue; for C=X and both legs the identity, u is an endomorphism and its mate is the usual name of that endomorphism under the unit–internal-Hom bijection. The zero coefficient map gives the zero section since the derived adjunction is additive. For an empty C the same ambient adjunction remains valid. No statement dispute was found; only the omitted prerequisite and implicit mate construction needed repair.

## Unfinished work

None for this definition split. Its previously existing prerequisites remain the DAG work of their respective items; no assertion that the concrete Lean declaration is proved is made here.
