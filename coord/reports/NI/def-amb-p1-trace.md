# Stage-1 report: def-amb-p1-trace

## Files written

- `dag/nodes/sec-smooth-purity/def-amb-p1-trace.json` — existing definition item, now split; no new nodes.
- `citations.json` — empty because the definition has no proof steps.

## Attachments

No sorry-free declaration in the project source states this definition exactly. Searches for `(blueprint: def-amb-p1-trace)`, the item id, and the trace notation found no attachment.

## WANTED:

None.

## Review by NI

I read the blueprint source `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/def-amb-p1-trace.md` and the imported item. The statement agrees clause by clause: for (q:\mathbf P^1_S\to S), (t_q) is projection onto the (A_S) summand in (Rq_*A(1)[2]\cong A_S(1)[2]\oplus A_S), it sends the Kummer class (h) to (1), and ε_K is the composite of the proper projection-formula isomorphism with (1\otimes t_q). The statement dependencies are exactly the existing nodes `lem-amb-proper-coproducts-projection`, `def-coefficient-twists-detailed`, and `thm-amb-p1-decomposition`; I opened the latter two relevant theorem/definition records and confirmed they supply the decomposition, twists, and projection formula named by the definition. Since this is a definition, there are no proof steps or cited-node quotes, so `citations.json` is empty. I checked the source tree for a project declaration or blueprint-tagged declaration and found none. The required LeanFinder, Loogle, grep, and LeanSearch searches were run; the first and third had no relevant match, while Loogle and LeanSearch were unavailable as recorded in the node.

## Not duplicates

No new nodes were created, so no duplicate pairs apply.

## What was wrong or corrected

The imported node had `status: imported`, an empty `blueprint.from`, and no Mathlib search record. I filled the blueprint location, recorded `same_as: []`, ran and recorded all required searches, and marked the already complete definition split. No mathematical clause was changed.

## What could not be finished

Nothing remains for this stage-1 split.


## Second reading by NI

- Item, coefficient and base clauses: checked the blueprint definition at order 1571, the preceding decomposition at order 1570, and the ordinary ambient projection formula at order 1563; found unbound $A$, missing Noetherian/invertibility hypotheses and an incompatible pro-etale twist citation. Repaired explicitly below.
- Item, trace clause: opened the existing `lem-asd-ordinary-finite-p1-adjunction` statement, which supplies exactly $b_q$ with components the shifted/twisted unit and $h$ under the repaired hypotheses; projection of its inverse gives the identical trace. No use of the lemma's proof or exceptional adjunction is made.
- Item, twist and Kummer clauses: opened `lem-asd-finite-etale-twist-line` and `lem-amb-kummer-any-base`; they supply the ordinary finite-level roots-of-unity line and exact Kummer sequence for precisely $N$ invertible and $NA=0$. Read Stacks `etale-cohomology.tex`, Tag 03PL, label `lemma-kummer-sequence`, and Tag 03RQ, label `lemma-cohomology-smooth-projective-curve`; these confirm the prime-to-characteristic condition and the degree-one normalization on a geometric projective-line fibre. Replaced the pro-etale inverse-limit twist citation, rather than silently identifying the two sites.
- Item, epsilon clause: opened `lem-amb-proper-coproducts-projection` and read Stacks Tag 0F0G, label `lemma-projection-formula-proper-mod-n`; substitute $r=q$ and $L=A_P(1)[2]$. The hypothesis is finite torsion coefficients and all ordinary unbounded complexes, exactly as now written. Its map goes from tensor to direct image, so epsilon uses its inverse. The final tensor unit arrow is now explicit.
- Item, notion dependencies: opened `def-nagata-projective-space-base-change`, `def-weil-pbc-derived-categories`, `def-weil-pbc-direct-image`, `prop-weil-pbc-inverse-image-modules-exact` and `def-kun-derived-tensor`; these state the projective line over an arbitrary base, constant-coefficient unbounded etale categories, the direct image, exact constant-ring inverse image and the required tensor, respectively. All agree with the repaired objects.
- Proof steps: none; this is a definition. The sole normalization identity is the two-line calculation $b_q^{-1}h=iota_2$, $operatorname{pr}_2iota_2=1$, written in the statement. It needs no new theorem or citation record; `citations.json` remains empty.
- New nodes: none. B1--B7, per-new-node duplicate and leaf checks have no instances. Searched all blueprint chapters with `blueprint_refs.py search 'projective-line trace'` and searched the DAG for trace/Kummer/twist statements; reused the existing typed decomposition and finite twist nodes. Their dependency closure does not reach this item, so the replacement introduces no cycle.
- Edge cases: $S$ empty and $K=0$ give unique zero maps; $A=0$ and $N=1$ give the zero module category and the same formulas. Over an algebraically closed field of characteristic prime to $N$, the degree-one Chern class is the second basis vector, hence trace sends it to 1. There is no relative-dimension-zero case: the projection here is always the projective line, of relative dimension one. No boundedness or flatness of $K$ is imposed.
- Searches: ran independent LeanFinder and Mathlib grep queries with different vocabulary through `msearch.py`; read all returned signatures, which concern cotangent/group cohomology and projective modules, not this trace. Kept the first reader's unavailable searches as unavailable. Read both upstream source trees for the item id and trace spellings; no matching declaration was found, and no upstream sorry declaration is used as a completed proof.

Changes: made the ambient finite-level etale hypotheses explicit, replaced the incompatible twist dependency by the existing finite etale line, reused the exactly typed existing decomposition clause, named the class $h$ and the tensor-unit arrow, and recorded the additional actual searches. The first worker's sections above are retained; their original no-correction verdict is superseded by this second reading.

### STATEMENT-DISPUTED: missing ambient hypotheses and site mismatch

The imported definition leaves $A$, $S$, and the category of $K$ unspecified. Its cited twist node defines pro-etale objects, whereas its cited projection formula is on ordinary small etale derived categories and its decomposition requires a Noetherian base. Without invertibility, take $S=\operatorname{Spec}\overline{\mathbf F}_p$, $N=p$ and $A=\mathbf F_p$. On every etale test scheme the sheaf $\mu_p$ is trivial, so $A_P(1)=0$ and $Rq_*A_P(1)[2]=0$; the claimed summand $A_S$ is nonzero. Thus the displayed decomposition cannot mean arbitrary coefficients and arbitrary schemes. The correction states the intended ordinary finite-torsion setting, $NA=0$, $N$ invertible, $S$ Noetherian, and all $K\in D(S_{\mathrm{et}},A)$, preserving the projection and epsilon construction. It neither asserts an adic extension nor restricts $K$ to bounded/constructible objects. The source's finite-coefficient purity conventions and its preceding ordinary projection/decomposition are the intent being made explicit.

The eight existing citers were read at their statements: `thm-pur-affine-line-purity`, `lem-amb-affine-space-top-trace`, `cor-pur-affine-space-zero-section-purity`, `cor-pur-vector-bundle-purity`, `thm-amb-p1-adjunction`, `lem-amb-p1-diagonal-integrals`, `def-pur-affine-line-purity-comparison`, and `lem-asd-ordinary-finite-p1-adjunction` (the last contains a textual comparison, not a dependency on this item). Their intended finite-level uses retain the same normalized map. The old ambiguous pro-etale notation in some citers needs its own ordinary/etale-origin comparison and is not proved by this definition; no citer is modified or declared to acquire a new pro-etale theorem here.

Further corrections after dry run: restored `blueprint.from: null`, required for this imported node (the first worker had incorrectly filled a self-ancestry). The original blueprint paragraph remains named by `split_report.blueprint`. Also read the full direct-image statement: it defines the module sheaf functor and its bounded-below derived functor only. The statement now explicitly defines the unbounded interpretation $Rq_*L=Q(q_*I)$, citing the opened statements `prop-weil-pbc-kinjective-resolutions-exist` (all module complexes admit K-injective resolutions) and `lem-weil-pbc-kinjective-total-derived` (such resolutions compute the total derived functor). Applying the additive sheaf functor degreewise respects shifts, cones and chain homotopies, so its homotopy-category functor is exact, as required by the latter. No new node was needed.
