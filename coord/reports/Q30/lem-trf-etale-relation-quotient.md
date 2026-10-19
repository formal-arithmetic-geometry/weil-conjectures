# Stage-1 report: lem-trf-etale-relation-quotient

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-relation-quotient.json` — repaired six-step quotient proof; Mathlib verdict: no match.
- `dag/nodes/sec-trace-formula/lem-trf-etale-relation-restriction-quotient.json` — repaired statement-only restriction lemma, now separating arbitrary étale restriction from the surjective quotient-isomorphism clause; Mathlib verdict: no match.
- `dag/nodes/sec-trace-formula/lem-trf-etale-relation-kernel-pair.json` — new statement-only kernel-pair lemma from Groupoids Tag 045Y; Mathlib verdict: no match.
- `dag/nodes/sec-trace-formula/lem-trf-etale-affine-quotient-representable.json` — retained statement-only affine representability lemma; Mathlib verdict: no match.
- `dag/nodes/sec-trace-formula/lem-trf-etale-relation-finding-opens.json` — retained statement-only open-subspace lemma; Mathlib verdict: no match.
- `dag/nodes/sec-trace-formula/lem-trf-algebraic-space-coproduct.json` — retained statement-only coproduct lemma; Mathlib verdict: no match.
- `dag/nodes/sec-trace-formula/lem-trf-algebraic-space-open-gluing.json` — retained statement-only gluing lemma; Mathlib verdict: no match.
- `citations.json` — verbatim statement fragments for every cited node in every proof step.

## Attachments

No Lean declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states this item or the repaired support statements without `sorry`. No attachment was found.

## WANTED

None. The required Stacks sources are present locally in `literature/stacks-project/`.

## What was wrong and what I corrected

The maintainer returned the earlier split for four specific reasons. First, the old restriction node required surjectivity and was then incorrectly applied to a non-surjective affine summand inclusion. I changed that node to assume only that the refinement map is étale, retaining injectivity of the quotient map and making the quotient map an isomorphism only under surjectivity. Step 2 now uses only the relation-preservation conclusion for each summand and never identifies an individual summand quotient with the total quotient.

Second, the affine and final atlas calculations used the kernel-pair identity without a cited statement. I added `lem-trf-etale-relation-kernel-pair`, whose statement is exactly the canonical isomorphism `h_R ≅ h_U ×_{U/R} h_U` for a monomorphic pre-equivalence relation. Its source is Groupoids Tag 045Y, with the quotient-sheaf definition immediately preceding that lemma.

Third, the fppf-local atlas calculation invoked descent of étaleness without a node. Step 3 and the final step now cite `lem-galois-fpqc-descend-etale`, which states that étaleness descends along an fpqc covering, and explicitly check surjectivity after the same jointly surjective cover. Fourth, the old final step was marked elementary although Tag 02WV gives a substantive argument. It is now a non-elementary step: after algebraicity and representable diagonal are known, it chooses local representatives, identifies the pullback with a base change of `t` using the kernel-pair node, descends étaleness, checks surjectivity, and then invokes the quotient-sheaf coequalizer for the universal mapping property.

## Review by Q30

I reread the returned maintainer review, the full Stacks passages for Tags 02WW, 02WV, 02WT, 02WU, 02WQ, and 02WR, and Groupoids Tags 045Y and 045Z. I also reread every statement cited by the repaired item, including the new kernel-pair statement, the existing affine representability statement, the open-subspace statement, the coproduct and gluing statements, the algebraic-space definition, the étale definition, and the fpqc étale-descent statement.

Step 1 uses the repaired restriction statement only for a surjective étale refinement, so it obtains both the restricted étale relation and the quotient isomorphism. Step 2 uses the scheme-coproduct statement for the affine open coproduct and uses the restriction statement only for the relation on each non-surjective summand; the statement explicitly gives relation étaleness for arbitrary étale maps and does not claim quotient equality there. This is the correction to the returned E1/C4 issue.

Step 3 uses the affine quotient statement for representability of the atlas pullbacks and the diagonal. The new kernel-pair statement supplies exactly the missing identification with `T_j ×_{a_j,U_i,t} R_i`; reflexivity of the equivalence relation gives a section of `t`, hence surjectivity. The cited fpqc-descent node supplies the non-elementary descent of étaleness, while surjectivity is checked after the jointly surjective fppf cover. Together with the algebraic-space definition, these are precisely the hypotheses needed for each `F_i` and its atlas. This repairs both C1 findings in the returned review.

Step 4 uses the finding-opens statement with its actual hypotheses: the equivalence-relation projections are surjective by reflexivity, and étale maps are flat and locally of finite presentation. The affine summand maps are étale, and the quotient is locally represented in one summand after refining an fppf cover. Step 5 checks the coproduct size condition using the scheme coproduct of the affine atlases, then checks all five hypotheses of the open-gluing statement: algebraic summands, representable open immersions, joint surjectivity, and algebraic coproduct.

Step 6 is now substantive rather than elementary. I checked that representable diagonal gives the scheme pullback over every test scheme, that local quotient representatives exist by the sheafification construction, that the kernel-pair statement turns the local pullback into a base change of `t`, and that the fpqc descent node applies to the fppf cover. The same kernel-pair statement gives the global presentation identity, and the quotient-sheaf universal property gives the bijection of maps to every fppf sheaf. No definition is used as a substitute for the presentation theorem.

I checked the new statement on the identity relation, on a two-component disjoint union with a non-surjective summand inclusion, and on an empty/singleton affine cover. The two-component example confirms why the repaired restriction lemma must state injectivity for arbitrary étale maps and reserve isomorphism for surjective maps. I reran the Mathlib searches required for the new kernel-pair node (LeanSearch, LeanFinder, Loogle, and Mathlib grep); only generic kernel-pair or setoid declarations appeared, so it remains an unsplit non-Mathlib node. The existing searches for the retained nodes were preserved. I checked all citation quotes against the current node statements and removed the stale presentation-node claim from the earlier report. No statement is weakened, no cycle is introduced, and no prohibited SGA source is used.

## Not duplicates

- `lem-trf-etale-relation-kernel-pair` vs `lem-weil-pbc-sheafification-sets-exact`: the new statement identifies the relation sheaf with the quotient kernel pair; the existing Mathlib leaf states only finite-limit preservation by set-valued sheafification.
- `lem-trf-etale-relation-kernel-pair` vs `lem-weil-pbc-fpqc-representable-descent`: the new statement concerns effectiveness of a monomorphic equivalence relation in a quotient sheaf; the existing node concerns gluing morphisms into a fixed scheme along an fpqc cover.
- `lem-trf-etale-relation-restriction-quotient` vs `lem-trf-etale-relation-kernel-pair`: the restriction statement controls pullback relations and injectivity/isomorphism of quotient maps; the kernel-pair statement identifies the relation with the quotient's fibre product.
- `lem-trf-etale-affine-quotient-representable` vs `lem-trf-etale-relation-kernel-pair`: the affine statement proves representability of quotient pullbacks and diagonals; it does not assert the kernel-pair identity.
- `lem-trf-algebraic-space-open-gluing` vs `lem-coef-infinity-relative-initial-boundary`: both metadata records mention Tag 02WR, but the former is the algebraic-space open-gluing criterion for fppf sheaves and the latter is an infinity-categorical relative-initial-boundary assertion; neither is a special case of the other.
- `lem-trf-etale-affine-quotient-representable` vs `lem-weil-pbc-fpqc-representable-descent`: both metadata records mention Tag 023Q, but the former proves representability of quotient fibre products and diagonals for affine étale relations, while the latter glues morphisms into a fixed scheme along an fpqc cover.
- `lem-trf-etale-affine-quotient-representable` vs `lem-trf-polarized-scheme-etale-descent`: both use Tag 023Q as a source cross-reference, but the former is the affine algebraic-space quotient input and the latter is effective descent of polarized schemes, which uses quotient representability downstream.
- `lem-trf-etale-affine-quotient-representable` vs `lem-coef-infinity-cartesian-initial-boundary-lift`: the former concerns scheme quotient representability and the latter concerns cartesian boundary lifts in an infinity-categorical setting; the shared 02WU metadata is a tag collision.
- `lem-trf-etale-relation-finding-opens` vs `lem-weil-pbc-fpqc-representable-descent`: the former identifies restrictions of quotient sheaves as representable open immersions, whereas the latter is fpqc descent for maps to a fixed scheme.
- `lem-trf-etale-relation-finding-opens` vs `lem-trf-polarized-scheme-etale-descent`: the former is the Stacks open-subspace theorem for an equivalence-relation quotient; the latter descends a polarized scheme and line bundle and does not state the open-subspace criterion.
- `lem-trf-etale-relation-finding-opens` vs `lem-coef-infinity-cartesian-initial-boundary-lift`: these are unrelated scheme-quotient and infinity-categorical boundary statements sharing the 02WU tag in source metadata.
