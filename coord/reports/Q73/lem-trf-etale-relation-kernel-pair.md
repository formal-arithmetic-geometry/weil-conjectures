Files written:
- `dag/nodes/sec-trace-formula/lem-trf-etale-relation-kernel-pair.json` — statement, split proof, no new nodes, Mathlib criterion used.
- `citations.json` — citation for Step 3.

Attachments:
- None. No sorry-free project declaration states this item exactly.

WANTED:
- None. The relevant Stacks source is present under `literature/stacks-project/groupoids.tex`.

The item statement was checked against Stacks Groupoids Tag 045Y and the quotient-sheaf definition immediately preceding it. The fppf topology, fibre product, scheme, and sheafification notions in the statement are exactly those of the cited definition nodes. The current slopmaster2 source was searched for the item id, its blueprint tag, and the quotient/kernel-pair terminology; no declaration in `WeilConjectures/` states this result without `sorry`.

The proof has three steps. Step 1 reads the two equivalent conditions in Tag 045Y: equality in the sheaf quotient is witnessed after an fppf cover by a section of the relation. This is exactly local surjectivity of the canonical map. Step 2 checks local injectivity directly: equality of the two projections makes the two maps into the fibre product equal, and the assumed monomorphism of `j` identifies the relation sections. Step 3 applies the existing generic sheaf-of-sets local-bijection criterion; its statement says verbatim that a morphism is an isomorphism iff it is locally injective and locally surjective. I read the full statement of `lem-galois-set-sheaf-local-bijection-isomorphism` and copied the quoted sentence into `citations.json`.

I tested the argument on the identity relation (`R=U`), the empty scheme, and a relation with two equal projections. In each case the local witness and monomorphism arguments have the expected behavior. No statement was changed, no new node was created, and no SGA source was used. The generic local-bijection lemma is declared as a tool use because it belongs to another unit.

## Not duplicates

- `lem-trf-etale-relation-kernel-pair` vs `lem-trf-etale-relation-quotient`: the existing node assumes the additional etaleness of `s,t` and concludes algebraic-space representability plus the kernel-pair identity; this item isolates only the kernel-pair identity under the weaker monomorphic pre-equivalence hypotheses. The existing node cites this item, so it cannot be used as a dependency.

## Review by Q73

I read the item node, its source passage in `groupoids.tex`, and every statement node named in `stmt_deps` and `proof_deps`. Step 1 uses the quotient-sheaf and fppf-site definitions to interpret sections and coverings, then follows Tag 045Y's local relation witness exactly. Step 2 uses the fibre-product universal property and the stated monomorphism of `j`; no etaleness or representability assumption was silently added. Step 3 uses the cited local-bijection statement exactly as written, with the hypotheses supplied by Steps 1 and 2. I verified that all proof uses occur in `proof_deps`, that the citation quote is verbatim, that the blueprint ancestry remains `lem-trf-local-term-locality` via `lem-trf-etale-relation-quotient`, and that the existing stronger quotient node is downstream rather than a usable dependency. The only correction made was replacing the empty imported proof with these three source-driven steps and recording the generic criterion as a declared tool use.
