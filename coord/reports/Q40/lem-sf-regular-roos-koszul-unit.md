# Q40: lem-sf-regular-roos-koszul-unit

## Files written

- `dag/nodes/sec-six-functors/lem-sf-regular-roos-koszul-unit.json`: statement, split using existing nodes; not a Mathlib leaf. Statement and statement dependencies unchanged. Five proof steps, 3348 characters in total, longest step 934 characters.
- `citations.json`: one entry for every step/node pair, quoting the full verbatim statement of the cited node so that all clauses used are visible.
- `searches.jsonl`: actual searches recorded by the prescribed msearch command. The five new searches are also appended to the item's existing search history.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched `lean/WeilConjectures/` by the exact blueprint tag and by Roos, Koszul/completion and canonical-unit terminology. The existing `DerivedCategory.derivedComplete`, `derivedComplete_iff` and `derivedComplete_iff_exists_iso` in `CategoryTheory/DerivedCategory/Complete/Defs.lean` concern constant-ring sheaves and an existential homotopy-limit condition, not the arbitrary sheaf of rings, local internal-Hom criterion and specified strict-tower unit of this item. They do not justify attachment. No Lean was written or compiled.

## WANTED

None. The sources needed for this split are available locally. The current live source metadata of the unit and ancestor mentions main-20261017, which is not present at that path in the read clone; I read the explicitly designated main-20261015 snapshot, `blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md`, and the live DAG unit and ancestor. Its quoted sentence about tensor reassociation, evaluation, units and counits agrees with the item's blueprint origin.

## Corrections and limitations

No statement dispute or correction. The item was unsplit and the sandbox had no earlier split/report, so there was no interrupted delivery to repeat. No repair-note file exists for this item in the read clone. The proof distinguishes the existence of an isomorphism supplied by a Roos triangle from invertibility of the specified completion unit. It obtains the latter through local completeness and the reflector theorem; it does not deduce equality of maps to a total limit from their projections.

The old parent was used only as context. All mathematical uses in the delivered proof cite the statements of existing nodes. In particular, the parent's historical proof and review are not used as an extra lemma.

## Existing nodes and Mathlib searches

Before choosing dependencies I searched the whole DAG and blueprint (`blueprint_refs.py search Koszul`, `Roos`, `completion`, and ancestor) and read the statements of the reconstruction, reflector, strict-tower limit and counit/projection nodes. These supply precisely the distinct facts needed, so no elementary step or existing clause was repackaged as a new node. The exact-product node `lem-pe-kflat-roos-representative-invariance` was inspected and deliberately not used: its exactness assumption is absent here.

The prescribed command ran grep, Loogle, LeanSearch and two differently phrased LeanFinder searches. Grep and Loogle returned no hits. LeanSearch returned AdicCompletion, IsAdicComplete and associated ordinary module-completion constructions. The first LeanFinder query returned sheaf generators and relations, and the second returned Tor and ordinary left-derived functors. I read the displayed types: none gives unbounded module-sheaf completion with derived products and the specified canonical units. The service results were successful, so none is recorded as unavailable. Earlier search records were retained unchanged.

## Not duplicates

No new nodes were created. The split directly reuses existing generic comparison and reflector results.

## Review by Q40

I read algebraization.tex Tag 099B (`lemma-derived-completion`), including its construction as derived Hom out of the extended Cech complex and its universal Hom bijection, and Tag 0A0E (`lemma-derived-completion-koszul`), including the finite-free Koszul duality and derived-limit formula. I also read the local definition in Tag 0999 (`definition-derived-complete`), the full proof of sites-cohomology.tex Tag 0941 (`lemma-derived-limit-is-ok`), and derived.tex Tags 09T5 (`lemma-derived-adjoint-functors`) and 0FND (`lemma-pre-derived-adjoint-functors-general`). The proof here is an agent-written assembly of those sources through the existing DAG statements. There are no new node statements requiring an independent source audit.

Step 1 uses the first assertion of `lem-pur-derived-complete-koszul-reconstruction`, which states the strict levelwise quasi-isomorphism and its derived-limit isomorphism for an arbitrary small ringed site, regular global element and K-flat representative. The variables match after renaming that node's K to our P and its representative to our Q. The node explicitly includes compatibility with strict augmentations. `lem-coef-derived-tower-counit-projections` supplies the actual derived constant-tower adjunction. I wrote the equality of strict augmentations before applying Rlim and its unit, so the equation c kappa = comp uses functoriality, rather than uniqueness from projections. Naturality follows from the tensor/quotient chain maps and, for derived objects and choices, the universal identification explained in Step 5.

Step 2 uses exactly the concluding criterion in `lem-weil-pbc-ringed-koszul-completion-reflector`: its unit is invertible if and only if its source is locally derived complete, and its target always satisfies that condition. A one-element list is allowed. Its transition is multiplication by t in degree -1 and identity in degree zero, matching this item. Its local condition quantifies over every object and every local section of the generated ideal; it is not just the weaker test at the single global section. The equality in Step 1 and invertibility of c then give the third equivalence by composing inverses.

Step 3 takes the *second* assertion of `lem-pur-derived-complete-koszul-reconstruction`, not merely its quasi-isomorphism clause: the given Roos triangle produces an isomorphism P to C_t(P). It does not say that isomorphism is kappa. I used the reflector's target-completeness assertion and the functoriality explicitly stated in `def-pur-derived-internal-hom` to carry vanishing across that isomorphism on each slice. Thus no hidden identification of two morphisms into a homotopy limit occurs.

Step 4 applies the distinguished triangle statement of `lem-weil-pbc-ringed-strict-tower-homotopy-limit` to U. It gives the actual total right derived limit and products in the derived category without exact products in module sheaves. Distinguishedness is preserved by isomorphism, as recorded in `def-weil-abstract-derived-category`. To verify that the first components are the actual quotient reductions, I used the counit/projection equality of `lem-coef-derived-tower-counit-projections` and wrote the counit-naturality and triangle-identity calculation. This is a proof of normalization, not a reference to a definition that does not give it. Only invertibility of comp is assumed at this step.

Step 5 is elementary once the reflector Hom bijection is available. Applying the bijection twice gives opposite maps between two completion objects preserving their units; injectivity of that same bijection makes both composites identities. Conjugation with the two c maps gives the required identification of quotient limits, carrying comp to comp. The uniqueness argument also proves transitivity and naturality. This avoids importing exact-product representative invariance. It proves independence of the four conditions and of the specified comparisons up to the unit-preserving identifications; it makes no canonical choice of the existential Roos-triangle comparison.

I checked all size and regularity hypotheses: the site is small in the module universe; module sheaves and strict towers are precisely those of the cited generic theorems; t is regular on the ring sheaf, not on P, and no flatness of P itself is required beyond its K-flat representative. The cases P=0 and t invertible give zero completions and all four conditions equivalent to P=0 in the unit case. If t=0 is regular, the ring sheaf is zero and all module objects vanish. A point site with O=Z and t a prime recovers ordinary principal derived completion; O[1/t] has zero completion and is not complete when nonzero. The argument also admits unbounded P and sites whose countable products are not exact, since no termwise-product model is used. Nonregular t is outside the hypothesis and is never used to claim that a Koszul resolution equals a quotient.

I checked B--E against the written files: there are no new statement-only nodes with hidden proofs, no duplicate or clause-restatement nodes, and no Mathlib leaf with an unchecked match. Every cited node's statement was opened and is quoted verbatim in citations.json. The generic lemmas used off-unit are declared in split_report.tool_uses with their precise role. All five proof steps are below 2000 characters; none contains an unexposed comparison lemma. The original statement, source metadata, blueprint origin chain and maintainer-owned fields were retained. No SGA source was used.

## Unfinished work

None in the stage-1 split. Existing dependencies retain their own live proof/Lean status and are not re-split by this delivery.
