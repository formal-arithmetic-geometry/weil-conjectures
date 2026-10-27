## Files written

- `dag/nodes/sec-trace-formula/lem-trf-lci-fibre-tensor-transition.json`: statement, now split in six steps; not a Mathlib leaf as a whole. No new nodes and no new Mathlib leaves.
- `citations.json`: verbatim statement quotes for every node used by each proof step.
- `searches.jsonl`: actual searches made with the prescribed command; their results are preserved verbatim in the item's added search records.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for syntomic, complete-intersection and tensor-fibre notions. The project's `CompleteIntersectionOverField.lean` supplies definitions, not a theorem giving this item's clauses. Other existing relative-global-complete-intersection results are different statements. No exact project declaration was found.

## Wanted literature

None. The relevant Stacks source is available locally.

## Corrections and route

The original statement is retained, including arbitrary transition maps and the absence of flatness or finite-presentation hypotheses on the original coefficient maps. The empty imported proof was replaced. Its statement dependencies gained the existing algebra-tensor pushout node, which supplies the ring/algebra structure implicit in the displayed tensor products.

Read the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md` and its proof. That current proof uses contracting correspondences, not the historical nearby-duality/alteration route recorded in this item's ancestry. This delivery supplies only the existing historical algebra obligation, as recorded in `blueprint.from.place`, and does not change the chapter, unit, ancestor statement, or route. `split_report.blueprint` says this explicitly.

Stacks 00SN's printed proof cites `lemma-compose-finite-type` for the finite-presentation permanence clause; that lemma concerns composition, whereas 05G5(4) states the required base-change result directly. The proof therefore cites the existing `lem-weil-pbc-finite-presentation-base-change-composition` for its base-change clause, with 05G5(4) as the precise source. This corrects the source's imprecise reference without changing any mathematical statement.

## Not duplicates

No new nodes were created. Whole-DAG searches by tags 00SN, 00SJ and 00HI and by titles/keywords found the existing tensor pushout, tensor cancellation, prime-residue-field algebra, flat-module base-change, finite-presentation base-change/composition, and lci field-change nodes. Those are reused. `tools/blueprint_refs.py ancestor` identifies `lem-trf-local-term-locality`; searches for `complete intersection`, `00SJ` and `00SN` found no blueprint node stating this item. Broad tensor and residue-field blueprint searches were also inspected; they concern other statements.

## Review by Q156

I read Stacks `algebra.tex` at 00SN (`lemma-base-change-syntomic`) and 00SM (`lemma-syntomic-descends`), including the displayed residue-fibre identity. I checked 00HI's flat-module base-change statement, 05G5(4)'s finite-presentation base-change statement, 00SJ's field-change statement with its finite-type hypothesis, and 00S9's complete-intersection definitions including the zero-ring convention. I also read the induced residue-field-map paragraph after 07BI and the tensor universal-property material 00CV/00CX. There are no new-node sources to review.

For steps 1 and 2 I opened `lem-weil-pbc-algebra-tensor-pushout-universal-property` and `def-weil-pbc-module-tensor-product`. The former actually gives the multiplication, maps out, and uniqueness used to construct theta and eta; the latter gives the balancing relations and generation by pure tensors. The maps agree on B_k because phi_0 is an R_0-algebra map. Eta is B_j-linear precisely by the balancing relation involving phi_0(b), not by an unproved claim that scalar extension is flat. Both composites are computed explicitly. These are elementary calculations with the cited universal properties, not new lemmas.

For step 3 I opened `lem-weil-pbc-prime-residue-field-algebra`: clauses (a) and (d) provide exactly the kernel assertion and factorization used. Primality of the inverse image is proved directly; elements outside it have nonzero image in a field and are therefore units. No residue-field map is assumed without checking its existence. Injectivity is the elementary kernel argument for a unital field homomorphism.

For step 4 I opened `lem-weil-pbc-tensor-cancel-base-change`. It states an algebra isomorphism, not merely a module isomorphism, with the precise pure-tensor and inverse formulas. Apply it to the towers B_k -> B_j -> kappa(q) and B_k -> kappa(p) -> kappa(q); step 3 provides compatibility of the latter tower. The tensor symmetries are the explicit balanced swap maps. I wrote both directions of the resulting fibre comparison and evaluated them on C_k and kappa(q), so compatibility with canonical maps is checked, not asserted as transport. This is an application of the existing cancellation theorem with elementary symmetry and substitution, not a hidden comparison lemma.

For step 5 I opened `lem-weil-pbc-flat-module-base-change`, `lem-weil-pbc-finite-presentation-base-change-composition`, and both finiteness definitions. The first result is for arbitrary base maps and a flat module, exactly the hypothesis on C_k as a B_k-module. Clause (1) of the second result likewise allows arbitrary base maps. I apply it twice, to B_j and to kappa(p). The finite-presentation definition gives finite algebra generators directly, verifying the finite-type hypothesis for the next step. Flatness and presentations pass through theta because it is a B_j-algebra isomorphism, already proved in steps 1--2.

For step 6 I opened `lem-weil-pbc-lci-field-change` and `def-weil-pbc-complete-intersection-over-field`. The cited theorem requires a finite-type k-algebra, which step 5 supplies, and a map of fields, supplied by step 3; its forward direction gives exactly the required scalar extension. Invariance under a K-algebra isomorphism is definitional: pull each principal-open generator across the isomorphism, use the induced localization isomorphism and compose each polynomial presentation; the bijection of prime ideals preserves chains and hence Krull dimension. The zero-ring case uses the stated zero-ring convention. This field-change result is recorded as a generic off-unit tool in `split_report.tool_uses`, since the unit's own statements do not give field-extension invariance of complete intersections. Other off-unit tools used here are existing Mathlib leaves.

I checked delivery-errors B--E against the files: every object is introduced in the unchanged statement; every non-elementary theorem used has an existing node and a verbatim citation; no new statement merely restates an item clause; and no proof uses the interior of another node's proof. Steps are all below 2000 characters. No Lean file or build was written or run, and no repository or launcher file was changed.

Small cases checked: identity alpha gives the identity tensor comparison; B_0=C_0 and phi_0=1 gives the usual coefficient-base-change identity; noninjective alpha, such as Z -> F_p, still satisfies every displayed balancing equation. The zero source algebra C_0 gives zero fibres and the permitted complete-intersection convention. If B_j is the zero ring there are no primes q, so the fibre assertion is vacuous and the tensor statements still hold. No nonzero-fibre assumption, injectivity of alpha, perfection of the residue fields, or finite type of R_0 -> B_0 was used.

## Unfinished work

None for this one-level split. Existing unsplit/sorried dependencies remain the responsibility of their own DAG items.

## Validation

The required remote dry run exited successfully: `OK (not pushed)` at `11b717cf7c0`, with server preflight passed. A final dry run is being made after recording that result and spelling out the definitional isomorphism-invariance argument in step 6.
