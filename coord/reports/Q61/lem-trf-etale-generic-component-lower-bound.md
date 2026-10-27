# Q61 stage-1 report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-etale-generic-component-lower-bound.json — statement item, now split; five steps, 2172 proof-text characters, no new nodes and no new Mathlib leaves.
- citations.json — one verbatim statement quotation for each cited node in each proof step.
- searches.jsonl — actual msearch output, retained; prepare.py is a sandbox-only preparation script.

The item's statement and statement dependencies are unchanged. The existing six Mathlib searches and provenance fields are retained; the five actual searches made during this attempt are appended. No Lean file, compiler, Lake command, repository write or git command was used.

## Attachments

None for the item. The already existing lemma AlgebraicGeometry.exists_etale_generic_residue_field_model (lean/WeilConjectures/AlgebraicGeometry/EtaleGenericResidueFieldModel.lean:46) covers only the model input and is already bound to lem-sbc-etale-generic-residue-field-model. Its complete proof was read; it does not prove the fibre lower bounds, so it is not an attachment for this item.

## WANTED

None.

## Findings and corrections

No statement dispute. The item allows a nonreduced irreducible base, a possibly empty generic fibre, an arbitrary field extension in its last conclusion, and does not assume Noetherianity. All of these are retained. Its split can be assembled entirely from existing statements: making fresh nodes for the model or component comparisons would duplicate existing nodes and merely move clauses out of the item.

The source place originally described the second paragraph of 055A as the model construction. That paragraph invokes 0551; I read 0551's actual monic-polynomial construction, not only 055A's reference. I also read 0554's component-closure proof, 01T4's base-change assertion, and 04KW/04KX's full statements and proofs. Step sources identify these exact labels and tags.

The latest blueprint files for sec-trace-formula, sk-i-curve-zero and lem-trf-local-term-locality (statement and proof) were read. The current ancestor proves local terms through contracting correspondences and does not contain the older semistable-alteration chain described in the item's inherited blueprint.from.place. That provenance is preserved, and this delivery completes the already assigned descendant through its supplied Stacks route; it proposes no change to the chapter or unit. This historical mismatch is explicitly recorded in split_report.blueprint.

## Not duplicates

No new nodes were created. DAG searches found and reused lem-sbc-etale-generic-residue-field-model, lem-sfb-finite-type-composition-base-change, lem-trf-generic-fibre-component-lower-bound, and lem-sfb-field-extension-irreducible-components. Whole-blueprint searches for generic residue, component count, etale generic, 0554 and 04KX returned no imported blueprint statement replacing the item. The project Lean search by exact blueprint tag and component/generic concepts found no declaration proving all its clauses. GenericComponentsSplit and GenericFibreComponentSpread concern different splitting/spreading assertions.

## Review by Q61

I checked B--E with the cited node statements and local Stacks sources open. No new unsplit statements need independent small-case testing, sources or searches. Every use has its actual verbatim statement in citations.json; no proof implementation of a cited node is being used as an extra conclusion. Every proof step is shorter than 2000 characters, and the full assembly is shorter than 3000.

Step 1 uses exactly the prescribed-map compatibility stated in lem-sbc-etale-generic-residue-field-model. Its hypotheses are an irreducible scheme and the given finite etale spectrum map; the item supplies both. The cited theorem's generic point is generic in the whole source, as confirmed by its Lean signature IsGenericPoint ξ Set.univ. I explicitly deduced irreducibility of T from the closure of that singleton, using def-sc-generic-point and def-weil-irreducible-components, rather than assuming that an arbitrary etale source is irreducible. This works equally for nonreduced S and for the identity field extension.

Step 2 uses only the universal property and functoriality stated in def-pc-fibre-product and the actual scheme-theoretic fibre stated in def-pc-scheme-fibre. It writes both directions using r and its inverse, and identifies the maps to S by Step 1's equality. The resulting maps are mutually inverse by uniqueness for the pullbacks. There is no unsupported identification based merely on an isomorphism of abstract residue fields, and no new comparison lemma is concealed here.

Step 3 uses clause (2) of lem-sfb-finite-type-composition-base-change: exactly the projection from X times_S T. The source 01T4 and the Mathlib match were read. Finite type of f is supplied; g needs no extra property for this application. This is already a Mathlib leaf, so it is not an off-unit route replacement.

Step 4 uses the entire ordinary lower-bound assertion of lem-trf-generic-fibre-component-lower-bound, whose hypotheses are finite type, an irreducible base and a finite generic component count. Steps 1--3 provide them. That statement promises a nonempty open, and I wrote the elementary argument showing it contains ξ; I did not silently replace nonempty with a pointed neighborhood. No geometric irreducibility, flatness or Noetherianity is taken from it.

Step 5 uses the surjectivity clause, not just the inverse-image clause, of lem-sfb-field-extension-irreducible-components. Its source 04KX asserts surjectivity for arbitrary field extensions, including transcendental and inseparable ones. I spelled out how preimages of n distinct downstairs components are distinct upstairs. This proves a lower bound, and does not incorrectly assert component-count equality. The n=0 and empty-fibre cases give the vacuous lower bound; the identity extension and a reducible generic fibre also fit. The cited theorem has no finite-type hypothesis to check at this step.

The model and field-extension comparison are generic tools from other units and are declared in split_report.tool_uses. Their statements were checked rather than relying on their source citations alone. No SGA source is used. No new notion, axiom, hidden construction, circular citation, or changed target statement was introduced.

## Unfinished work

None in the split. Its existing unsplit descendants remain separate queue items according to the stage-1 contract.
