# Stage-1 report: lem-coef-sequence-adjunction-cochain-transposes

## Files written

- `dag/nodes/sec-six-functors/lem-coef-sequence-adjunction-cochain-transposes.json`: statement, split; six proof steps, no new nodes, no Mathlib match for the whole item.
- `citations.json`: verbatim statements supporting all ten step/node citations.
- `searches.jsonl`: six searches actually run with msearch.py; both semantic phrasings, Loogle, LeanSearch, and source grep. The earlier searches in the repository node were retained.
- `report.md`: this report. `write_split.py` is sandbox-only preparation, not part of the DAG delivery.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint id, cochain transposes, sequence/scalar adjunctions, and the SystemScalarModel and derived-change-of-rings names. There is no project declaration stating all clauses of the item. Ordinary tensor units and abstract derived-adjunction transformations in Mathlib are insufficient to attach this item.

## WANTED

None. The Stacks sources needed for the proof are present locally.

## Corrections and scope

The item was statement-only, with no proof. I kept its statement, statement dependencies, source, creation record, and blueprint provenance. No statement dispute was found. I added a complete calculation rather than creating separate nodes for the unit and counit, which would simply restate the two principal clauses.

The blueprint ancestor is `prop-coef-integral-exceptional-adjoint`. I read its available master blueprint file, especially proof paragraph 2 (derived coefficient adjunction) and the following paragraph on units and counits. The same relative node file is absent from the main-20261015 and main-20261017 snapshots in the read clone. The ancestor's current DAG proof and this item's precise `blueprint.from.place` specify the untransported coefficient-adjunction calculation. This split supplies that calculation; it does not replace the unit's geometric or coefficient-transport route. I read the chapter and unit records and the three levels in SETUP.md; this is not the key statement of the unit, so no unit record was changed. Whole-blueprint searches for tensor/limit, cochain transposes, cochain unit, and simultaneous derived scalar returned no equivalent blueprint node. The broader adjunction search found other adjunctions but none with this statement.

The useful existing general node is `lem-pur-sheaf-ring-derived-coefficient-adjunction`, not the more restrictive `lem-weil-derived-scalar-extension-restriction-adjunction`, which is about completed DVR coefficients on scheme pro-etale sites. I opened both and used only the genuinely general statement. Likewise, the ordinary scalar adjunction is in `lem-pur-sheaf-ring-coefficient-ordinary-adjunction`; it explicitly includes the sheafification-unit section formula, so the argument does not assume all sheaf-tensor sections are global pure tensors.

## Mathlib assessment

I read `Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean`, lines 20-158. The derived unit/counit results need derived-functor comparison and postcomposition-derivedness hypotheses; they do not construct the particular ringed-sequence comparison or establish these representative formulas by a one-line specialization. I read `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`, lines 905-923: the unit and counit formulas there concern ordinary modules. The sheaf pullback/direct-image hits are also ordinary adjunctions (`Sheaf/PullbackContinuous.lean`, lines 60 and 79; `Sheaf/PushforwardContinuous.lean`, line 274). None states this unbounded sequence-system calculation. The actual search results were read, and no unavailable response was treated as a negative result. No new node or Mathlib leaf was created.

## Review by Q24

I read Stacks `sites-cohomology.tex` Tag 07A6 (`lemma-adjoint`), Section 07A5 (the K-injective construction of total direct image), and the full statement and proof of Tag 0FPI (`lemma-adjoints-push-pull-compatibility`). In 0FPI the chosen flat-term K-flat complex resolves the ordinary direct image of the K-injective complex; the proof does not assume that this direct image is itself K-injective. I also read `derived.tex` Tags 0FND and 09T5 and their surrounding pre-derived Hom calculation, and `sites-modules.tex` Tag 03D7 and Section 03EK for the sheafified tensor convention. The counit follows 0FPI. The unit calculation and explicit scalar/transition calculations are my deductions from the normalized adjunction, so proof_origin is agent rather than claiming the unit is written verbatim in 0FPI.

For step 1 I checked the full statements of the two general ring-sheaf coefficient nodes. The derived one supplies exact restriction, the flat-term K-flat comparison, the pure-tensor unit, and inverse adjuncts for arbitrary target complexes. The ordinary one supplies the actual sheaf-section transpose and its sheafification unit. The adjunction identity gives the transpose of f by composing restriction of f with that unit. No restriction to quotient rings, constant rings, or K-injective targets is introduced.

For step 2 I checked that the sequence-projection node's statement includes the ordinary Hom correspondence and the ordinary direct image as the restricted inverse limit. I wrote both inverse assignments, the horizontal transition equation with the ring map rho, both differential equations, and the inverse identities. The ordinary scalar node justifies interpreting local tensor formulas as sheaf maps. In particular, no surjectivity or flatness of a ring transition is used.

For step 3 I checked that the projection node explicitly states that its Hom bijection is the derived fraction extension of the specified ordinary correspondence and that a single flat-term K-flat source computes all levels. The total-direct-image node explicitly says that ringed-topos direct images are computed by K-injective resolutions; only that part of its statement is used. The source sequence site is small, so its smallness hypothesis is satisfied. The resulting normalized equation is applied only to the actual chain maps a and v_q, with K-injective system target. There is no claim that every derived map from an arbitrary K-flat complex is a chain map. The generic ringed-topos computation node is declared in split_report.tool_uses; no off-route geometric result is used.

For step 4 I checked the types of j=[a]c_Q and Rp_*(j). The normalized Hom equation identifies Phi(j) with the specified cone map, while naturality gives Rp_*(j) composed with the unit. Thus Rp_*(j) is exactly the resolution identification, not an extra isomorphism chosen after the calculation. The family really is compatible and a chain map by the equations already written in step 2.

For step 5 I checked that k=[q] has target [FI]=Rp_*[I], and that Lp^*(k) must be inverted on the source of the counit representative. The ordinary transpose of v_q equals q on every projection. Naturality in the first variable sends the displayed composite to k k^{-1}=1, so it is the counit by the definition of the inverse Hom bijection. This checks the orientation of both resolution isomorphisms and all domains; the formula is not obtained by declaring componentwise equal derived maps equal as systems.

For step 6 I checked that all formulas were identified with the fixed canonical adjunction maps. Their naturality and resolution independence therefore follow from these identities under the prescribed comparisons. Right-derived evaluation was performed only on the system I, and the scalar theorem allows arbitrary targets. No K-injectivity claim about U_0I or I_n is used anywhere.

I tested the formulas for zero complexes, identity coefficient maps, and constant coefficient towers, where they reduce to the ordinary tensor unit and evaluation counit. I also checked the nonflat map of constant sheaves Z to Z/2 with a flat-term K-flat source, and transitions through a zero ring: the tensor/transition equations still hold and nowhere cancel coefficients. Negative degrees and unbounded complexes use the same degree-zero tensor formulas, so no additional sign or boundedness assumption appears. These are checks of the stated formulas, not substitute hypotheses.

Against delivery-errors B-E: there are no new nodes needing a definition audit or duplicate comparison; all cited statements were opened, every non-elementary input is an existing cited node, and the proof is carried by explicit calculations. All six steps are shorter than 2000 characters. The unit and counit clauses have not been moved into new nodes. The statement is unchanged and no target meaning was altered.

## Not duplicates

No new nodes.

## Unfinished work

None in the stage-1 split. No Lean was written or compiled. Independent maintainer review remains part of the delivery process.
