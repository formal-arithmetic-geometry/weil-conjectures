# Q127: sk-def-sfb-coefficient-comparisons

## Files written

- `dag/nodes/sec-six-functors-basics/sk-def-sfb-coefficient-comparisons.json`: definition, split into seven construction/verification steps using existing nodes; not a Mathlib leaf.
- `dag/units/sk-def-sfb-coefficient-comparisons.json`: only `realized` and `realized_by`, realizing all five unit proof paragraphs.
- `citations.json`: 29 verbatim statement quotations, one for each step/node citation.
- `report.md`: this report. `searches.jsonl` is the search command's log; `prepare.py` is the sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

`AddCommGrpCat.hasFunctorialFlatResolution` belongs to `lem-sfb-abelian-functorial-flat-resolution` (existing node, created by Q31). The item's imported open entry has `nodes: []`, but that node now supplies the exact statement. The current declaration is in `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean:148`, with body `infer_instance`. This is a requested attachment candidate, not a claim of verified transitive closure. No existing node or audit was edited.

The item's named comparisons are present in `WeilConjectures/SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean` and its formal module. Its audit is `rests_on_sorry`; the item therefore does not qualify as a finished attachment. I read the actual definitions of the coefficient squares and all underived/derived comparisons, including the flatness instance parameter and chosen compactification. The direct bodies lack `sorry`, but that does not establish closure of all their inputs.

## Wanted sources

None. The current blueprint definition and its accompanying proof are present, and they suffice for this formal construction split. No SGA source is used.

## Corrections and search findings

The statement is unchanged. The imported proof cited `sk-prop-sfb-cartesian-coefficients` for invertibility for an arbitrary commutative condensed ring. Its current statement asserts invertibility only for the enumerated admissible coefficients, so that citation did not justify the full quantified use. I replaced it with existing `lem-sfb-alpha-iso`, whose statement quantifies over any condensed ring and every scheme morphism. This repairs a citation, not the unit's route or statement.

The imported final step merely named two nodes. Steps 6–7 now specify the two whiskered factors, their domains and codomains, and the inverse when the proper-part comparison is invertible. Steps 2 and 4 specify the mate's unit/counit construction and distinguish it from conjugation, which is the reason Pull is invertible. All steps now have source places and explicit elementary judgments.

The logged Mathlib searches found general conjugation (`CategoryTheory.conjugateIsoEquiv`, read at `Mathlib/CategoryTheory/Adjunction/Mates.lean:425`), sheaf-module pullback adjunctions and their composition (`Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:167`), and condensed module definitions. These do not give this whole pro-etale ring-object construction on unbounded categories by one-line specialization. The first Loogle query contained an unknown identifier; its actual diagnostic is recorded, and I reran with `CategoryTheory.conjugateIsoEquiv`. A second semantic phrasing was also run and read. Existing nodes already state the general formal constructions and every required coefficient comparison, so no new node is justified. The full-DAG/blueprint coefficient-comparisons search additionally found ctf/direct-image/compact-support/ex-ceptional/Hom comparison nodes: those concern additional constructibility or invertibility assertions, not this formal definition.

## Not duplicates

No new nodes. All formal and coefficient comparisons are reused, and the previously unassigned flat-resolution open entry is matched to the existing Q31 node.

## Review by Q127

I read `GOAL.md`, the chapter record, this unit's record, the current `main-20261015` `_section.md` and `sk-def-sfb-coefficient-comparisons.proof.md`, and delivery-errors B–E in both copies. This is the unit's key definition. I retained its general condensed ring coefficients, its unbounded categories, and the flatness boundary between open extension by zero and the derived direct-image construction. No compiler or Lake command was run.

For step 1 I opened all six cited node statements. The square node supplies transport/restriction for a commuting square of ring objects, the underlying lemma specifies identity components, the conjugate and mate nodes specify their directions, and the invertible-square and projection-formula nodes give precisely the two extra formal comparisons. I use them as general construction inputs; I do not assert that a generic lax monoidal functor is exact or satisfies a projection formula. Their actual geometric instances are provided by the comparison nodes in subsequent steps.

For step 2 I read the coefficient-change statement's second commuting square, the module-pushforward/pullback statement's definition and adjunction, the change-of-scalars adjunction, and the statements of comap-lower-star, pull-iso and push-hom. They give exactly the composites and adjunctions used. I checked the component formula: after the unit, the inverse of the restriction/pushforward isomorphism has source `f_* Res_X`; the counit then removes `Ext_Y Res_Y`. Hence the resulting map points from scalar extension of pushforward to pushforward of scalar extension. There is no flatness hypothesis in this step.

For step 3 I checked the arbitrary-ring quantifier in `lem-sfb-alpha-iso`, then the source/target of `def-sfb-comap-upper-star-iso` and the explicit unbounded, levelwise statement of its derived version. These statements give the restriction/pullback comparison needed later. The narrower Cartesian-coefficients proposition was the one citation corrected. The alpha lemma is declared in split_report.tool_uses as a generic input from another unit; it does not replace any step of this unit.

For step 4 I checked the finite-limit hypothesis of both homology preservation and K-injective preservation: exactness of extension, assumed at every scheme, implies it. The derived comap-lower-star node supplies the derived natural isomorphism, not just objectwise identifications. The module-derived-pushpull statement gives `Lf^* ⊣ Rf_*`, and the coefficient-change statement gives `T ⊣ D(Res)`. The derived pull/push node statements specify the conjugate and mate for exactly those adjunctions. Thus the unbounded derived comparison is cited as a theorem/construction, not inferred just from the definition of flatness. The resolution and naturality work is already the subject of the existing derived comparison node; this item adds no new hidden claim about resolutions.

For step 5 I checked all four cited statements. The restriction/open-shriek node supplies its natural isomorphism; the underived extension/open-shriek node supplies the conjugate convention; module-lower-shriek gives exactness and `j_! ⊣ j^*`; the derived extension/open-shriek node explicitly constructs the conjugate along the derived open adjunctions on unbounded categories and explicitly removes flatness as a requirement. I rely on that node for the derived adjunction, rather than claiming that an arbitrary underived adjunction descends automatically. In particular the nonflat map of discrete condensed rings Z → Z/2 remains permitted for open extension by zero; it is not fed into step 4.

For step 6 I read the derived-lower-shriek definition and the comparison statement. Both use the same chosen compactification and define `Rf_!` as the composite of derived factors. Whiskering the already constructed Push_g and the open isomorphism has the displayed endpoints; this is elementary substitution/composition, not a new compactification-independence theorem. For step 7 I read the exact proper-part invertibility hypothesis in the existing criterion. The inverse written in the step is the reverse composite of the two whiskered inverses, with reverse associators. Its cancellation checks are elementary and require no extra geometric assertion.

I tested directions and endpoints also for f = identity, a = identity, and j = identity or the empty open immersion. The unit/counit formulas specialize to their triangle identities for identities; empty-source module extension by zero gives the zero objects and hence invertible open comparisons. No step asserts Push is always invertible. In step 6 the proper factor has source Z and target Y, so its coefficient functor is T^Z in the middle, not T^X. There are no new statements to test and no new node that restates a clause, duplicates a tag, or needs another split. The longest non-elementary step is 1162 characters, below the long-step threshold. Each citation is backed by an actual verbatim statement quotation in citations.json; no cited proof's internal construction is treated as an unstated theorem.

## Unfinished work

None in the assigned one-level split. Existing unresolved descendant results remain assigned to their existing nodes. Delivery validation and push are performed after this report is written.
