# Stage-1 repair: lem-trf-bounded-below-derived-mate-model

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-bounded-below-derived-mate-model.json`: repaired existing item, seven explicit proof steps. The mathematical statement and every hypothesis are retained; the only statement edit adds the citation for its canonical derived adjunctions.
- `dag/nodes/sec-trace-formula/lem-trf-bounded-below-derived-adjunction.json`: one new statement-only structural dependency, no proof or proof dependencies. Not an exact Mathlib leaf: the generic Mathlib derived-adjunction theorem needs absoluteness hypotheses beyond the node's hypotheses. Three existing project declarations jointly state this node, and their attachment is recorded below.
- `citations.json`: fourteen step/node entries with verbatim quotations from the actual cited statements, including the complete two comparison identities of the new node.
- `report.md`: this report. Existing `searches.jsonl` entries are retained; five actual searches for the new dependency were appended.

## Attachments

`CategoryTheory.Adjunction.derivedPlus`, `CategoryTheory.Adjunction.derivedPlus_unit_app_fac`, `CategoryTheory.Adjunction.derivedPlus_counit_app_fac` belong jointly to `lem-trf-bounded-below-derived-adjunction`, in `WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/PlusAdjunction.lean`, current declaration lines 133, 143, 154 (recorded map ranges 129–137, 139–149, 151–160). The source hypotheses and formulas were read, not inferred from their names. All three have `s=false, ts=false` in `local/sorry_map_slopmaster2_full.jsonl.gz`. Their declaration records are included in the new node; the authoritative `closed` state is left to the maintainer's attachment check/status tool.

The item itself is not an exact attachment: `CategoryTheory.Adjunction.derivedPlus_mateEquiv_app_fac` has an independently supplied derived square and an explicit factorization hypothesis. The repair supplies both, rather than treating that stronger-hypothesis theorem as already proving the item.

## WANTED

None. I read the relevant source in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/PlusAdjunction.lean`, lines 99–160 and 399–484, the termwise adjunction source `CategoryTheory/HomotopyCategory/Adjunction.lean`, and Mathlib's `CategoryTheory/Functor/Derived/Adjunction.lean`, including its four derived-functor hypotheses. Stacks `sites-cohomology.tex`, Tag 07A7, `remark-base-change`, was read for the counit-transpose convention; it does not itself state the abstract comparison formula. No SGA source is used.

## What was wrong or changed

The retained earlier delivery had three steps and no children. Its Step 2 wrongly treated the existence of right derived functors as giving an adjunction; its Step 3 applied a theorem without supplying its square or checking its factorization hypothesis. The previous report's claim that no independent dependency was needed was incorrect. Both returned points are repaired:

1. A strictly structural dependency now states the canonical bounded-below derived adjunction and both unit/counit comparison identities. It concerns only one adjunction and no mate or square; it does not restate the item's conclusion. Its three declarations already exist with no reachable sorry, so it is attached rather than split further. Step 2 cites its actual statement twice, with exactness and enough injectives checked on the correct target categories.
2. Step 3 constructs `θ : TwoSquare T E E' S` by the localization universal property. With the explicitly defined composites A_N and B_N, its defining formula is θ_(qN)=B_N⁻¹ q(σ^K_N) A_N. Multiplying by B_N proves precisely the source's hθ equation on every N in K⁺(B), including N=K(R)P used later. Steps 4–7 then prove the desired comparison equation directly from the mate formula and the cited adjunction identities. The source's mate theorem is not invoked as an uncited black box.

The returned work was retained and compared with the current shared item: the base statement, source, ancestry, chapter, unit, created metadata, and imported search records match; the base still has status unsplit. The returned head recorded by the sandbox was ed1262cf4b. As required, I first reran the unchanged retained split through `deliver.py --no-push`; it passed mechanically at 5db74b0ab3. That receipt did not address the mathematical return, so the changes above are substantive repairs, not an unchanged re-push. Existing search results about mates/derived functors were read and reused. No unit record was changed.

## Not duplicates

lem-trf-bounded-below-derived-adjunction vs lem-sc-derived-adjunction-from-underived: the existing Mathlib leaf assumes absolute derived functors as input; the new node establishes the specialized canonical bounded-below adjunction from exactness and enough injectives, and states both normalization equations. The existing node's counit display also uses composition in a different order; I use none of that display.

lem-trf-bounded-below-derived-adjunction vs lem-pc-derived-adjoint-functors: the existing node assumes everywhere-defined unbounded derived functors via essentially constant systems; enough injectives alone gives the bounded-below functors needed here, not those unbounded hypotheses.

lem-trf-bounded-below-derived-adjunction vs new-derived-adjunction-compatibility: the existing node takes essentially constant systems and derived-functor comparison hypotheses as inputs; it does not supply the bounded-below specialization or the two explicit identities.

lem-trf-bounded-below-derived-adjunction vs def-sfb-finite-derived-adjunction-plus: the blueprint node is a specific sheaf pullback/direct-image adjunction with its coefficient hypotheses, not arbitrary abelian categories or the unit/counit normalization needed here.

lem-trf-bounded-below-derived-adjunction vs lem-weil-pbc-termwise-adjunction-homotopy: the existing node is the adjunction before localization, not an adjunction involving the right derived functor.

lem-trf-bounded-below-derived-adjunction vs lem-trf-bounded-below-derived-mate-model: the new node supplies the one-adjunction structural theorem used by the mate computation. It contains no G, H, σ, b, derived square, or assertion of the item's displayed mate equation.

I searched the entire DAG by `derivedPlus`, bounded-below adjunction, normalization, and the declaration names, and inspected the generic derived-adjunction and homotopy-adjunction statements above. Blueprint searches for `derived adjunction`, `derivedPlus`, `unit counit`, and `bounded below derived adjunction` produced no general matching blueprint node. The inherited blueprint ancestor and via chain are retained. There is no Stacks-tag source claimed for the new project-specific normalization lemma, so no same-tag duplicate pair is being suppressed.

## What remains

The item has a complete comparison calculation. The new dependency is statement-only with existing closed declaration attachment candidates. The maintainer must independently verify that attachment; I have not assigned a `closed` verdict. No Lean was written or compiled, and all writes are confined to this sandbox.

## Review by Q32

I reread delivery-errors B–E against the repaired files and the sources above, and the chapter and sk-i-curve-zero unit. This is a generic categorical input to the inherited normal-cone specialization descent, not a replacement for the unit's geometric route. The item has no blueprint update to apply. The only new node concerns the adjunction structure already used by the imported statement, and all its objects and size hypotheses are introduced. Its proof, proof dependencies and proof origin are empty/null, with the argument supplied by existing declarations rather than a proof sketch smuggled into its statement.

Step 1 uses the exact-functor factorization statement for the natural φ comparisons and for quasi-isomorphism preservation. Its homotopy assertions are written as the additive homotopy equation, and the chain map σ^K is checked against each differential by naturality. Passing to bounded-below complexes requires only preservation of zero terms. Step 2 uses precisely the existence/naturality clause of the right-derived-plus node, the new node's adjunction and comparison clauses, and the termwise-homotopy adjunction statement's clauses (a)–(c). A and A′, the sources of R and R′, have enough injectives; neither B nor B′ is assumed to have them.

Step 3 uses the localization universal property's clause (2), whose statement explicitly lifts natural transformations with the prescribed conjugation formula. Both sides invert quasi-isomorphisms because all four functors defining them are exact. The A_N and B_N comparisons have the same source and target as the source theorem's Factorsh maps. Multiplication by B_N proves hθ; it is not an additional unproved hypothesis. This single lifting application is smaller than the mate theorem and is already a Mathlib leaf.

Step 4 expands the mate's defining component formula (the exact formula in the mate-definition statement), and writes the two naturality equalities used to move t and α_P. Step 5 substitutes the new node's counit equality and the exact-localization isomorphism's naturality, then uses the actual hθ proved in Step 3. I checked the source and target of every factor: d runs from K(L′)K(G)K(R)P to K(H)P. Step 6 substitutes the new node's primed unit equality and naturality of α′ on this very d. It never applies an injective-resolution isomorphism to H(P). Step 7 uses the cited termwise unit/counit and mate statements to identify the composite in each degree with b_(Pⁿ); the final equation includes φ_H on the target and φ_G⁻¹ on the source, so the transport to the item's notation is explicit. Steps 4–7 are short substitutions and naturality calculations from these already cited statements; every equality used is written. No step is over 2000 characters and no independent comparison lemma is hidden in a long step.

For the new node, I matched the source declarations' universes, abelian and enough-injectives instances, exactness instances, and both formulas with its statement. The two exactness instances are precisely preserving finite limits and finite colimits; the source assumes enough injectives only in A. The generic Mathlib search hits were read: they do not remove the absoluteness checks in the specialized construction. The source establishes those checks before defining derivedPlus, so I record the project attachment rather than claim a one-line Mathlib specialization. The new node's searches are the five queries actually recorded by msearch.py, including two different semantic phrasings. Prior item searches and their results remain unchanged.

Small cases checked: identity adjunctions give the usual termwise mate; σ=0 gives zero on both sides without an invertibility assumption; the zero complex gives the zero-object equality; arbitrary negative lower bounds remain allowed. For an exact H not preserving injectives, take the forgetful functor from F_p-vector spaces to abelian groups (F_p is injective over F_p but not over Z), and take the two vertical adjunctions to be identities: the calculation remains valid. The new adjunction statement also permits B without enough injectives, e.g. the zero adjunction from finitely generated abelian groups to the zero abelian category. These checks expose neither a missing boundedness nor an illicit injectivity assumption.

For C4, every citation was opened and its actual statement copied into citations.json, with the substantive new adjunction identities quoted together. For C1/D3, the structural adjunction theorem and the localization lifting theorem are named dependencies; the mate calculation itself is written, not outsourced to the source's conclusion. The off-unit homotopy adjunction is declared in split_report.tool_uses as a generic categorical tool. The dependency graph contains no edge back from the new structural node to the item. The earlier malformed control characters in the proof's alpha notation were eliminated by rewriting the steps with proper TeX.

The first repaired dry run rejected the phrase “the item’s equation” in Step 7 as a self-containment lint. I replaced it with “the displayed conclusion”; no object, hypothesis or mathematical equation changed.
