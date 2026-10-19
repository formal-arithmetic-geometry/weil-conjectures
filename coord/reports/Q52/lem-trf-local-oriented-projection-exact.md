## Files written

- `dag/nodes/sec-trace-formula/lem-trf-local-oriented-projection-exact.json`: statement, now split into eight proof steps. Statement unchanged. No Mathlib match.
- New nodes: none. New Mathlib leaves: none.
- `citations.json`: verbatim statement quotations for every citation in every proof step.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item id, oriented products, and strictly local notions. The hits concern Gabber's other theorem and w-strictly-local rings, and do not state this assertion. A read-only concept check in the upstream master source also found no oriented-product comparison declaration. No Lean was written or compiled.

## WANTED

None needed for this split. The existing item also mentions Illusie's Around the Thom--Sebastiani theorem, but the proof here uses the available ILO volume, not that secondary citation.

## What was wrong or incomplete

The item had a correct statement and no proof. It now has the explicit neighbourhood refinement missing from the bare assertion of cofinality in the source, both directions of the resulting stalk comparison, and a calculation identifying that comparison with the unit-defined map in the statement. The old statement dependencies were retained and supplemented by the constant-sheaf and geometric-morphism definitions.

Source error: ILO Exposé XI Corollary 2.3.1 prints the enough-points hypothesis on S. The displayed transformation is on Y, and Proposition 2.3 proves its isomorphism on the points of Y. That argument requires a conservative point family on Y. Here Y is the arbitrary scheme B, whose small etale topos has enough geometric points; the proof uses that fact explicitly and makes no inference from enough points of S to enough points of an arbitrary topos Y. This is a correction of the application of a source typo, not a change of the item's statement.

The blueprint's chapter and unit route are unchanged. This item is the general local-projection tool already introduced below the normal-cone specialization argument, not a replacement of the contracting-correspondence route. Off-unit general tools are declared in `split_report.tool_uses`.

## Unfinished work

None at this level. Supporting nodes retain their current status; no statement-only node was created or split beyond the assigned item.

## Search and reuse

I searched the whole DAG for oriented products, local topoi, canonical sections, strict henselian global sections, representable stalks, and filtered module colimit representatives. `tools/blueprint_refs.py ancestor lem-trf-local-oriented-projection-exact` gives `lem-trf-local-term-locality`. Whole-blueprint searches for `oriented`, `strictly henselian`, and `local topos` gave no second blueprint statement of this item. In particular the existing general strict-local set-sheaf theorem, site-point fibre theorem, filtered-module elementwise colimit leaf, and constant-coefficient inverse-image theorem cover the inputs; no new local-topos/cofinality/transport node is needed.

The item's inherited searches were preserved. The new actual `msearch.py` calls and their results are in `searches.jsonl` and appended to `mathlib_searches`: two LeanFinder phrasings, Loogle `"oriented"`, source grep `oriented.?product|localTopos|canonicalSection`, and LeanSearch for Gabber's exact projection on modules. Both semantic searches returned unrelated pullback/range, sheaf, and module declarations; Loogle returned oriented ordering classes; grep found no hit. None states the item or specializes to it in one line.

## Not duplicates

There are no new nodes. In particular the two local-section and colimit facts were reused rather than restated. The refinement of pointed triples is proved in steps 4--6 of the item; moving it into a new statement would move the main argument of this item rather than split it usefully.

## Review by Q52

I read ILO, Exposé XI, 1.3--1.4 for the projection and inverse-image conventions, 2.1--2.2 for local topoi and the canonical section (2.a)--(2.f), and Proposition 2.3 / Corollary 2.3.1 on printed pages 177--178. I also read the current `main-20261015` blueprint unit and the proof paragraph “(1) and (2)” of `lem-trf-local-term-locality`, plus the DAG chapter/unit records and the item's ancestry. The source's hypotheses are exactly the ones used: A and S are strictly local, a takes centre to centre, b is arbitrary, and the coefficients are constant modules over an arbitrary commutative ring. No coherence, finite type, torsion, or boundedness assumption enters this underived comparison.

I opened every cited node and checked its statement, not just its proof or source label. The supporting source passages read were Stacks etale-cohomology.tex Tags 03QO (`lemma-vanishing-etale-cohomology-strictly-henselian`), 03O3 / 03O4 (representable sheaves), 04FM (geometric stalks as points), 03Q1 (representable pullback), 03PU / 040S (conservativity); sites.tex Tag 00YA(2) (recovering a topos point's stalk colimit) and 00YV (algebraic structures and module pullback); and algebra.tex Tags 00D6 / 00D7 (filtered module representatives and equality). No SGA source is used.

1. Step 1 uses the **set-sheaf** statement of `lem-weil-pbc-sets-strictly-henselian-open-sections-stalk`, with T=U=A or S. The abelian-only variant would not justify the 2-morphism on set sheaves. Together with the inverse-image-mate convention of `def-trf-geometric-morphism`, this gives the natural closed-point counit. I checked the direction: the map from the constant closed fibre to F represents `Id => s epsilon`.
2. Step 2 uses exactly the universal property's triple (x epsilon, Id, b => s epsilon). The constant-module theorem `lem-pe-constant-left-module-inverse-image` supplies compatible units and composition, not merely a definition of module pullback. Thus applying p2 direct image to the unit produces the specified map, with p2 sigma equal to the identity.
3. Step 3 uses the **statement** of `lem-trf-oriented-product-universal` for p2 inverse image of a representable, actual subcanonicity on the B site, the sheafification adjunction, and the general Yoneda Hom-bijection. The calculation of sections is written out and is elementary from those statements. Triple representables are sheafified; I did not assume that the triple site is subcanonical.
4. Step 4 uses the universal inverse-image formula, representable-stalk bijection, subcanonicity and the representable pullback formula. The closed fibres of U and V extend to unique global sections because step 1 concerns all set sheaves. Their compatibility on A is established by injectivity of the A closed-point germ map, rather than asserted from equality at the point. The local hypothesis on a is used here.
5. Step 5 explicitly constructs W0 as a fibre product in the small etale site, whose finite limits are scheme fibre products. The matched stalk values give its chosen geometric lift. The three maps then form the required triple refinement. This is a routine finite-limit construction from step 4 and the two cited statements, not an uncited theorem of cofinality. No claim that a fibre product of strictly local schemes is local is made.
6. Step 6 uses `lem-trf-site-point-fibre` for the small cofiltered neighbourhood categories and the module stalk colimits; it uses the existing Mathlib leaf `lem-weil-pbc-filtered-colimit-modules-elementwise` for both representatives and eventual equality. The explicit refinement supplies surjectivity, then injectivity. A map between the final-first-two-component triples is just its B component, which is the needed verification for injectivity. This proves the underlying bijection by actual restrictions.
7. Step 7 uses the same universal inverse-image formula, the site-point theorem's explicit map on sections, and the geometric-morphism adjunction unit. Pulling a section back along sigma gives its restriction, so its evaluation at y is the triple-stalk germ. The constant-module theorem identifies the units with these underlying units. This checks the canonical map and its direction, not just an existence of some isomorphism.
8. Step 8 uses the statement of `lemma-openclosed-point-ulift`, which explicitly supplies a conservative geometric family at the coefficient universe, on B. The constant-module inverse-image theorem explicitly states exactness for any geometric morphism, so it applies to sigma (which is not a scheme map). Transport along the natural isomorphism then proves exactness. No definition node was cited as a substitute for that exactness theorem.

For B1--B9 and C1--C5 there are no new statement-only nodes to audit; all notions of the unchanged statement have definition dependencies, every used theorem is an existing citation, and every cited occurrence has a verbatim quotation. The elementary-labelled steps are explicit adjunction/Yoneda, finite-limit, or unit computations. For D1--D5 the main cofinality argument remains in the item's proof, with both representative and equality checks supplied. I checked cycles through the server checks rather than assuming off-unit tools were harmless. Every proof step is below 1000 characters, and none exceeds the human's 2000-character long-step review threshold.

For E1--E7 I checked compatible closed points, arbitrary B, constant coefficients, and the actual gamma defined by the unit. Small cases: if A=S is a separably closed point then the oriented product is B and the comparison is the identity; if B is empty its module category is zero and the conservative empty family still gives the claim; if Lambda is the zero ring everything is zero. Non-noetherian strictly local A and S require no change because the argument uses only locality and finite limits. A generic-point morphism to a nontrivial strictly local base does not satisfy the local hypothesis, so it is correctly excluded. The corrections made during this reading were to avoid an abelian-only locality lemma, use enough points on B rather than the printed S, retain sheafification on triple representables, and verify the specific unit-defined comparison.
