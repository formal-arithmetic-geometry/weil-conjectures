# Q130: lem-per-constructible-subset-closure-dimension

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-constructible-subset-closure-dimension.json`: statement, split into seven steps; no Mathlib match.
- `citations.json`: a verbatim statement quotation for every citation in every step.
- `report.md`: this report. `searches.jsonl` contains the search command's genuine logs.

New nodes: none. New Mathlib leaves: none.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact item tag, constructible/closure terminology and Krull-dimension/closure combinations found no declaration stating this item. The perverse smooth-pullback declarations in `SixFunctors/Etale/Perverse/Operations.lean:170` and following contain `sorry` and concern a larger statement. `AlgebraicGeometry.topologicalKrullDim_opens_eq` in `Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:140` is proved but concerns integral schemes and nonempty opens, not the constructible closure equality. The existing DAG already carries its open-dimension role.

## WANTED

None. Every source needed is available locally.

## Findings and changes

The mathematical statement is correct as written and retains every hypothesis and the empty-set convention. The only statement-text change replaces the umbrella reference `def-weil-scheme-morphism-properties` by `def-weil-finite-type-morphism`, which actually defines finite type. The corresponding statement dependency changes too; this has no mathematical effect. The previous node had no proof. I supplied the finite locally closed decomposition argument that its source note promises, without relocating its conclusion into a new lemma.

I read Algebra Tag 00OT, `lemma-dimension-at-a-point-finite-type-over-field`, especially the proof of (1)=(2), and Varieties Tag 0A21, `lemma-dimension-locally-algebraic`, (3) and its proof. The latter is the precise existing scheme-level result implementing 00OT's nonempty-open dimension calculation. The assembly from these statements is recorded as agent-written, since neither source states the constructible-set corollary verbatim. The ancestry remains the first paragraph of the current main-20261015 `lem-per-smooth-pullback-t-exact.proof.md`; this justifies the support/closure replacement used by its existing support-dimension child. The chapter and unit records were read; this item is not the unit's key node and no unit realization record is changed.

## Existing-node and Mathlib searches

I searched the whole DAG for 00OT, nonempty-open dimension, finite irreducible components, constructible dense opens and dimension/closure terminology, and used `tools/blueprint_refs.py ancestor` plus whole-blueprint searches for dimension/closure, constructible/dimension, nonempty opens, and irreducible components. No imported blueprint node states the item in another form, so `same_as` remains empty. The useful matches are the existing `lem-sc-dimension-locally-algebraic`, `lem-sc-noetherian-closed-subset-finite-components`, `lem-weil-pbc-reduced-induced-closed-subscheme`, and `lem-weil-pbc-finite-type-over-noetherian`; each is cited rather than duplicated. In particular no new open-dimension, finite closed-union dimension, or subspace-monotonicity node is needed: the first already exists, and the last two are short chain arguments written in the proof itself.

All fresh Mathlib searches used the mandated `msearch.py Q130 lem-per-constructible-subset-closure-dimension` command. Loogle (`"topologicalKrullDim", "closure"`) and the Krull-dimension/closure/constructible regex returned no hits. LeanFinder was run both for the constructible closure equality and for a second wording via finite locally closed strata. LeanSearch was run for the equality too. The hits provide definitions, subspace dimension monotonicity, spectrum/ring dimension comparison and constructibility facts, not the desired equality. I read the monotonicity declaration in Mathlib/Topology/KrullDimension.lean:63 and the source project's integral-open theorem; neither states the item. Existing search records were preserved and only genuinely run new queries appended. No service was unavailable.

## Tool uses

The split_report declares the following generic tools from other units: `lem-weil-pbc-finite-type-over-noetherian` for the Noetherian hypothesis of the finite-component theorem; `lem-weil-pbc-reduced-induced-closed-subscheme` for the closed-component scheme structure and its affine quotient charts; and `lem-sc-dimension-locally-algebraic` for dimension preservation on a nonempty open of an irreducible locally finite type scheme over a field. These are general geometric tools under the support-dimension argument. They replace no step of the perverse unit. The finite-component node is already a Mathlib leaf. No maintainer-owned `tool_uses` field was edited.

## Review by Q130

I reopened the item, all cited node statements, and the Stacks source text while checking the split. For the item I compared the finite-type-over-a-field and constructibility hypotheses with the 00OT open-dimension argument and 0A21(3). I did not generalize to arbitrary dense subsets or arbitrary Noetherian schemes. No new node needs its own source or hypothesis audit.

Step 1 uses exactly the finite locally closed decomposition explicitly stated in `def-weil-constructible-subset` and the empty-space convention of `def-kun-topological-krull-dimension`. Writing a piece as U intersect F, its closure lies in F, so its intersection with U recovers the piece. Finite unions of closed sets are closed, giving closure of S as the union of the piece closures. No assertion about dimensions of a general finite union of subsets is assumed.

Step 2 applies the actual statement of `lem-weil-pbc-finite-type-over-noetherian`: the base is Spec k, whose one-point affine topology and two ideals show it is Noetherian, and T is finite type by the item's hypothesis. I read Morphisms Tag 01T6, `lemma-finite-type-noetherian`. I then read `lem-sc-noetherian-closed-subset-finite-components`, which explicitly gives a covering, not just the finiteness of an unspecified family, for every closed subset of a Noetherian scheme. Each Z_a is closed in T, so its hypotheses hold. I read Properties Tag 0BA8 and Topology Tag 0052, including the closed-subspace and component arguments, to check the existing leaf's meaning.

Step 3 cites `def-weil-irreducible-components` for nonemptiness, maximality and the two-closed-set irreducibility condition. Induction on a finite family gives the finite-union version of that condition. Removing all other components therefore leaves a nonempty open of Z_a inside C_ab, exactly as in the proof of 0052(3). Its intersection with L_a is nonempty by the definition of closure. This establishes the often implicit but necessary hypothesis that U_a meets every component. The cited `def-kun-subspace-topology` gives all the open-subspace identifications. Nothing about affine intersections or generic points is assumed.

Step 4 uses clauses (1) and (2) of `lem-weil-pbc-reduced-induced-closed-subscheme`, which I read against Schemes Tag 01J3, `lemma-reduced-closed-subscheme`, including its construction. This node supplies the actual quotient charts Spec(A/I). The cited `def-weil-closed-immersion` explicitly gives a homeomorphism onto the closed image, so it supports the subspace identification instead of merely naming an immersion. The cited finite-type definition supplies a finite affine cover with finitely generated k-algebras; their quotient algebras have the images of those same finite generators. This verifies local finite type without hiding a separate permanence theorem. Irreducibility is already a property of C_ab; reducedness is not needed for the theorem used in the next step.

Step 5 cites only `lem-sc-dimension-locally-algebraic`. I checked its complete statement: k is a field; C_ab is an irreducible scheme; its structure morphism is locally of finite type; and V_ab is a nonempty open. Each is established in Steps 3 and 4. Its statement explicitly gives dim V_ab = dim C_ab and does not require k algebraically closed, separatedness, or smoothness. I use its statement, not an intermediate construction in its proof.

Step 6 proves subspace monotonicity from the chain definition rather than citing an undocumented fact. Intersecting the closures of the chain members with the original subspace recovers those members, which proves strictness. The written dense-set/two-closed-set argument proves irreducibility of their closures. This applies to arbitrary nested subspaces and therefore both S inside its closure and V_ab inside S. The only citations are the actual dimension and subspace definitions. This is an elementary short argument, not a new lemma moved out of the item.

Step 7 considers an arbitrary finite chain in the closure. Its top irreducible member lies in one member of the finite CLOSED cover by the C_ab, by the finite-union version of the cited irreducibility definition. All earlier members are then closed irreducible subsets of that same component and form the same chain there. This proves the reverse bound from the component bounds already established, and taking the defining supremum completes the equality. The statement of `def-kun-topological-krull-dimension` gives exactly this supremum. In particular I avoided the unjustified general claim that dimension of every finite union of arbitrary subspaces is the maximum of their dimensions.

For B1–B7, no new nodes are created; the statement is self-contained, uses actual definition nodes, and the JSON has single TeX escapes after decoding. For C1–C8, each non-elementary input is an opened existing statement, every use has a verbatim quotation in citations.json, and the off-unit tools are declared. For D1–D5, the steps contain the argument, with no restatement child, circular use, unproved induction, or omitted standard lemma. For E1–E7 I checked the hypotheses individually above. Small cases checked were S empty; a closed point of affine space; the nonempty principal open D(t) in A1; a locally closed piece on a reducible union of two affine lines; and nonreduced finite-type schemes (the subspace dimensions and reduced induced structures agree). Spec of a DVR with S the generic-point open has dimension 0 versus closure dimension 1, showing why the proof must not apply open-dimension invariance to an arbitrary Noetherian scheme. The generic singleton of A1 has dimension 0 and closure dimension 1 but is not constructible, showing why arbitrary subsets are excluded. No claim in the delivered statement needs correction. Every proof step is below 2000 characters, and the elementary chain arguments are fully written, so no long step hides a separate lemma. There was no prior returned delivery or second worker; this is the direct-delivery self-review authorized in the brief.

## Unfinished work

None in this one-level split. The delivery's server dry run and push are performed after this review.
