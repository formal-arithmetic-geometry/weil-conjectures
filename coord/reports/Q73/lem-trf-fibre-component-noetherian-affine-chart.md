# Stage-1 report: lem-trf-fibre-component-noetherian-affine-chart

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fibre-component-noetherian-affine-chart.json`: item, split into four steps, statement unchanged; not an exact Mathlib leaf.
- `citations.json`: thirteen entries, one for every node citation in every proof step, copied verbatim from the live node statements.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The existing Mathlib leaves are reused.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for fibre/component/affine, Noetherian, generic-point and minimal-prime terminology. The project has related arguments under stronger hypotheses (for example the flat power-series chart generic-image theorem), but no declaration giving every clause of this item under its hypotheses. Mathlib's `IsAffineOpen.primeIdealOf_genericPoint` assumes an integral scheme; the fibre here need not even be reduced.

## WANTED

None. All the literature needed is available locally.

## Findings and changes

The imported item was unsplit and had no proof. Its mathematical statement is correct and has not changed. I added the four-step proof: the field base is locally Noetherian; base change and the existing finite-type theorem give local Noetherianity of the fibre; its defining affine cover gives the Noetherian chart; the affine closure formula and component maximality give minimality. No component-generic-point lemma was created, since the necessary argument is written out from the cited closure formula and definitions.

Read the current blueprint `main-20261015` unit `sk-i-curve-zero`, chapter record, and ancestor `lem-trf-local-term-locality.proof.md`, especially (1)--(2), the normal-cone specialization branch. This subordinate fibre-chart input remains in its inherited ancestry, without changing the chapter or unit route. The unit record is not this item's statement and was not edited.

Searched the whole DAG by tags 01T4, 01T6, 00ES, Noetherian affine charts, minimal primes, and the relevant titles; read the actual matching node statements. Blueprint searches for `minimal prime`, `Noetherian affine`, `finite type over`, `Noetherian affine minimal`, and `fibre component` found no blueprint restatement of this item. The existing generic commutative-algebra and geometry leaves suffice. Their use is permitted across units because they are Mathlib leaves.

All six searches made here were issued through msearch.py and are preserved verbatim in searches.jsonl and the item's mathlib_searches, in addition to its genuine inherited searches. LeanFinder was tried with both the full fibre statement and the component-generic-point phrasing. Read the returned finite-type and Noetherian chart declarations in Mathlib/AlgebraicGeometry/Noetherian.lean, notably lines 57--59, 239--264, and the integral-only candidate in FunctionField.lean:132--142. LeanSearch and Loogle were available. The first grep had no hits; the second returned Noetherian class documentation/fields, not a declaration of the whole item. None removes the elementary maximality argument for arbitrary components, so the item is split rather than declared a leaf.

## Unfinished work

None in the assigned one-level split. No new statement-only nodes are necessary. No Lean files, compilers, Lake commands, repository writes, or repository git commands were used.

## Not duplicates

No new nodes were created. Reused `lem-weil-pbc-lft-base-change`, `pqf-lem-locnoeth-lft`, and `lem-weil-pbc-spec-irreducible-closed-subsets-primes`; did not duplicate their tags or package an item clause as a new lemma. The existing component/minimal-prime correspondence node was also read, but is unnecessary for the direct proof.

## Review by Q73

I read the actual Stacks text in morphisms.tex at labels lemma-base-change-finite-type (01T4) and lemma-finite-type-noetherian (01T6), properties.tex at definition-noetherian (01OV) and lemma-locally-Noetherian (01OW), algebra.tex at lemma-irreducible (00ES), and topology.tex at definition-irreducible-components (004V), lemma-irreducible (004W), and definition-generic-point (004X). The numerical tags were checked against tags/tags. There are no new-node sources to audit.

Step 1 cites the fibre definition for the actual residue field, the affine-spectrum definition for its section ring, the Noetherian-ring definition for finite generation of ideals, and the locally Noetherian definition for the one-member affine cover. Each of those claims appears in the cited statement. The proof that a field's ideals are zero or the whole ring is explicit; it needs no Hilbert basis theorem or additional node.

Step 2 cites the fibre definition, whose statement actually supplies the fibre product and second projection, and the two existing statements 01T4 and 01T6. I checked that 01T4 allows an arbitrary base-change morphism and that 01T6 only needs a locally Noetherian target and a locally finite type projection. The target is Spec(kappa(t)), from step 1; the argument never assumes S is locally Noetherian or that f is globally finite type.

Step 3 cites pqf-def-locnoeth, whose statement provides precisely an affine cover with Noetherian section rings, and the scheme and affine-spectrum definitions. Choosing a member containing y is an instance of the cover. To make the coordinate identification explicit rather than silently identifying two rings, the step names an initial affine coordinate ring B, identifies its global sections with B, and applies Spec to the resulting ring isomorphism. These operations are contained in the cited affine-spectrum convention. It does not assume intersections of affine opens are affine.

Step 4 uses exactly the affine spectrum closure formula in the statement of lem-weil-pbc-spec-irreducible-closed-subsets-primes, genericity as closure equality from def-sc-generic-point, and maximality from def-weil-irreducible-components. The prime inclusion is used in the correct direction: q contained in p_y gives y in closure{z}. That closure is irreducible by the closed-cover argument written in the step; it contains C and therefore equals C. Restricting closure to U then puts z in closure{y}, which gives the reverse prime inclusion. I checked every fact taken from the cited node against its statement, rather than its proof. The subspace closure identity and the singleton-closure irreducibility argument are both explicitly written, so no extra topological lemma is hidden. This step is marked non-elementary because it uses the substantive cited affine closure theorem; it is under 1000 characters and introduces no independent comparison lemma.

For the B--E delivery checklist: all objects and notions in the unchanged statement already have their definition dependencies; the JSON uses single TeX escapes after decoding; every non-elementary input is a cited existing node, and citations.json contains actual statement text. The proof does not simply apply a restatement of the item, introduces no new cycle, and cites no node depending on this item. The elementary steps are cover selection, field ideals, and the stated affine-spectrum conventions. No source error or disputed statement was found.

I tested the empty fibre (there is then no C or y, so the component hypothesis is vacuous), a nonreduced one-point fibre Spec(k[epsilon]/epsilon^2) (the generic prime is (epsilon), not zero), a reducible fibre Spec(k[x,y]/(xy)) (either component gives its own minimal prime), a disjoint union of infinitely many finite-type affine schemes (only local Noetherianity is asserted), and a morphism over a non-Noetherian base (only the residue-field base enters 01T6). None requires integrality, reducedness, flatness, global quasi-compactness, or finiteness of the set of components. I corrected the potential integral-only shortcut by using maximality and the full affine closure formula instead.
