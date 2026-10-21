# Worker report: lem-sp-ordinary-horizontal-pasting-transport

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-ordinary-horizontal-pasting-transport.json`: existing statement node, now split into six explicit elementary component calculations. The statement is unchanged. No Mathlib match for the whole implication.
- `citations.json`: `[]`, because every proof step has `uses: []`. The proof uses hypotheses of the item, functoriality, naturality and inverse identities, rather than any external theorem.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The existing statement dependency `def-weil-pbc-adjunction-mate` is retained because the statement names its square notation; the proof never invokes its mate bijection or assumes adjunctions.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, `ordinary_horizontal_transport`, and horizontal transport/pasting terminology. The results concern particular base-change or QCoh constructions, not this arbitrary-category implication. The exact private calculation `ordinary_horizontal_transport` occurs at line 550 of `lean/Sheaf/AlgebraicGeometry/VaryingRingProperOpenPasting.lean`, with its proof at lines 582–607. I read its hypotheses and calculation. It is not a declaration under `WeilConjectures/`, as the attachment rule requires, so I do not submit an ATTACH claim. No Lean file was changed or compiled.

## WANTED

None. All sources used are present locally.

## Sources, route and searches

Read `GOAL.md`, the worker contract, the three blueprint levels in `SETUP.md`, the stage-1 document, and delivery-errors B–E. Read the smooth-purity chapter record, the complete `sk-prop-sp-tower-geometric` unit, and the current `main-20261015` gluing proof, especially Local pairs. This is a generic component calculation below the proper/open calculus used to compose chart counits; it replaces no step of the unit. No chapter or unit file is changed, and the item is not the key node of that unit.

Read Stacks Tag 0F7D in `more-etale.tex`, label `lemma-shriek-proper-and-open-compose-horizontal`, including its proof. The source identifies the outer proper/open arrow with the horizontal composite, using the shriek compositors. It is not a theorem about six arbitrary realization functors: the transport from that equation is the agent argument identified in the item's source. The delivered proof is therefore marked `proof_origin.by: agent`. It proves the abstract implication from its stated coherence hypotheses and does not apply a geometric theorem without geometric assumptions. No SGA source is used.

Searched the whole DAG for the item and ordinary transport/pasting terminology, and for `0F7D`. The neighboring vertical-transport node is about a different arrangement of compositors. The scheme-specific ordinary pasting nodes impose QCoh/base-change hypotheses and do not state this arbitrary-category comparison implication. Blueprint searches `horizontal.*transport`, `horizontal`, and `coherent comparison`, together with the ancestor command, found no equivalent imported blueprint statement. The item's ancestor remains `det-sp-tower-gluing` and its `same_as` is `[]`.

The item's four inherited Mathlib searches are preserved. Ran eight further searches using the required `msearch.py`, two phrasings each through LeanFinder, LeanSearch, Loogle and grep; all succeeded and their actual summary records are copied from `searches.jsonl` into `mathlib_searches`. Read the hits rather than treating a keyword match as the theorem. In particular, `CatCommSq.hComp` constructs a pasted invertible square, `TwoSquare.hComp` constructs a pasted arbitrary square, and `TwoSquare.hCompVCompHComp` states interchange for four given squares. None supplies the nine edge comparisons, two compositor compatibility hypotheses, and transport implication by a one-line specialization. The `NatIso` naturality/cancellation lemmas are elementary ingredients. The GuitartExact candidates assert preservation of exactness, and the monoidal-closed hit concerns an exponential comparison. These do not give this item's statement. Relevant source reads were CatCommSq lines 38–110, TwoSquare lines 47–166, NatIso lines 51–170, and the grep-hit passages of GuitartExact/HorizontalComposition, GuitartExact/VerticalComposition and Monoidal/Closed/Functor.

## What was wrong, and what changed

The imported item had no proof. Its delicate content is the placement of the realizations and comparison components in the horizontal equation. I supplied every intervening equation instead of saying that pasting transports. No statement dispute or hypothesis correction was needed. In particular, the conclusion only concerns the images under `E_E`; faithfulness is neither assumed nor used. The proof cancels a comparison morphism in `E'` and never reflects equality through a functor.

The statement of `def-weil-pbc-adjunction-mate` was opened: it defines mates under adjunctions, with an explicit natural-transformation square as its input. Only that notation is referenced by the item's statement. Its bijection is not a theorem required here, so it is not cited in a proof step and no quote is attributed to it in `citations.json`.

## Not duplicates

No new node is proposed. The many existing `0F7D` citations concern the geometric horizontal-pasting identity or applications of it. They are context rather than new dependencies for this conditional categorical identity.

## Review by Q23

I checked the unchanged statement against the local Stacks passage, the current gluing unit, and the actual private horizontal transport calculation. The distinction matters: Stacks proves the geometric primed equality, whereas this item assumes that equality and only compares its two images. Every functor endpoint in the statement is sufficient for the calculations below; no properness, smallness, exactness, equivalence, or adjunction is smuggled into them.

Step 1 introduces a fixed object `N` and writes all five comparison products explicitly. I checked their endpoints: `s` starts at `E_E(QJIN)`, and `t` ends at `K'_{12}R'(E_C N)`. The two triple parenthesizations expand to the same three factors. Functor associators have identity components, so there is no unproved coherence theorem behind the notation. This is direct evaluation of the given definition, with no cited node.

Step 2 uses naturality of the given `e_Q` at `(c_I)_N`, the stated compositor equation for `c_I`, and the respected-cell hypothesis for `c`. Each substitution is displayed, producing the primed left path followed by exactly `s`. In particular the compositor equation is evaluated at `N`, and the outer cell at that same object. No separate compatibility of whiskering is asserted without proof.

Step 3 uses precisely the stated compositor equation for `c_K` at `RN`, followed by naturality of the supplied `c'_K` at `e_R(N)`. Its intermediate object is `E_A(RN)`, not `R'(E_C N)` until that naturality equation is used. The resulting source comparison is exactly `v` from Step 1. This catches the common misplaced-comparison error.

Step 4 uses naturality of `e_L` at `a_N` and the respected-cell equation for `a`. I expanded that equation in the text before applying `L'`, so it gives all three required factors and yields `L'(a'_{E_C N})` followed by `w`. Only preservation of composition is used in moving these factors through `L'`.

Step 5 uses the respected-cell equation for `b` at `IN`, then naturality of `b'` at `e_I(N)`. This changes `b'_{E_D(IN)}` into `b'_{I'(E_C N)}` and produces `s`. The components of `a`, `b`, and `c` need not be invertible in any step.

Step 6 substitutes the preceding three equalities into the right path and uses the given primed pasting equality at `E_C N`. Step 2 then identifies it with the left path after the common postcomposition by `t`. I wrote an explicit inverse of `t`; its two inverse identities follow by applying the functor to the inverse identities and reassociating. Cancelling this actual isomorphism proves the desired image equality. It does not use a faithful functor or a conservativity assertion.

Every step is elementary because the displayed calculations consist of the defining naturality equation, an explicitly supplied hypothesis, functoriality, associativity, or the inverse identity. There are no non-elementary facts requiring a node and no hidden lemma moved into a new node. All steps are below 2000 characters. Thus the empty proof-dependency union and the empty citations list accurately describe the proof, rather than omit a source theorem. The existing definition node is a statement dependency only, as explained above.

For edge cases, checked the empty category `C` (the conclusion has no objects to test), all identity functors/comparisons (the formulas reduce to the assumed equation), and arbitrary noninvertible cells (the calculation inverts only comparisons). Also checked nonfaithful realization, in particular realization into terminal primed categories, where the conclusion is correctly just equality of images. No strengthening to equality in `E` occurs. B1–B10 impose no new-node obligations because none was created; the retained item is self-contained and searched. C1–C4 and D1–D5 are addressed by the explicit six calculations, not by referring to the proof of another node. The checks of E1–E7 required no correction of the statement. The only repair was replacing an empty proof with those calculations.

## Unfinished work

None in this stage-1 split. Maintainer independent review remains the delivery protocol's next step.
