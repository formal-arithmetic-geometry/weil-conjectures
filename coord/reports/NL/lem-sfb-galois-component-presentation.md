# Stage-1 delivery: lem-sfb-galois-component-presentation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-galois-component-presentation.json: item, statement; split into ten proof steps. No change to its statement or statement dependencies. Existing metadata and previous searches retained.
- citations.json: one entry for every proof-step citation, quoting the cited node's statement verbatim, including its hypotheses.
- report.md: this report. searches.jsonl contains the actual searches run with msearch.py; write_split.py is sandbox-only preparation material, not a DAG delivery file.

New nodes: 0. New Mathlib leaves: 0. All thirty distinct proof dependencies already exist.

## Attachments

None for the item. Searched the live lean/WeilConjectures source for its blueprint tag, its notion, Galois component terminology and geometrically integral components. No project declaration supplies the complete statement. The existing flat Cartier-pullback node records AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.comap_of_flat; its live source, lines 76 onward in WeilConjectures/Mathlib/AlgebraicGeometry/IdealSheaf/Invertible.lean, was read. That supplies only the boundary input and is not an attachment of this item.

## WANTED

None. The ILO PDF and Stacks sources needed here are already in literature/.

## Findings and changes

The imported item is true as stated. Its source is ILO, Expose X, proof 2.3 Step 2, printed page 150 (PDF page 156): choose a finite Galois extension splitting the components, take a component and its decomposition subgroup, and use the transitive contracted component presentation. I read the full paragraph in the PDF, as well as the preceding reduction to normal geometrically reduced schemes. No SGA source is used. I read the current main-20261015 unit and direct-image proof paragraph (3), together with the recorded DAG unit and chapter; this is a generic geometric prerequisite beneath that paragraph's alteration route, not a replacement of a unit-level proof.

The split spells out the source's implicit geometric arguments rather than creating a node for each conclusion. The finite separable splitting input already exists as lem-sbc-generic-components-split, the Galois envelope as lem-weil-pbc-finite-galois-receiving-separable-extensions, and the normal-component input as lem-fin-etale-normal-components. The Cartier input already exists as lem-pc-flat-pullback-effective-cartier-ideal. No new lemma is needed.

Mathlib searches used leanfinder twice with different formulations, loogle, leansearch and the prescribed grep. The successful services returned geometric-reducedness definitions, normalization, geometric-irreducibility definitions and abstract Galois-category transitivity. Reading their returned signatures and Mathlib/AlgebraicGeometry/Geometrically/Integral.lean (especially the reduction to geometric irreducibility plus geometric reducedness) rules out an exact or one-line match for the full component presentation. All queries and results were recorded honestly; the original item searches were preserved as well.

The blueprint search for Galois component, geometrically integral, components, normal closure, 054R and 0551 gives no duplicate of the entire item. The ancestor command reports None for the inherited creation chain. The item's existing blueprint.from.node is therefore retained as null, and its explicit place and via chain are retained. The split_report identifies the intended direct-image paragraph and the ILO paragraph precisely. No unit realization record is modified: this item is not its unit's key statement.

## Not duplicates

No new nodes are proposed. Existing field, component, finiteness, properness and Cartier lemmas are cited directly. In particular, the general 054R splitting theorem and the 033C normal-component consequence are not recreated under new names.

## Review by NL

I checked the split against delivery-errors B through E, with the item, the statements of all cited nodes, the source PDF and Stacks sources open. The statement introduces its field, scheme and divisor; it defines normality and geometric integrality explicitly. The existing definition node def-pc-geometrically-irreducible actually defines geometric reducedness and geometric integrality as well as geometric irreducibility, so using it for those notions is correct. There are no unsplit new statements, no invented Mathlib matches, no new definition with hidden data, and no relabelled clause posing as a split.

Step 1 uses the finite-type base-change clause of lem-sfb-finite-type-composition-base-change and the exact Noetherian-base conclusion of lem-weil-pbc-finite-type-over-noetherian. Fields satisfy the base hypothesis because their ideals are zero or the unit ideal. It applies to any extension field, which covers both L and e_0 later. This agrees with Stacks morphisms.tex Tags 01T4 and 01T6.

Step 2 uses exactly the conclusion of lem-sbc-generic-components-split: finite etale L/e and geometrically irreducible full inverse images of components. The residue-field separability lemma applies at the unique point of Spec L. The finite-Galois-receiving lemma takes a finite family of finite separable extensions, so its one-member case receives L and produces e_0. I read varieties.tex Tag 054R, more-morphisms.tex Tag 0551 and fields.tex Tags 09DT and 0EXM; the latter two give the normal closure and its Galois property. No separability is inferred merely from normality or from geometric reducedness.

Step 3 cites the finite-spectrum-map lemma, the finite-separable-etale lemma, field-spectrum surjectivity, finite base change and etale-cover base change, exactly as their statements assert. The one-element covering hypothesis is satisfied. The statement of lem-fin-etale-normal-components requires W Noetherian and Y normal integral; these are step 1 and the item hypotheses, respectively, with W=B_L or B_e0 and Y=B. I read the node and algebra.tex Tag 033C. The cited node explicitly supplies a finite disjoint clopen normal integral decomposition; I do not extract additional facts from its proof or from its Lean attachment.

Step 4 retains the intermediate L-structure, so every extension of e_0 is an extension of L. Hence the full inverse images supplied by the splitting node stay irreducible and nonempty. They are reduced because they are open subschemes of B_E, which is reduced by the original geometric-reducedness hypothesis. The integral-scheme definition explicitly equates nonempty reduced irreducible with integral. The clopen disjoint covering identifies these inverse images with the components, with the maximality argument written out. Proper base change and closed-immersion properness supply precisely the two properness assertions used; the closed immersion is the inclusion of a clopen subscheme with its restricted scheme structure.

Step 5 is a fibre-product construction. The inverse in Spec(a^{-1}) fixes the left-action convention. The cited fibre-product definition explicitly includes functoriality and uniqueness, which yield the action law and invariance over B. No quotient-existence theorem is assumed.

Step 6 uses open-immersion etaleness and composition of covering families with the full component cover, not with a single component prematurely assumed surjective. The inclusions are also closed immersions, so the closed-immersion finite lemma and finite composition apply. The finite-proper node supplies properness; the properness definition supplies closed image; the etale-open-map node supplies open image. The integral definition gives irreducibility of B. Thus every nonempty component has all of B as its image. This explicitly proves surjectivity before it is needed in the orbit argument.

Step 7 uses the exact algebra isomorphism in clause (1) of lem-exc-finite-galois-tensor-decomposition, not the sheaf clause or an abstract full-faithfulness assertion. The algebraic-extension embedding lemma applies because e_0/e is finite. The affine fibre-product lemma identifies the actual geometric fibre ring with Omega tensor_e e_0. The displayed coordinate map comes from extending the tensor decomposition along e_0 -> Omega. Finite-product extension of scalars is checked by its coordinate idempotents, and primes of a finite product of fields select one coordinate. Thus the fibre points include their residue embeddings and are simply transitively permuted by A. I read pione.tex Tag 03SF for the Galois-cover interpretation. I did not substitute transitivity of ordinary prime points for transitivity on geometric fibre points.

Step 8 applies the surjective-base-change node only after step 6. A nonempty clopen part of the split Omega-fibre has an Omega-point by step 7's explicit product description. For components X_i and X_j, moving chosen points over the same geometric base point makes aX_i intersect X_j, which forces equality by disjointness. For two points of X's fibre, the same calculation forces the moving element into H. These are short set and component arguments from previous steps, so no standalone orbit lemma is created. The arbitrary geometric base point gives every fibre, rather than merely the generic fibre.

Step 9 proves faithfulness explicitly on a residue field using nonemptiness of X and injectivity of a field homomorphism. Faithfulness on e_0 is built into H being a subgroup of Aut_e(e_0). Semilinearity was constructed in step 5. No implicit assumption that a semilinear action is linear over e_0 is made.

Step 10 uses the actual flatness clause of the etale definition. The flat Cartier-pullback node states precisely that the inverse-image divisor has a locally principal nonzerodivisor ideal. I read divisors.tex Tag 02OO, case (6), and its affine proof. The formula for the inverse-image ideal and uh=u show equality of pulled-back ideals, which proves stability of the divisor itself, not only of its support. The local equation also gives the support assertion.

For small cases I tested B=Spec e, a normal proper geometrically integral variety over e, and B=Spec K for a nontrivial finite separable K/e. In the first two cases e_0=e and H=1 can occur, and u is the identity; enlarging e_0 instead gives the expected field torsor. In the last case a component is Spec e_0 and its stabilizer is the subgroup fixing the embedding of K; its geometric fibres have the expected nonempty H-orbit. Imperfect e is allowed: geometric reducedness is used exactly to keep all extended components reduced, without asserting arbitrary field extension preserves normality. Empty Cartier divisors and zero-dimensional B are allowed. Empty B is excluded by the item and is used nowhere inadvertently.

All non-elementary facts used by the steps are cited as existing nodes, with quotations in citations.json. The short group, local-ring restriction and tensor-coordinate calculations are written in the steps. Every step has fewer than 2000 characters. I checked dependency reachability for each proposed edge; none reaches back to the item. Off-unit generic tools are declared in split_report.tool_uses. No statement dispute or source error was found. The strengthened intermediate simply-transitive calculation is used only to prove the item's requested single-orbit property; no freeness hypothesis was added.

## Unfinished work

None within stage 1. No Lean file was written, no compiler or build tool was run, and no repository or launcher file was modified. Delivery validation is performed by the required server-side dry run.
