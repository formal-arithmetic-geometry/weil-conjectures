# Stage 1 worker report

## Files written

- `dag/nodes/sec-proper-base-change/thm-weil-pbc-weak-etale-refinement.json`: split item.
- Existing node `lem-weil-pbc-faithfully-flat-base-change`: Mathlib leaf, exact match; reused without modifying its file.

## Attachments

None. I searched the project source for the blueprint tag and for weakly etale refinement declarations; no sorry-free declaration states this item.

## WANTED

None.

## What was checked and changed

The imported item follows the three proof paragraphs of the master blueprint and its Stacks context (Tag 097Z). I retained the item statement and all existing dependencies. The first paragraph uses the explicit construction node for `D_0` and `B'`, the strict w-cover properties, the field calculation for algebraic residue extensions, and the retained-localization properties. The second paragraph uses the existing stability, strict-local, and local-rings-to-ind-Zariski statements. The third paragraph uses the strict-cover surjectivity and the existing Mathlib leaf for faithful flatness under base change. I changed the item from `imported` to `split`, filled its blueprint search result, and made that existing base-change dependency explicit.

## Review by NH

I read the item source `literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/thm-weil-pbc-weak-etale-refinement.md` and opened every cited node. Step 1's construction quote is exactly the definition's displayed tensor/localization construction; the strict-cover node supplies faithful flatness, ind-etaleness, w-locality, strict henselian maximal local rings, and closed-point surjectivity; the field node supplies algebraic/separable residue fields; and retained localization supplies w-locality and the retained closed points. Step 2's weak-etale stability node states base-change/composition stability, the strict-local theorem states that the local weakly etale map is an isomorphism, and the local-rings node states precisely that local-ring identifications into a w-local target imply ind-Zariski. Step 3 uses the strict-cover node's closed-point surjectivity and the new Mathlib declaration `RingHom.FaithfullyFlat.isStableUnderBaseChange`, whose statement is quoted verbatim in `citations.json`, to justify faithful-flatness after tensor base change. I checked that each step's hypotheses match the cited statements: `C/A` comes from the strict cover, `D_0=B⊗_A C` is its ring base change, `B'` is the retained localization along `V(JD_0)`, maximal points of `B'` correspond to retained closed points, and the final composition maps are the displayed algebra structures. I tested the construction in the zero-ring and identity cases conceptually; no edge-case contradiction or source error appeared. The only missing non-elementary fact was faithful-flat base change; I found and reused the existing Mathlib leaf rather than leaving it implicit.

## Not duplicates

lem-weil-pbc-faithfully-flat-base-change vs lem-weil-pbc-flat-morphism-base-change: the existing node concerns flatness of scheme morphisms under base change, while the cited existing leaf concerns faithful flatness of commutative-ring homomorphisms.

## Second reading by NH

I reread the item against the blueprint node at order 1232 and the Stacks
Project index entry for Tag 097Z (proetale-proposition-weakly-etale). The
statement preserves all three clauses: the displayed retained-localization
construction is the one from the definition, and the conclusions are faithful
flatness plus ind-etaleness of $B\to B'$ and ind-etaleness of $A\to B'$. The
zero-ring and identity-map cases introduce no extra hypothesis or missing
conclusion.

Step 1 was checked against the definition node, the strict w-cover statement,
the weakly-etale field statement, and retained localization. I verified that
$D_0=B\otimes_A C$, $K=JD_0$, and $T=V(K)$ are the stated objects, and that
the closed-point and local-ring conclusions are the cited ones. I added the
existing ind-etale-stability node to this step because its base-change clause
is needed to apply the field calculation to the fibers of $D_0/C$; this was
an omitted citation, not a new mathematical assertion.

Step 2 was checked against ind-etale stability, the strict-local isomorphism
theorem, and the local-rings-to-ind-Zariski lemma. The contractions of maximal
ideals, localization of the local isomorphism, and composition with $A\to C$
use exactly the hypotheses in force; the maximal-ideal and further-localization
facts are elementary commutative algebra.

Step 3 was checked against strict w-cover and the existing Mathlib leaf
`RingHom.FaithfullyFlat.isStableUnderBaseChange`, whose declaration and source
lines are recorded in `citations.json`. Base change gives surjectivity onto
$\operatorname{Spec}B$, and the retained localization keeps precisely those
closed points. The ind-etale composition and flatness follow from the cited
definitions and retained-localization statement.

There are no new nodes in this delivery. The existing faithful-flat base-change
node was checked as a Mathlib leaf, and no duplicate or elementary node was
created. As required for an imported blueprint item, its `blueprint.from` field
remains null; the three proof paragraphs are recorded in the imported source
and checked above. No statement correction or source error was found.
