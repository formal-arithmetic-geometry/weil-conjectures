# Stage-1 report: lem-sfb-affine-group-homomorphism-image

## Files written
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-group-homomorphism-image.json: split, three proof steps, unchanged statement.
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-group-faithfully-flat-image-factorization.json: statement, unsplit; no Mathlib match after LeanFinder (two formulations), Loogle, LeanSearch and source grep.
- citations.json: seven step/node citations with exact statement quotations.

## Attachments
None for the item. The project has closed-image theorems and a rational-point lifting theorem, but none supplies faithful flatness of an arbitrary homomorphism onto a smooth affine target. No Lean code was written or compiled.

## WANTED
None. All proof sources used are present locally.

## Findings and changes
The original node had no proof. Its statement agrees with the algebraically closed, affine case of Milne Proposition 5.47, printed p.110. I kept the statement and its hypotheses. The reverse direction must use smoothness to eliminate a possibly nonzero defining ideal: equality of underlying point sets alone is insufficient. I expanded this into vanishing of every element of the ideal using the existing Nullstellensatz node. The image factorization is Theorem 3.34, printed p.75, the affine case of the node's original reference to 5.39. This exposes a proper structural input rather than copying either implication of the rational-point criterion into a child.

The new node is deliberately statement-only. Its future proof is given by Milne 3.34: the coordinate homomorphism factors through its Hopf-algebra image (Proposition 3.14), and the inclusion of that finitely generated Hopf algebra is faithfully flat by Theorem 3.31. Those details belong to the future split of that node, not an unrecorded argument in this item.

The live blueprint ancestor command returns null, as already recorded by the item; I retained that value and extended its precise inherited place/via chain. I read the current latest blueprint's sk-thm-sf-ctf-stability unit and its direct-image proof, as well as the DAG unit and chapter. The current direct-image paragraph (3) has evolved from the alteration argument in the inherited provenance; this delivery supplies the already-assigned algebraic-group prerequisite without changing the unit or its route.

## Not duplicates
lem-sfb-affine-group-faithfully-flat-image-factorization vs lem-ag-homomorphism-image-closed: the existing node is about reduced matrix groups over algebraically closed characteristic-zero coefficients and the closed set of rational points; the new node is over any field, allows nonreduced group schemes, and gives faithful flatness onto a scheme-theoretic closed subgroup.
lem-sfb-affine-group-faithfully-flat-image-factorization vs lem-sc-image-subgroup: the existing node assumes the source proper and gives surjectivity onto its image; the new node assumes affine finite-type groups, with no properness, and gives a faithfully flat homomorphism.
lem-sfb-affine-group-faithfully-flat-image-factorization vs lem-sfb-affine-group-homomorphism-image: the item is a rational-point criterion with smooth target over an algebraically closed field; the child gives a structural factorization over any field with no smoothness assumption and contains no rational-point criterion.
No other node has the same Milne theorem as a statement. Whole-DAG statement/title searches and blueprint_refs searches for homomorphism, Hopf, affine group, homomorphism image, faithfully flat and Nullstellensatz were read; existing definitions and the Nullstellensatz result were reused. No new Stacks-tag node was created.

## Review by Q56
I read Milne Proposition 5.47 on printed p.110 and Theorem 3.34 on printed p.75, including its proof and its explicit use of 3.14 and 3.31. These apply to finite-type affine group schemes and do not impose reducedness, smoothness or connectedness. This is essential because H1 is not assumed smooth. I also read Stacks algebra.tex Tag 00HQ (lemma-ff-rings), Tag 00FV (theorem-nullstellensatz), varieties.tex Tag 056T (lemma-smooth-geometrically-normal), and the statements of every DAG node cited.

Step 1 uses precisely spectrum-surjectivity from lem-weil-pbc-faithfully-flat-surjective-spectrum. A maximal ideal above the supplied prime still contracts to the fixed maximal ideal; properness of contraction follows from a unital homomorphism. Clause (1) of lem-wf-affine-nullstellensatz-vanishing supplies B/n=F because B is finite type and F algebraically closed. The two resulting maps out of A agree since they factor as F-algebra maps through A/m=F. This verifies equality of rational morphisms, not merely of their underlying points. Choosing a maximal ideal containing a proper prime is ordinary elementary ideal theory.

Step 2 uses exactly the new node's factorization with q faithfully flat and j a closed immersion. def-weil-closed-immersion explicitly gives the quotient-algebra description over the affine target, so I=Spec(A/J). Surjectivity of f(F), not a lifting property of q, gives a lift of every y through j and annihilation of J. I have not used the proof or a stronger conclusion of any cited node.

Step 3 uses the exact assertion of sbc-lem-smooth-geometrically-reduced for H2 -> Spec F: the unique fibre is H2. The reduced-scheme definition explicitly identifies reducedness of local rings with reducedness of sections over every open, so A is reduced. Clause (2) of the Nullstellensatz node now applies to every element of J; no assertion about a nonreduced closed subgroup having a reduced ideal was assumed. J=0 makes the quotient map an isomorphism, and extension of scalars along that isomorphism identifies the tensor functors for f and q, preserving exactness and detection of zero modules.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the written nodes: self-contained statements and definition dependencies, single-escaped TeX, exact sources, actual recorded searches, no restated clause, no circular inference, no uncited scheme-theoretic comparison. The only new unsplit node has no proof or proof dependencies. Each cited statement was opened and copied verbatim into citations.json; the two generic off-unit inputs are declared in split_report.tool_uses. Each step is under 2000 characters and contains one routine argument, with no hidden comparison lemma.

Small cases: trivial groups, finite constant groups, disconnected groups, positive-characteristic Frobenius on Ga, and a nonreduced source such as alpha_p mapping to the trivial group all agree. The omitted smooth-target assumption would be false: the unit inclusion 1 -> alpha_p over an algebraically closed field of characteristic p is surjective on rational points but F[t]/(t^p) -> F is not flat. Thus the proof uses exactly the hypothesis needed. Image factorization also works for that inclusion by taking I=1, and for Frobenius by taking I=Ga; no finite or etale kernel hypothesis entered. No assertion was changed and no source dispute was found.

## Unfinished
No work remains in this item's assembly proof. The new structural factorization node remains unsplit by the one-level rule.
