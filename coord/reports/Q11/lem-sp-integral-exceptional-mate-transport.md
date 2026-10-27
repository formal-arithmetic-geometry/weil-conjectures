# Stage-1 worker report

Item: lem-sp-integral-exceptional-mate-transport. Group: Q11. Date: 2026-10-22.

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-integral-exceptional-mate-transport.json`: statement, split; eight proof steps; Mathlib verdict: no match for the geometric integral/actual-tower assertion.
- `citations.json`: 24 verbatim statement extracts, one for each step/node citation.
- `report.md`: this report.

No new nodes, no new Mathlib leaves, no unit record changes. The sandbox also contains the logged searches and the item-specific writing script. All repository and launcher files were read-only.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the exact item id and for exceptional mate, transport and normalized tower notions. The source contains general mate calculus and normalized tower results, but no declaration stating all clauses of this item. In particular `IntegralCoefficients.lean`'s integral exceptional-adjoint assertion contains `sorry` and is not an attachment. Generic adjunction uniqueness is already the existing Mathlib leaf `det-sp-unique-right-adjoint`; it is reused, not recreated.

## WANTED

None. The item's current blueprint proof and all cited node statements are available locally. The explicit categorical calculation is my argument, recorded with `proof_origin.by = agent`.

## What required attention

The item was unsplit with an empty proof. Its statement is retained verbatim, with its full statement-dependency list. There is no statement dispute and no change to the target statements. The source's phrase that the integral transpose is the limit of the transposes does not by itself display the comparison maps. I supplied those maps and the calculation, rather than treating level evaluation as faithful. Nothing in this proof deduces equality of derived-tower maps merely from equality of their evaluations.

The compactification exchange in the statement is fixed as an actual natural isomorphism. The proof establishes its unique lift through the normalized-tower equivalence; it does not assert agreement with an additional, independently defined integral exchange. Its direction is from pulled-back compact support to compact support of the pullback, so the transpose equation uses its inverse.

## Not duplicates

No new nodes were created. Blueprint-wide searches for the integral adjunction normalization and normalized equivalence found no second blueprint statement of this item. I reused the normalized equivalence, integral Hom bijection, integral direct-image comparison, pullback reconstruction, tower adjunction, preservation result and right-adjoint uniqueness already in the DAG. Thus no generic full-faithfulness, reconstruction or uniqueness fact was duplicated as a new node.

## Review by Q11

I read the current source `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-tower.proof.md`, especially (3), and the chapter and unit records. The unit route is the tower counit calculation followed by normalized reconstruction. I also read the source proof `sk-prop-sp-integral-adjunction/sk-prop-sp-integral-adjunction-bijection.proof.md`: its middle paragraph explicitly constructs the Hom bijection by reduction, the tower adjunction, and reconstruction. This is the input needed for the entire-tower counit identity. No SGA source is used. There are no new-node sources to check.

For Step 1 I opened `lem-sbc-smooth-relative-dimension-permanence`: clause (1) allows arbitrary base change and keeps relative dimension, including empty schemes. I checked its Stacks source at Tags 01VB (`morphisms-lemma-base-change-smooth`) and 02NK (`morphisms-lemma-base-change-relative-dimension-d`), including the latter's locally finite type hypothesis, satisfied by smoothness. `def-cbc-compact-support-square` actually includes the statement that the pulled-back factorization is a compactification. The pullback-reconstruction node states Noetherianity in this standing scheme setting. This checks the extra Noetherian hypothesis of `det-sp-normalized-equivalence`, which is not an equivalence assertion over arbitrary schemes without that condition. The characteristic and prime hypotheses match throughout.

For Step 2 I read the full statements of `prop-coef-integral-exceptional-adjoint`, `det-sp-integral-adjunction-bijection`, `det-sp-integral-direct-image-tower` and `det-sp-unique-right-adjoint`. The first supplies J as a right adjoint to integral compact supports on the specified constructible categories, the second supplies H and its full-tower Hom bijection for the separately derived compactification functor, and the third compares that same left functor to the entire tower functor. Consequently uniqueness applies to the same left functor, not to merely isomorphic unnamed functors with unspecified counits. The uniqueness leaf states naturality, invertibility and counit preservation. I also read Mathlib `CategoryTheory/Adjunction/Unique.lean` at lines 102-140: the right-adjoint isomorphism, its transpose, counit and inverse formulas match that leaf. The definition of q is reduction of delta followed by the reconstruction counit. Substituting this in the transported Hom bijection gives the entire-tower counit identity, so finite-level agreement alone is not used as evidence for equality.

For Step 3 I checked `lem-sp-ctf-tower-pullback-reconstruction` in full: it supplies both the normalized preservation assertion and the specified natural alpha as the equivalence counit. `det-sp-tower-gamma` clause (3) preserves normalized constructible towers for both exceptional operations. Combined with Step 1 these statements apply to f and f-prime, and put P, Q, C and D in the required categories. The integral direct-image node also supplies membership of the compact-support results in the integral constructible category. Thus the two objects between which the integral exchange is to be lifted really lie in the domain of the equivalence. I wrote a = U(q) alpha and b = G-prime(alpha) q-prime in their correct directions.

For Step 4 I used the existing equivalence and the natural sigma and alpha comparisons just checked. The expression for the reduction of beta-I has five factors whose endpoints match, starting at r(v-I-star F-I M) and ending at r(F-prime-I u-I-star M). Each factor is invertible. I proved the explicit inverse-on-Hom formula with the triangle identity and naturality of kappa, and the other inverse identity with naturality of iota. This is a few-line elementary calculation from the cited equivalence, not an omitted extra transport theorem. Applying that calculation to the inverse gives invertibility, and faithfulness proves naturality of the lifted beta-I.

For Step 5 the same inverse-on-Hom calculation applies to the actual morphism b-inverse t a, including a noninvertible t. Its reduction is that morphism, and its naturality follows by faithful reduction of the naturality square. Only the equivalence is cited here; no assertion of existence for arbitrary families of maps at finite levels is made.

For Step 6 I opened `det-sp-tower-gluing` and checked that its statement supplies the natural right adjoint and counit. Together with the integral Hom bijection, natural sigma and specified alpha this justifies each operation in the displayed calculation. The common source comparison is sigma-prime-C-inverse followed on its right by F-prime(a-inverse); the target comparison is alpha-v-K. Naturality of sigma brings r(T) inside F-prime. Naturality of the tower counit brings alpha inside G-prime. Substitution of b and r(T) then cancels b and a, leaving precisely epsilon-prime F-prime(t). This calculation is algebraic substitution from already cited identities, so it creates no hidden geometric lemma.

For Step 7 I checked the other integral composite under exactly those same comparisons. Naturality of alpha-v applies to epsilon-f-I-K, whose source is F-f-I J-f K. Inverting the definition of the beta-I reduction, then cancelling sigma-prime and alpha-u, leaves the displayed expression involving q. The Step 2 counit identity removes sigma-f. Finally I wrote the naturality square for beta at q explicitly and cancelled F-prime U(q) and its inverse. This is what identifies the result with V(epsilon-f) beta-at-G-f-R-inverse. It is not an appeal to an unspecified compatibility of limit and transpose.

For Step 8 both actual tower morphisms are now the two sides of the hypothesized equation. Cancelling the common isomorphisms and using the faithful reduction equivalence proves the integral equality. There is no use of invertibility of t, only of the specified comparisons.

I checked edge cases: for identity equivalences the reconstruction formula returns g itself; identity f and an identity square make all the comparison cancellations identity cancellations; d = 0 uses the same hypotheses and formulas; empty schemes are allowed by the cited base-change lemma and require no point choices. The zero map t reconstructs to zero, and the transpose identity still holds; the final conclusion then requires exactly the stated tower counit equation, not an extra claim that zero automatically satisfies it. No inversion of t appears anywhere. All eight steps have fewer than 2000 characters, and none hides a separate non-elementary subclaim.

Against delivery-errors B-E: the unchanged statement introduces its objects; no new statement-only node or definition needs validation; all non-elementary inputs are existing cited statements, read above; the proof has a genuine calculation and is not a relabeling of the conclusion. The 24 citation extracts were verified as literal substrings of the respective statements. No route replacement is used. The two declared generic tool uses are base-change permanence and the independently specified integral right adjoint. I kept all imported metadata and the original searches, and appended only searches recorded by this item's msearch command. Both semantic phrasings returned general categorical or algebraic results, not this geometric assertion.

## Unfinished work

None in the stage-1 split. The independent maintainer review and subsequent formalization remain part of the project process.
