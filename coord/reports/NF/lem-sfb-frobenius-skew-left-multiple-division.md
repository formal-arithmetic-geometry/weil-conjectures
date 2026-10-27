Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-frobenius-skew-left-multiple-division.json`: split statement; no new nodes.
- `citations.json`: citation for the field inverse used in leading-term cancellation.

Attachments:
- None. No sorry-free project declaration states this item exactly.

WANTED:
- None. Milne's Algebraic Groups PDF is present locally and supplies the stated division algorithm.

What was checked and changed:
- The imported statement was compared with Milne, *Algebraic Groups* (iAG2017), printed p.296. It is the right division algorithm (f=qg+r), and it explicitly does not assume that the field is perfect. The opposite orientation (f=gq+r) is the one Milne places after the perfectness hypothesis.
- I searched the whole DAG and current blueprint for skew-polynomial division. The existing nodes `lem-sfb-frobenius-skew-free-submodules`, `lem-sfb-perfect-skew-polynomial-cyclic-decomposition`, and `lem-sfb-left-principal-finite-submodules` concern later module consequences or principal ideals; none states the division-with-remainder result, so no duplicate node was created. The blueprint search found only the separate algebraically closed-field Step 1 in `lem-sc-lang-steinberg`, which is not the same statement and is not cited.
- I searched the live project source for the item id and the skew-polynomial/division notions. There is no exact declaration to attach.
- The proof now has four steps. Step 1 handles (f=0) and (deg f<deg g). Step 2 writes (g_m=b), (f_n=a), (d=n-m), and chooses (c=a(b^{p^d})^{-1}); the coefficient of (F^n) in ((cF^d)g) is exactly (a). The only cited fact is the field property, quoted verbatim from `def-weil-field`. Step 3 verifies the leading term cancels and the degree decreases, including the (n=0) edge case without assigning a degree to zero. Step 4 applies strong induction and assembles the quotient (q=(cF^d)+q_1); when (m=0), the remainder condition forces (r=0).
- I tested the edge cases (f=0), (deg f<deg g), constant nonzero (g), and (n=m). The argument uses only inversion and injectivity of multiplication by nonzero field elements, never a (p^d)-th root or perfectness.

## Not duplicates

- `lem-sfb-frobenius-skew-left-multiple-division` vs `lem-sfb-frobenius-skew-free-submodules`: the existing node concludes finite generated submodules of a free skew module are free; it does not state polynomial division.
- `lem-sfb-frobenius-skew-left-multiple-division` vs `lem-sfb-perfect-skew-polynomial-cyclic-decomposition`: the existing node assumes perfectness and gives cyclic decomposition of modules; this item is the one-sided division algorithm without perfectness.
- `lem-sfb-frobenius-skew-left-multiple-division` vs `lem-sfb-left-principal-finite-submodules`: the existing node is an abstract consequence of principal left ideals; it neither proves nor states that Frobenius skew-polynomial left ideals are principal via division.
- `lem-sfb-frobenius-skew-left-multiple-division` vs blueprint `lem-sc-lang-steinberg` Step 1: that step uses an algebraically closed field and presents division only as an ingredient for a module classification; this item gives the precise arbitrary characteristic-(p) division statement.

## Review by NF

I read the item node, its chapter and unit records, the current blueprint ancestry recorded in the node, Milne p.296, and the relevant existing DAG nodes listed above. I checked every proof step against the ring multiplication: in Step 2 the twist exponent is (p^{n-m}), so the leading coefficient is (c b^{p^{n-m}}), which is invertible in a field; this is why no perfectness hypothesis enters. I verified that Step 3 compares finite supports and treats the zero polynomial separately. The sole cited node says verbatim that a field is a commutative ring with every nonzero element invertible, and that exact statement is recorded in `citations.json`. I also checked the statement's left-multiple orientation against the source's explicit contrast with the perfect-field left-division orientation. No hidden lemma was moved to a new node: all remaining steps are direct coefficient calculations, induction, and distributivity from the statement's definitions.

The first server dry run flagged Step 4 as non-elementary without a cited node. I corrected its classification to elementary: it is precisely application of the explicitly stated strong induction hypothesis followed by distributivity, with no external lemma. All four steps are under 2000 characters.
