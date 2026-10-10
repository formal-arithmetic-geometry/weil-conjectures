1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-right-adjoint-open-support-criterion.json`: item, split; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-open-restriction-support-triangle.json`: statement-only child, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-supported-derived-generated-perfect.json`: statement-only child, no Mathlib match.
- `citations.json`: three step-to-node verbatim quotes.

2. Attachments: none.

3. WANTED: `literature/stacks-project/duality.tex`, Tag 0E4G (the local literature checkout has no Stacks TeX source; I read the authoritative Stacks HTML page for the tag).

4. The original item had an empty proof. I retained its statement and dependencies, and split the two non-elementary inputs that the Tag 0E4G proof uses: the open-restriction triangle with supported cone, and generation of the supported derived category by a perfect object. No existing DAG or blueprint node stated either input; the blueprint search returned no matches. The proof follows the Stacks proof: construct the open-square map by adjunction, apply the support triangle for the bounded-below equivalences, and use direct-sum preservation plus perfect generation for the unbounded implication.

## Not duplicates

lem-sc-open-restriction-support-triangle vs lem-sc-right-adjoint-open-support-criterion: the new node states only the restriction triangle and support of its cone; the existing item states the equivalence relating right-adjoint support to restriction-map isomorphisms.
lem-sc-open-restriction-support-triangle vs lem-sc-proper-flat-right-adjoint-open-support: the new node is a general open-immersion triangle for any qcqs scheme, while the existing node is proper-flat support preservation for a right adjoint.
lem-sc-supported-derived-generated-perfect vs lem-sc-right-adjoint-open-support-criterion: the new node states perfect generation of the supported derived subcategory; the existing item states a right-adjoint support criterion.
lem-sc-supported-derived-generated-perfect vs lem-sc-proper-flat-right-adjoint-open-support: the new node is a general generation theorem, while the existing node asserts support preservation under proper flat finite-presentation hypotheses.

## Review by M1

I read the item source at Stacks Tag 0E4G, including the displayed transformation (48.4.1.1) and the proofs of parts (1), (2), and (3). I also read the source places for both new nodes: Tag 0E4G's support triangle argument invokes Derived Categories of Schemes Lemma 36.4.1 and Definition 36.6.1, while its direct-sum argument invokes Lemma 36.15.4 and Derived Categories Lemma 13.37.3. Step 1 uses the triangle node only for the open-restriction setup and states the adjunction construction explicitly. Step 2 uses exactly the triangle node's bounded-below and support clauses; the hypotheses that Y is qcqs and V is quasi-compact are those in both statements. Step 3 uses exactly the perfect-generation node, and separately verifies that direct-sum preservation makes the support subcategory closed under the derived colimits used in the source. I checked the converse directions by restriction to the bounded-below subcategory and tested V=Y, V empty, identity f, and zero Q: every map reduces to the expected identity or zero-support assertion. I ran all required Mathlib searches for the item and both children; LeanFinder returned only generic derived-category or open-restriction declarations, Loogle and source grep found no matching scheme theorem, and LeanSearch was unavailable, recorded as such. Citations are verbatim substrings of the two child statements.

## Second reading by M1

- Source Tag 0E4G, Lemma 48.4.3, parts (1)--(3), statement: checked the qcqs hypotheses, quasi-compact open, inverse image, right adjoints, and the three separate bounded-below, unbounded, and direct-sum clauses; verdict: corrected to match the source quantifiers.
- Source Tag 0E4G, equation (48.4.1.1) and following paragraph, Step 1: checked the open-square adjunction unit/counit construction and its equivalent restriction map; verdict: sound.
- Source Tag 0E4G proof of part (1), Step 2: checked the triangle, bounded-below cone, restriction to U, and converse using K=Q with Lj^*Q=0; verdict: repaired and sound.
- Source Tag 0E4G proof of part (2), Step 2: checked the same argument for arbitrary D_QCoh objects; verdict: repaired by extending the triangle node to all complexes.
- Source Tag 0E4G proof of part (3), Step 3: checked the supported subcategory, perfect generator, induction on cones, and closure under derived colimits from exactness plus direct sums; verdict: sound after making the induction and closure explicit.
- New node lem-sc-open-restriction-support-triangle: checked against 0E4G proof and Derived Categories of Schemes 36.4.1/36.6.1; verdict: repaired to state the all-complex triangle and the additional bounded-below conclusion, with existing scheme, derived-category, and direct-image definitions cited.
- New node lem-sc-supported-derived-generated-perfect: checked against 0E4G proof and Derived Categories of Schemes 36.15.4/13.37.3; verdict: repaired to define T as the complement of a quasi-compact open and to cite def-pc-perfect-complex; no Mathlib declaration matched the scheme theorem.
- Edge cases checked: V=Y gives zero cone and tautological restriction; V empty gives zero restriction and full support; f the identity gives the identity right-adjoint map; Q=0 satisfies both support clauses.
- Searches checked: all recorded LeanFinder, Loogle, grep, and unavailable LeanSearch entries were rerun through msearch.py; no matching Mathlib scheme theorem was found.

Changes made: separated the item’s source clauses and fixed their quantifiers; extended the support-triangle node to unbounded complexes; added the perfect-complex dependency and precise supported-subcategory formulation; repaired Step 2’s converse and Step 3’s induction text; updated verbatim citation quotes. The sandbox item’s stale created.item metadata is maintainer-owned and is left for delivery to preserve the repository record.
