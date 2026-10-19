Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-admissible-quotient-generic-degree.json`: split statement, 12 proof steps, and citations.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-artin-tate-subalgebra-finite-type.json`: one Mathlib leaf, `fg_of_fg_of_fg` (Mathlib/RingTheory/Adjoin/Tower.lean:145--154; Stacks 00IS).
- `citations.json`: verbatim statement quotes for every cited node in every step.

Attachments: none. No declaration tagged `(blueprint: lem-per-admissible-quotient-generic-degree)` exists in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `/home/ubuntu/weil-newtargets-master/WeilConjectures`.

WANTED: none.

The imported item had no proof and its statement carried a long list of unrelated convention dependencies. I retained every mathematical clause and reduced `stmt_deps` to the notions actually used in the statement. I split the proof into affine invariant-ring construction, restriction and gluing, categorical descent, intermediate finiteness, and invariant function-field degree. The only new node is the Artin--Tate finite-type descent lemma; Mathlib contains it exactly as `fg_of_fg_of_fg`, so it is a Mathlib leaf. I checked the existing quotient, affine groupoid, projective quotient, function-field, Noetherian, excellence, finite-morphism, localization, and Galois nodes before citing them. The source text at ILO Exposé IX 1.4, pp. 132--133, was read directly from `gabber.txt`; the affine invariant-ring and orbit-space details were checked against Stacks groupoids Tags 03BJ, 03BL, 03BM and scheme gluing Tag 01JC, while the field-action assertion was checked against Fields Tag 09I3. The projective sufficient condition uses the existing `lem-per-projective-finite-group-quotient` statement.

## Not duplicates

- `lem-per-artin-tate-subalgebra-finite-type` vs existing DAG nodes: no existing node states Artin--Tate finite-type descent for an intermediate subalgebra; searches for `00IS`, `Artin-Tate`, and `fg_of_fg_of_fg` found no existing DAG statement.

## Review by Q134

I read the item source and the ancestor blueprint route, then checked the item against ILO IX 1.4 and the archived source extract. Step 1 verifies admissibility for every subgroup by finite orbit intersections and uses the cited separated-affine-intersection, finite-type, and integral-scheme statements. Step 2 reads the invariant polynomial construction and uses the existing finite-integral-generator statement plus the new Mathlib Artin--Tate leaf; the Noetherian conclusion and finite affine morphism are exactly the cited statements. Step 3 checks the finite action groupoid, its finite-locally-free projections, and the orbit-fibre theorem against the cited coproduct, spectrum, finite-free, orbit-fibre, and finite-closed-map nodes. Step 4 checks localization edge cases, including the zero element and nonzero denominators in the domain. Step 5 explicitly supplies invariant principal neighbourhoods using prime avoidance, and does not assume arbitrary opens are affine. Step 6 checks the scheme and morphism gluing hypotheses and the cocycle identity on common invariant sections. Step 7 checks that categorical descent is constructed locally on affine targets and then glued, including the equivariant-map consequence. Step 8 checks intermediate finiteness via the Noetherian-submodule statement and verifies integrality, finite type, Noetherianity, excellence, and the affine special case clause. Steps 9--11 check the fraction-field identification, faithfulness from generic freeness, and the Galois degree calculation; the denominator product is written explicitly and the tower-basis and coset count are marked elementary. Step 12 checks the projective/trivial-action sufficient condition against the existing projective quotient statement. Every `uses` entry was opened and its quoted statement copied verbatim into `citations.json`; `proof_deps` is the union of those uses. I retained the original `created` metadata and removed unrelated convention dependencies while preserving every mathematical clause.

What I could not finish: none. The required dry run and delivery remain to be run.
