Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-good-stratification-refinement.json`: item, statement node, no new nodes, no Mathlib leaf.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

Attachments: none.

WANTED: none.

The imported statement is unchanged and follows Stacks Tag 09Y5. No Lean declaration with this exact statement was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, and no existing DAG node states the good-refinement theorem. The item is not a Mathlib leaf: the recorded searches find only Noetherian irreducible-component decompositions, local-closedness characterizations, and unrelated cover refinements.

No new node was needed. The existing Mathlib leaf `lem-sc-noetherian-finite-irreducible-components` supplies finiteness of components, and `lem-sc-irreducible-components-cover` supplies that they cover the space. The existing scheme-specific `lem-sfb-noetherian-component-open` was not used because this item assumes only a topological space; step 3 derives the required open directly from the finite component cover and the locally closed partition.

## Review by Q75

I read the item source at `literature/stacks-project/topology.tex`, Tag 09Y5, together with the definition of good stratification at Tag 09Y0 and the preceding component argument in the same proof. I also read the full statements of every cited node: `lem-sc-noetherian-finite-irreducible-components` says a Noetherian space has finitely many irreducible components; `lem-sc-irreducible-components-cover` says the components cover the space; `def-weil-irreducible-components` defines components as maximal irreducible subsets and says they are closed; and `def-weil-locally-closed-subset` gives the open-intersect-closed description used to preserve local closedness.

Step 1 sets up strong induction on closed subspaces. I checked that closed subsets of a closed subspace are closed in the ambient space, so the descending-chain condition is inherited, and that the empty space is handled by the allowed empty partition. Step 2 applies only the two existing component statements and checks the finite, nonempty, closed, irreducible, maximal hypotheses. Step 3 constructs the nonempty open `O` inside a selected component by deleting the other finitely many components; the nonemptiness argument uses irreducibility and maximality, and the intersection with a partition part uses local closedness. This avoids importing the scheme-only component-open lemma into a purely topological statement.

Step 4 explicitly forms the two boundary pieces in the proper closed complement `C`, checks they are disjoint, cover `C`, refine the original partition, and remain locally closed. Step 5 applies the induction hypothesis and checks that local closedness and closures computed in `C` agree with those in `T` because `C` is closed. Step 6 checks all frontier pairs involving the new open `U`; pairs wholly in `C` are handled by induction. It then derives the closure-as-union clause from the frontier condition and the partition. I tested the construction on the empty space, a one-point space, a finite discrete space, and the Sierpiński space with its one-part and two-part partitions. No source error or hidden dependency was found.
