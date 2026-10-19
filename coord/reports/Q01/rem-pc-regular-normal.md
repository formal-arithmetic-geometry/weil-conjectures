# Worker report: rem-pc-regular-normal

## Files written

- `dag/nodes/sec-abelian-varieties/rem-pc-regular-normal.json`: statement; seven proof steps; split, not a Mathlib leaf. No new nodes and no new Mathlib leaves.
- `citations.json`: verbatim statement evidence for every citation in each numbered proof step. This is delivery-side evidence, not an extra project file.

## Attachments

No attachment for this item. I searched the exact blueprint id and the regular/normal, normal decomposition and connected/irreducible notions throughout `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/`, and checked `dag/lean_names_upstream.json`. `AlgebraicGeometry.IsRegular.irreducibleSpace` in `WeilConjectures/AlgebraicGeometry/Regular.lean:216` proves only the connected consequence, with `ConnectedSpace` including nonemptiness. The nearby integrally-closed-stalk result assumes dimension at most one. Neither supplies both scheme-level facts of this item. No sorry declaration from master was treated as a finished proof.

## WANTED

None. All sources used are present locally.

## Statement disputed and corrected

STATEMENT-DISPUTED: the imported final sentence says that a regular, connected, Noetherian scheme is irreducible, without nonemptiness. Under the usual definition of connectedness allowing the empty space, take the empty scheme, equivalently Spec of the zero ring. It is quasi-compact, locally Noetherian and regular by the empty affine cover, and connected since it has no partition into two nonempty opens. It is not irreducible because irreducibility includes nonemptiness in `def-weil-irreducible-components`. The imported proof's assertion that connectedness leaves exactly one component fails when there are zero components.

I made nonemptiness explicit in the consequence, retained both original scheme-theoretic assertions, and stated normality inline as normal-domain stalks. This is faithful to the intended nonempty connected consequence; equivalently Lean's `ConnectedSpace` convention would package the same nonemptiness. The finite decomposition still permits the empty scheme and the empty index set. I added precise statement dependencies rather than leaving every notion hidden behind `def-pc-scheme`.

The current repository has one direct citer: `lem-weil-pbc-good-curves-boundary-quasifinite`, step 4. I read its statement and proof: the fibre X is explicitly assumed nonempty, and that step explicitly repeats this before invoking this item's consequence. Thus its application remains valid. No citer or target was edited.

## Sources, route and searches

I read the current blueprint item at `literature/blueprint/main-20261015/blueprint/sec-abelian-varieties/sk-def-av-jacobian/rem-pc-regular-normal.md`, its `sk-def-av-jacobian` unit and the `sec-abelian-varieties` chapter. The unit is the Jacobian definition and has no proof steps; this item is its background scheme geometry. The route remains Stacks 0569 and 033M. I read `properties.tex`, labels `lemma-regular-normal` (0569), `lemma-characterize-regular` (02IT), `definition-normal` (033I), `lemma-normal-reduced` (033K), `lemma-normal-locally-finite-nr-irreducibles` (0357), and `lemma-normal-Noetherian` (033M). In `algebra.tex` I read `lemma-characterize-reduced-ring-normal` (030C), the algebraic input explicitly cited by 0357. Its finite-product conclusion is already fully stated by `lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions`; I did not take it merely from another node's proof.

Before writing, I searched the whole DAG by the source tags and regular/normal/decomposition/component keywords. `tools/blueprint_refs.py search` was run for `normal`, `normal ring`, `disjoint union of normal integral`, and `irreducible components`, and `ancestor rem-pc-regular-normal` confirmed the imported blueprint ancestor. The whole blueprint has no second statement of the combined item (`same_as: []`). Supporting algebraic and topological nodes were reused. The normal-ring decomposition and regular-ring normality, filed under the proper-base-change unit, are generic tools explicitly required by these Stacks proofs; they are declared in `split_report.tool_uses`. No Jacobian-unit step is replaced.

The logged msearch calls include LeanFinder with two phrasings, LeanSearch, Loogle, and a Mathlib grep. All returned successfully. Loogle reported the unknown identifier `AlgebraicGeometry.IsNormal`; that result is recorded, not treated as service unavailability. The results provide `IsIntegral`, `IsReduced`, `IsNoetherian`, `IsLocallyNoetherian`, and finiteness of irreducible components, but no normal-scheme decomposition or the combined item. I read the relevant Mathlib `AlgebraicGeometry/Properties.lean` and `Noetherian.lean` source candidates, including stalkwise reducedness and `finite_irreducibleComponents_of_isNoetherian`. Exact queries and returned names are retained in `searches.jsonl` and the item's `mathlib_searches`. No new node required a further search.

## Not duplicates

No new nodes. Existing supporting results were cited directly rather than recreating clauses of the item, the normal-ring product theorem, or elementary connectedness arguments.

## Review by Q01

This is my direct-delivery author review with the node statements and Stacks proofs open. The independent maintainer review remains separate.

1. Step 1 uses `def-weil-regular-scheme` for an affine cover by regular rings, `lem-weil-pbc-regular-ring-normal` for normality of those rings, `lem-weil-pbc-affine-open-stalk-localization` for the actual ring isomorphism from a prime localization to the scheme stalk, and `def-weil-pbc-normal-ring` for its normal-domain conclusion. I read all four statements. In particular the ring theorem assumes Noetherian regular rings; those are exactly what the regular-scheme definition supplies. No dimension-one smooth-curve lemma is used. The argument is the one referred to by 0569, with the affine/stalk bridge explicit.

2. Step 2 uses `def-pc-reduced-scheme`, whose statement includes both stalkwise and sectionwise reducedness, and `pqf-def-locnoeth`, which supplies an affine cover with Noetherian coordinate rings. The only inline algebra is that nilpotents in a domain vanish. This step is elementary, including the zero ring on an empty affine open. It does not assume intersections of affine opens are affine, nor require every affine open to have a Noetherian ring.

3. Step 3 uses `lem-weil-pbc-affine-open-spec-points` to cover every prime, and `lem-weil-pbc-affine-open-stalk-localization` to identify its localization with a normal stalk. `def-weil-pbc-normal-ring` then gives ring normality. `lem-weil-pbc-noetherian-finitely-many-minimal-primes` supplies its stated finite-minimal-prime hypothesis. `lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions` explicitly has the finite product of normal domains as clause (3). I checked reducedness from step 2, finiteness from Noetherianity, and normality before applying it. In particular I did not cite a definition node for the product theorem.

4. Step 4 uses `lem-weil-pbc-finite-affine-coproduct-spectrum` for the scheme isomorphism from the product-ring spectrum; `lem-weil-pbc-scheme-coproduct-family` explicitly states openness, disjointness and the covering property of the factors. `lem-weil-pbc-spec-domain-stalks-function-field` states both integralness of a domain spectrum and its prime-localization stalk description. `lem-weil-pbc-localization-normal-domain` states that prime localizations of normal domains are normal domains. The condition zero is excluded from each prime-complement multiplicative set, because the factors are domains and primes are proper. `def-pc-integral-scheme` gives the irreducibility needed here. The last few-line maximality argument uses the clopen partition, so no component-comparison lemma is hidden. The empty product yields no irreducible component.

5. Step 5 uses the full statement of `lem-sc-components-open-injection`: intersections of components with an open meeting them are components of that open, and the assignment is injective. This is enough both for openness of each global component and to rule out intersections of distinct components. The two intersections used for injectivity are nonempty because they contain the chosen x. Closedness is explicitly part of `def-weil-irreducible-components`. The affine normal pieces used in this step have been established in step 4, not imported from a circular decomposition statement.

6. Step 6 uses `lem-sc-irreducible-components-cover` for the cover and `lem-weil-pbc-noetherian-finitely-many-components` for global finiteness. Its hypothesis is the actual Noetherian assumption on X. `def-weil-open-immersion` identifies the component scheme with the restricted structure sheaf; hence its stalks equal the original stalks. `def-pc-reduced-scheme` and the reduced-and-irreducible equivalence in `def-pc-integral-scheme` give integralness. `lem-weil-pbc-scheme-coproduct-family` supplies the coproduct. The isomorphism to X is checked on the disjoint open cover: each inverse is the identity on an open subscheme, and overlap compatibility is vacuous. This is gluing and uniqueness from the existing Mathlib leaf `lem-weil-pbc-scheme-morphism-gluing`, whose full statement I checked: compatible morphisms on an open cover glue uniquely, and equality can be checked on that cover. Its hypotheses hold for the disjoint open components; compatibility on the empty overlaps is automatic. Normality is inherited from the same stalks, not from a theorem with additional hypotheses.

7. Step 7 uses the established decomposition and `def-weil-irreducible-components`. The separation into one component and the union of all other components is a direct elementary connectedness argument. I explicitly checked the formerly omitted zero-component case and now use nonemptiness before choosing a component.

I checked B1–B10 and C1–C8: no new nodes or proof sketches in new statements; every named notion is defined inline or has a definition dependency; all cited statements were read and copied verbatim into citation evidence; no uncited non-elementary fact is hidden in an elementary step; no clause is moved into a renamed child. I checked that none of the 20 cited existing nodes has a dependency path back to this item. I checked D1–D5 against the actual seven-step argument: the affine product decomposition is an existing strictly algebraic tool and the global component argument remains here. I checked E1–E7 with the empty scheme, one normal integral scheme, two disjoint normal integral schemes, a field spectrum, and the nonnormal crossing of two affine lines. The two-component example satisfies (2) but fails the connectedness hypothesis of (3); the crossing is excluded by normality, since its crossing stalk is not a domain. No connectedness or nonemptiness was silently used in (1) or (2). All steps are shorter than 2000 characters and contain one identified argument; no long-step extraction is needed.

On resumption I checked the saved dry-run receipt and confirmed there was no active delivery process before running a fresh successful dry run. I then made the gluing input in step 6 explicit by citing the existing morphism-gluing Mathlib leaf, adding its verbatim statement to `citations.json` and using its uniqueness clause for both inverse identities. This repairs a possible C1 omission without creating a node.

Corrections made during review: the normal-reduced source tag is 033K (checked in the tag map), and the nonempty hypothesis repairs the imported consequence. The split's normality notion is explicitly scheme-stalk normality, not a choice of an unspecified normalization. No SGA source is used.

## Unfinished work

No mathematical part of this one-level split remains unfinished. Stage-1 delivery validation follows below; existing supporting nodes retain their own states and are not edited.
