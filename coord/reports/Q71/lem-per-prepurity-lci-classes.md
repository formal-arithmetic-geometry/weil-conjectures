# Stage-1 report: lem-per-prepurity-lci-classes (Q71)

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-prepurity-lci-classes.json`: split into ten proof steps. No new nodes; no Mathlib leaves. The natural statement is unchanged. Removed its unused `def-weil-proper-morphism` statement dependency and added `lem-asd-etale-finite-twist-pullback`, which actually defines the signed twists used in the statement.
- `citations.json`: one verbatim statement excerpt for every node citation of every item step.

The sandbox also contains the source PDF's extracted text, a preparation script and the actual `searches.jsonl`; these are working material, not delivered node files. The chapter and unit records were read and left unchanged: this item is infrastructure for the regular-duality input in ancestor `lem-per-artin-gabber-affine-curve`, not the key node realizing the unit.

## Attachments

None. Searches in `WeilConjectures/` of the read-only slopmaster2 and master references found no tagged declaration or full lci construction. The nearest source declaration, `AlgebraicGeometry.Etale.existsUnique_fundamentalClass` in `WeilConjectures/EtaleCohomology/Purity/Smooth/RegularImmersion.lean:163`, has `sorry` at line 168 and assumes an ambient scheme smooth over a perfect field. It does not prove this mixed-characteristic trait assertion or its factorization/composition clauses.

## WANTED

None. I read the local ILO PDF, Expose XVI, section 2.5 (printed pp.238–241), Definition 3.5.4 and the beginning of Proposition 3.5.7 (printed pp.248–249). The source text was extracted locally in this sandbox; no literature was downloaded.

## Problems found and corrections

The item has no false clause to repair. The main risk was circularity: `lem-per-regular-gysin-calculus`, `lem-per-smooth-immersion-interchange`, and the absolute-purity classes are unsuitable as black boxes for this prepurity assertion. The delivered proof instead uses `lem-per-regular-immersion-class-calculus` and `lem-per-smooth-gysin-mixed-identities`, whose statements provide the classes and mixed identities without requiring their invertibility. The latter is already the diagonal/DNC replacement of the source's classical smooth construction. I opened both it and `lem-per-ordinary-smooth-orientation`, along with `lem-per-noetherian-prime-power-smooth-duality`, to check the n=1 coefficient and normalization agreement.

A local construction alone would not justify a global morphism by descent in an ordinary derived category. Step 1 therefore constructs a global factorization using the quasi-projective immersion, a separated graph projection, and the existing closed-immersion-from-composite lemma. Step 6 compares global factorizations by a global fibre product; its final local assertion is restriction of an existing global map. For composition, Step 8 extends the projective ambient open from the closed subscheme into the ambient projective space. This ensures the two immersions really are closed immersions in the Cartesian diagram, rather than treating a locally closed immersion as closed in the full projective space.

## Unfinished work

No part of this one-level split remains unfinished. Existing unsplit descendants remain existing items; this delivery creates none and does not claim that the entire transitive proof closure is finished.

## Not duplicates

There are no new node pairs to distinguish. Whole-DAG statement searches and blueprint searches for “fundamental class”, “Gysin”, “virtual relative dimension”, “graph” and “quasi-projective” were read before writing. The geometric calculus and mixed-identity nodes were reused. The blueprint regular-immersion purity nodes assume smoothness over the fixed perfect field and assert invertibility, so cannot replace the present prepurity trait statement. The existing affine regular-Gysin calculus also asserts invertibility, has stronger geometry hypotheses, and lies above the absolute-purity argument. No duplicate or clause-restating children were created.

## Review by Q71

I reviewed delivery-errors B–E against the source and each proof citation, not just against JSON validity. Every step's cited statement is included verbatim in `citations.json`. I used these statements as follows.

1. The finite-type-over-Noetherian node makes T and U Noetherian. The projective chart node states a cover by polynomial affine charts over the integers, and the base-change definition identifies relative projective space with their pullback. Affine-space smoothness, source locality and open restriction then give the needed smooth projection; relative dimension is N on every chart. The projective-proper node supplies separatedness. I explicitly restrict and pull back its closed diagonal, and apply the closed-immersion-from-composite statement only with a separated projection and a genuinely closed composite. The geometric calculus states regularity of an immersion between regular schemes and smooth ascent of regularity. Thus its hypotheses apply to the graph immersion. Regularity of S itself follows directly from the dimension-one principal-maximal-ideal hypothesis, and no excellence or flatness of T over S is assumed.

2. The geometric calculus's intrinsic virtual-dimension formula is stated for any regular Noetherian factorization, beyond its separate affine existence clause. I use that formula, local constancy, the integral-scheme irreducibility clause and the field-tower transcendence-degree identity. Subtracting the three pointwise expressions gives e_f=e_T-e_U. At generic points a generically finite map has zero transcendence degree and both local dimensions are zero, giving e_f=0. This does not equate virtual dimension with a nonnegative fibre dimension on a vertical scheme.

3. Nagata supplies compactifiability of the separated finite-type maps. Ordinary-etale compact-support comparison and right-adjoint-composition supply exceptional transitivity with its actual counits. The signed Tate-pullback node supplies invertible lines and their inverse-image identifications. The exceptional twist comparison is written as the Hom adjunction chain using the proper projection formula and the stalkwise tensor identity for extension by zero, rather than assuming a projection formula for exceptional inverse image on all coefficients. The star product is then ordinary functorial composition; no new abstract lemma is needed.

4. The immersion-class statement gives exactly A -> i^! A(c)[2c] at n=1, and the smooth statement gives exactly the diagonal/DNC map A(r)[2r] -> p^!A. The prime-power smooth-duality statement specifies that same construction and Kummer normalization at n=1. The mixed identities apply over arbitrary Noetherian bases with ell invertible, including this trait; there is no perfect-field or excellence hypothesis to import. Moving twists is by the Step 3 comparison.

5. The geometric calculus gives the smooth-pullback regular immersion and regular section. I additionally cite smooth-flatness rather than treating it as a definition. The mixed-identity node states both the Cartesian interchange and section normalization exactly in the star notation used here. The immersion and smooth class nodes supply their separate composition laws. I checked the domains in each equation: the section goes T -> T x_P P', its composite with the closed pullback j is i', and the star order is outer class followed by inner class.

6. The product projection is separated and smooth; its composite with the diagonal lift is the original closed immersion. This is exactly the hypothesis of the closed-immersion-from-composite node. Its ambient regularity follows by smooth ascent over regular P. The resulting factorization dominates each original one, so Step 5 proves equality of global morphisms, without a claim that restriction on derived Hom is injective.

7. The two class nodes state the identity and open-restriction clauses. Source exceptional restriction is precisely the adjoint-locality node; target exceptional restriction uses the open-exchange adjoint node. These are ordinary-etale comparisons, with no completed or pro-etale coefficient category silently substituted. Identity factors check both required specializations and the Kummer sign.

8. I checked the source's projective-ambient diagram rather than presuming an affine embedding of T globally. The graph immersion is the one established in Step 1. An open of a closed subspace is the inverse image of an ambient open; base changing this equality gives the claimed Cartesian square. Projective charts and smooth open restriction give its smooth projections. The geometric calculus then supplies flat-pullback regularity and regular-immersion composition. All ambient schemes are Noetherian and regular, so every cited Gysin clause applies.

9. I expanded the source's last three equations: interchange is used for j and p', not for a mismatched pair; separate smooth and immersion compositions give the first expansion. Associativity is the explicit adjunction composition of Step 3. Undoing normalized twists gives exactly the item's displayed formula, including the shift of g_f by e_h.

10. This step substitutes p_T=p_U f into Steps 2, 3 and 9, and is marked elementary for that reason. It does not cite a new lemma that merely restates the final clause. The normalization c_T lands in precisely p_T^! A(-e_T)[-2e_T]. When e_f=0, the twist vanishes and f^? really is f^!.

I tested the identity map, codimension zero, smooth dimension zero, the structure map of S, a vertical closed point (e=-1), a vertical positive-dimensional regular scheme (e=dimension-1 at its generic point), and a dominant generically finite etale map. The empty scheme is excluded by integrality; the argument never requires an unprovided nonzero purity isomorphism. There are no newly proposed statements to test. I traversed the existing dependency closures: the class-calculus, geometric-calculus and no-purity mixed-identity inputs do not reach this item, so the new edges do not form a cycle through it. Every non-elementary step has cited inputs; no proof step exceeds 2000 characters. Generic off-unit scheme and adjunction tools are declared in `split_report.tool_uses`, with no change to the unit or chapter route.

Mathlib searches were made only through msearch.py and retained in the log. I read both semantic phrasings, LeanSearch, Loogle and grep hits. They give smooth/etale morphism properties, standard-etale presentations and the irrelevant `finestTopologySingle` substring collision, not etale Gysin classes. Their queries and actual hit names were appended to the item's pre-existing search record. No search was invented, and no old search was erased.
