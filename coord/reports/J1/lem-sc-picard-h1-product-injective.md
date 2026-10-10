Files written:
- `dag/nodes/sec-abelian-varieties/lem-sc-picard-h1-product-injective.json`: split item, no Mathlib match.
- `dag/nodes/sec-abelian-varieties/lem-sc-picard-kunneth-qcoh.json`: statement-only child, no Mathlib match.
- `citations.json`: verbatim child-statement quotes for all four proof steps.

Attachments:
- None. I searched the slopmaster2 WeilConjectures source for the item tag and for Kunneth/product H1 declarations; no sorry-free project declaration states this item.

## Not duplicates

- `lem-sc-picard-kunneth-qcoh` vs `lem-sc-picard-h1-product-injective`: the child is the general all-degrees Kunneth isomorphism for arbitrary quasi-coherent modules, while the item is only the degree-one injectivity of two slice pullbacks for structure sheaves with H0 and rational-point hypotheses.

WANTED:
- None; `literature/stacks-project/varieties.tex` is present and contains Tag 0BED.

What I checked and changed:
- The item source is Varieties, Lemma `varieties-lemma-kunneth`, Tag 0BED, applied to the structure sheaves in degree one. The source gives the general canonical Kunneth isomorphism, and the item is its slice-injectivity consequence under the stated H0 and rational-point hypotheses.
- I searched the entire DAG and blueprint for Kunneth/cohomology-product statements. Existing Kunneth nodes concern etale derived coefficients and do not state the Zariski quasi-coherent product isomorphism needed here, so the new child is not a duplicate. The child was searched with LeanFinder, Loogle, grep, and LeanSearch; the first three found no matching Mathlib theorem and LeanSearch was unavailable.
- Step 1 checks proper schemes are quasi-compact and separated, hence have affine diagonals, so the child applies. Step 2 specializes the child at the structure sheaves and n=1, then uses the two H0=k hypotheses. Step 3 checks the slice compositions with the projections: each slice is identity on one summand and factors through Spec(k) on the other, whose positive cohomology is zero; this is the functorial pullback description in Tag 0BED. Step 4 concludes that the pair of slice maps is the identity under the decomposition and hence injective.
- Small cases checked: if X=Y=Spec(k), all H1 groups vanish and the map is injective; if one factor has H1=0, the decomposition reduces to the other factor and the corresponding slice is an isomorphism.

## Review by J1

I read the exact Tag 0BED statement and proof around `varieties.tex` lines 5441--5525. The child statement matches its hypotheses (field, quasi-compact schemes with affine diagonals, quasi-coherent modules) and conclusion (canonical cup-product Kunneth isomorphism). The item statement is the degree-one structure-sheaf specialization with the H0 and rational-point assumptions required to identify the slice map. Every proof step cites only the child statement, and each citation quote is copied verbatim into `citations.json`. I verified that the parent is strictly weaker than the child, that no existing DAG node states the same Zariski Kunneth result, and that the Mathlib searches were actually run and recorded. The only correction made during review was to make the child explicit and to spell out both identity/zero slice components instead of asserting injectivity directly.

## Second reading by J1

- Source statement: checked item against Varieties, Lemma `varieties-lemma-kunneth`, Tag 0BED; properness, rational points, and both H0 hypotheses are present.
- Child `lem-sc-picard-kunneth-qcoh`: checked against Tag 0BED; corrected to arbitrary k-schemes, n >= 0, the fibre product over Spec(k), and the projection/cup-product functoriality used by the parent.
- Item step 1: checked properness consequences against `pqf-lem-proper-basic` and `def-weil-proper-morphism`; all non-elementary facts are cited.
- Item step 2: checked degree-one specialization and the two H0=k hypotheses; the two summands are correct.
- Item step 3: checked slice functoriality against the child and affine vanishing against `pqf-lem-affine-vanishing`; identity and zero components are explicit.
- Item step 4: checked that the ordered pair of slice maps is the identity under the decomposition, hence injective.
- Small cases: checked X=Y=Spec(k), one factor with H1=0, and the empty scheme.
- Citation audit: replaced incomplete child-only quotes with verbatim excerpts for every cited node and added the missing proof dependencies.

Changes made: corrected the child statement; cited properness and affine vanishing in the parent proof; repaired `citations.json` accordingly.
