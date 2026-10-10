# def-pc-curve

## Files written

- dag/nodes/sec-abelian-varieties/def-pc-curve.json: split definition; no new nodes and no Mathlib leaf.

## Attachments

None. The slopmaster2 declaration `AlgebraicGeometry.IsCurve` in `WeilConjectures/AlgebraicGeometry/Curve.lean:75` is weaker: it allows nonintegral and zero-dimensional schemes. It does not state this item.

## Wanted

WANTED: literature/blueprint/master/blueprint/sec-abelian-varieties/sk-def-av-jacobian/def-pc-curve.md, for def-pc-curve. The literature checkout is absent on this machine, so I checked the imported node against the primary Stacks pages for Tags 020D and 0A23.

## Corrections

The imported definition named broad convention collections but omitted the integral-scheme definition. I replaced its statement dependencies with the precise existing definition nodes. The imported string also had literal newline escapes and a trailing semicolon; I rewrote it as a paragraph with ordinary TeX. The variety and curve conditions are unchanged. LeanSearch returned HTTP 500 twice; LeanFinder and a Mathlib source search found the constituents but no predicate for exactly this Stacks curve.

## Unfinished

Nothing in the split. The blueprint markdown source and local Stacks checkout were not present, as recorded above.

## Review by E1

I read Stacks Definition 33.3.1 (Tag 020D), which requires an integral scheme with a separated finite-type structure morphism over a field, and Definition 33.43.1 (Tag 0A23), which adds dimension exactly one. The item states those hypotheses verbatim in mathematical content. Its comparison with the curve-calculation convention is supported by the statement of def-sc-curves: that node assumes an algebraically closed field and allows schemes of dimension at most one without integrality. The unit sk-def-av-jacobian has no proof steps for this auxiliary definition, so the item has no proof steps or proof dependencies; the blueprint node itself has no proof.

I checked each cited statement: def-pc-scheme defines schemes; def-weil-scheme-over-base defines the structure morphism of a k-scheme; def-weil-affine-spectrum defines Spec(k); def-pc-integral-scheme defines integral schemes; def-weil-proper-morphism defines separated morphisms; def-weil-finite-type-morphism defines finite type; def-pc-dimension defines scheme dimension; and def-sc-curves defines the comparison convention. These statements supply precisely the notions used here. I searched the whole DAG and the blueprint index for the variety/curve clauses and found no separate duplicate to cite, and no new node was necessary. I checked the slopmaster2 IsCurve source: it has dimension at most one and no integrality, hence is not an attachment. The existing def-pc-smooth-projective-curve review independently notes this difference.

For small cases, Spec(k) is integral, separated and finite type but has dimension zero, so it is a variety and not a curve; affine one-space over k satisfies the curve conditions; the empty scheme fails integrality. Over an algebraically closed field, the one-point scheme and a disconnected union of affine lines fit def-sc-curves but fail this item's dimension or integrality condition, respectively. This checks that the two definitions were not conflated. I also checked that each replacement dependency is earlier and does not point back to the item. I corrected the missing integral-scheme citation, removed the broad convention citations, and normalized the text; no new statement or source route was introduced.
