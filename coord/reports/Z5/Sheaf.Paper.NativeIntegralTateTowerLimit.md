## What changed

The item theorem `AlgebraicGeometry.ProEtale.spIntegralTwist_inverseImage_isLimit`
now has a complete categorical proof, conditional on one single-level geometric
representation lemma in the new module
`Sheaf.Paper.NativeIntegralTateFiniteRepresentation`.
The target theorem's signature is unchanged.

The proof follows the current blueprint's geometric argument. It lifts the
actual finite-level transition maps through fully faithful lifted Yoneda,
constructs the geometric inverse limit with the existing source-library
`AffineOverLimit` construction, proves that limit weakly etale, and shows its
base change is limiting. It transports the limit through Yoneda, the actual
Kan-extension/sheafification inverse image, and abelian forgetting. The final
internal-module forgetful functor preserves the original chosen limit.
All geometric-limit and categorical glue is proved in the item. No data are
selected from the new existence theorem to define any public object.

The only split assertion represents **one finite level**. It contains no
infinite limit, no inverse-image functor, no base-change morphism and no
transition condition. The item itself constructs all transitions by Yoneda
fullness and proves their identities, composition and naturality.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.spIntegralTwist_inverseImage_isLimit`
(node `lem-pur-native-integral-tate-tower-limit`).
The item has zero textual holes.

Added one hole in
`AlgebraicGeometry.ProEtale.spIntegralTwistLevel_finiteEtale_representation`
(node `lem-pur-native-integral-tate-finite-representation`). Its whole proof
is `by sorry`, with a source and full mathematical proof in its docstring.
This is a decomposition: one hole closed and one strictly smaller hole added;
it is not a net hole reduction or a claim of a sorry-free dependency closure.

The private helpers `lift_representable_diagram`, `finiteEtale_geometric_limit`,
`representableInverseImageIso`, and `abelianForgetInverseImageIso` are proved.
No new axioms, no holes in definitions, and no source-library edits.

Validation: the server compiler accepted the item and its new dependency. The
final item compile exited successfully in 18.7 seconds. All Lean lines are at
most 100 characters, and the node proof-dependency union matches its steps.

## No longer needed

The old local-basis/coefficient-comparison route is unnecessary for this proof.
Removed from the item's proof dependencies:

- `sk-def-sp-coefficient-towers` / `Sheaf.Paper.SmoothPurityCoefficientTowers`;
- `det-def-sp-tate-twist-locally-free` / `Sheaf.Paper.TateTwistLocallyFree` as a
  separate compatible-bases preservation hypothesis;
- `det-prop-sfb-qlbar-colimit-x-integral-limit` /
  `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit` as a separate
  comparison of the coefficient limit;
- `det-prop-sfb-qlbar-colimit-x-pullback` /
  `Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback`;
- `lem-pur-adic-integral-comparison` / `Sheaf.Paper.PurAdicIntegralComparison`;
- `lem-pur-inverse-image-compatible-free-tower` /
  `Sheaf.Paper.PurInverseImageCompatibleFreeTower`;
- `lem-weil-proetale-weakly-etale-localization` /
  `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.

These modules were not imported by the original item; no existing public
import was removed. Some remain transitive imports of the definitions and
are not claimed globally pruned. The public import of
`Sheaf.Paper.ProEtaleTateTwists` remains necessary for the statement.
No module was withdrawn and no adopted source declaration was removed.

## Where the brief, the DAG or earlier work was wrong

The current blueprint's Integral twist paragraph explicitly uses finite etale
representation and geometric inverse limits, whereas this node's older plan
used compatible local bases, cofinal coefficient filtrations and normalized
slice inverse image. Both routes are mathematical arguments below the unit
level; the delivered route follows the current text directly and avoids those
extra comparisons. The unit's statement and steps are retained.

Single-level representability is not supplied by any of the old proof
dependencies: `spIntegralTwistLevel_comparison` compares two sheaf-module
presentations, and local freeness supplies bases, rather than a representing
finite etale scheme. The source library supplies the geometric affine limit
and its weak etaleness, so those steps were proved instead of split again.

Edge cases: the new lemma uses an arbitrary base scheme, allows the empty
scheme, and uses only positive exponents n+1. The diagram-lifting helper
transports every arrow and does not assume surjective transitions. Base
change is arbitrary; the unused invertibility hypothesis on X is retained in
the original signature. The AsSmall reindexing lifts both objects and Homs,
matching the source limit construction's SmallCategory universe.

## New nodes

`lem-pur-native-integral-tate-finite-representation` states finite etale
representation of one underlying native integral Tate level. Its docstring
and node describe reduction of an integral basis, the finite constant versus
continuous-function comparison, integral tensor balancing, and representation
by a finite product of roots-of-unity schemes. It is strictly a finite-level
step of the blueprint's argument, not the item under a new name.

Change record: `coord/changes/Z5-native-integral-tate-finite-representation.md`.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
