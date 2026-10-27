## What changed

Filled `WeilConjectures.sfLocalizationAllStages_weil` in
`Sheaf.Paper.SfLocalizationAllStages`, preserving its entire signature and the
already completed ordinary all-stage proof. Added three proved private helpers:
`sfWeilLift`, `sfWeilTransports`, and `sfWeilFiberRange`.

The categorical helper takes mates successively along closed pullback/pushforward,
closed pushforward/exceptional pullback, and open pullback/pushforward. The existing
proved `IsoAlgebra.mateIso` and `mapOfNatIsoAdjunction` API constructs the lifts,
including exactly the original adjunction units and counits on carriers. The
Frobenius image of a supported triangle is distinguished. Conjugating its vertices
by the transported structure isomorphisms preserves its first two prescribed
arrows; uniqueness of the supported boundary forces its last arrow to be the
original one. This supplies a natural fixed-pair boundary with the required
carrier equality, without a triangulation on fixed pairs.

The geometric helpers specialize the existing semilinear transport theorem to
identity morphisms, and prove the range formula for a geometric-fibre map from
its Cartesian square, using its commutativity and the point-lifting property. This shows that base change preserves the complementary
pair. The existing ordinary all-stage theorem supplies the rational and
common-stage records, and the canonical pullback squares feed the categorical
helper at each stage. The construction works for empty closed or open schemes,
zero objects, arbitrary finite E, and independent universes for the scheme and
algebraic closure; no scalar embedding of E into the chosen closure is required.

Added only private proof imports. Updated the existing proposition node's proof,
proof dependencies, and proof origin to this route. No source-library file,
public import, definition, instance, or declaration signature is changed.

Validation: the required remote `lcompile.py` accepted the complete module with
exit code 0 in 14.6 seconds. Both theorem signatures were compared to the shared
source and are identical. There are zero `sorry` tokens and all Lean lines fit
within 100 columns. The revised DAG proof dependencies equal the union of proof
step uses, and none has a path back to this proposition. The final delivery tool
also runs compilation and preflight.

## Proved and sorry left

Original module holes: 1. Closed: `WeilConjectures.sfLocalizationAllStages_weil`,
node `prop-sf-localization-all-stages`. New holes: 0. Remaining module holes: 0.
No split-off statements, axioms, or data selected from arbitrary unproved
existence assertions are added. The three private helpers are fully proved.

This is a proof from existing declarations: the ordinary all-stage theorem and
semilinear Frobenius transport still depend on their separately assigned open
proofs. This delivery does not claim their transitive `sorryAx` dependencies are
closed. The proved integral exceptional-limit formula remains untouched in the
publicly re-exported data module.

## No longer needed

No existing import is removed and no module is withdrawn. The existing private
construction imports remain necessary for the ordinary theorem.

The Weil proof no longer needs `lem-sf-supported-weil-mate-lift`
(`Sheaf.SixFunctors.SupportedWeilMateLift`): it uses the proved IsoAlgebra mate and
adjunction constructors directly, and boundary uniqueness proves precisely the
boundary equivariance required here. It does not need that wrapper's extra exact
adjunction, full-faithfulness, unique-middle-map and coefficient comparison input
records. The original localization and coefficient-stage route stays intact.

The stale direct dependency `lem-fix-weil-operations` is removed, together with
its `tool_uses` entry. Its current attached declaration is only the mixed-support
cup-product Weil pairing on etale coefficient categories and is not used here.
The actual Frobenius equivalences and exactness come from the existing
`lem-pod-semilinear-field-operation-lifts`; pullback squares are the published
`fieldWeilPullSquare` and `zlFrobeniusSquare`. No global module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The planned supported-Weil wrapper is conditional on a substantially richer input
record than `SfSupportedLocalization` supplies. Its conclusion is also not the
literal `SfWeilLocalization` record. None of this is a false statement or an
obstacle to using existing open lemmas. The shorter argument above supplies the
needed lift directly from the smaller public record and the already proved mate
API. The unit's ordinary Hom(-,K) construction remains in the unchanged
coefficient-stage dependencies, so no prescribed unit route is bypassed.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
