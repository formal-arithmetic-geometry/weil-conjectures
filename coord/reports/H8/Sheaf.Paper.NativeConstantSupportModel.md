## What changed

Constructed the actual constant-integral-to-finite-quotient maps and their compatible
`OrdinaryScalarRestriction` record on the existing explicit section tower. Applied the
existing `ordinaryScalarAdjunctions` theorem. Sectionwise uniqueness identifies its proper
comparison with this module's specified comparison; its unit equation proves the specified
pullback mate invertible.

For open extension, the native invertible unit and the generic open-unit equation give
invertibility of the constant open unit on restricted modules. The triangle identity and
the open comparison then give the required counit isomorphism. The actual open mate is a
composite of isomorphisms. All choices of generic comparison data occur inside theorem
proofs; the new definitions are explicit constructions.

Extracted the existing complete private `sequenceRestriction_properties` proof into the
new module `Sheaf.Paper.NativeSequenceRestrictionProperties`, exported as
`nativeSequenceRestriction_properties`, with its own node. This preserves the unit
route and the full unbounded statement. Slow-definition and inference improvements
were attempted first; the independent extraction keeps each compilation below the
per-file limit. The explicit section tower and scalar record are also extracted to
`Sheaf.Paper.NativeConstantSectionRestriction`: the record takes only the three proved
exactness properties as arguments; all data is constructed directly. Updated the owning
node's proof and dependencies. Public statements, definitions, and
public imports retain their existing signatures and bodies. The private section-tower
implementation now aliases its identical extracted construction. The existing exactness proof
now specializes a generic scalar-restriction argument. Explicit preservation instances
avoid broad searches, and explicit conversions normalize the equal cochain-complex
shapes used by the existing derived-comparison argument.

Validation: all three delivered modules compile successfully together through
`lcompile.py --all`. No debugging options remain.

## Proved and sorry left

Closed the two original holes:

- `WeilConjectures.PurStrictScalar.systemPullMap_isIso`
- `WeilConjectures.PurStrictScalar.systemOpenMap_isIso`

No `sorry` remains in the item, and no new hole or split-off `sorry` statement is added. The proof uses
the existing stated dependency
`AlgebraicGeometry.ProEtale.VaryingRing.ordinaryScalarAdjunctions`, which still has `sorry`;
this delivery specializes and combines that dependency rather than claiming to prove it.

## No longer needed

Removed the item's direct proof imports of
`Sheaf.CategoryTheory.RestrictedTowerResolutionAcyclicity` and
`Sheaf.CategoryTheory.SystemEvaluationTopos`; they are now used by the extracted proved
module. These modules and their nodes remain needed through it. No mathematical
dependency is withdrawn. Both
inverse/open obligations use the existing general scalar-adjunction interface, so they
need no newly stated tensor-balancing or sheafification lemmas. The main module
no longer needs its private `constantLevelMap_horizontal` theorem: the extracted
construction contains the identical compatibility argument.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The owning node recorded the inverse/open obligations as
open without using the existing generic normalized scalar-adjunction declaration. Its
proof now records that shorter specialization. The open proof explicitly supplies the
support/counit argument; invertibility of a square alone does not imply invertibility of
its mate.

## New nodes

`lem-pur-native-sequence-restriction-properties` records the extracted complete proof
of right adjointness and inverse-limit acyclicity of native sequence restriction. It
has no `sorry` and adds no hole. The original owning node now cites it for Steps 1
and 2. No definition or statement is changed, and no change record is required.

`def-pur-native-constant-section-restriction` records the explicit section tower, actual
quotient maps, and normalized scalar-restriction record, with additivity and finite
exactness provided as proof arguments. It contains no `sorry`; the main module passes
its existing exactness theorems after the proved functor identification.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
